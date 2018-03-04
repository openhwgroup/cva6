// Copyright 2017 University of Cambridge.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
// See LICENSE for license details.

`default_nettype none

  module sd_bus(
                input              msoc_clk,
                input              sd_clk,
                input              rstn,
                input [31:0]       core_lsu_addr,
                input wire [31:0]  core_lsu_wdata,
                input              core_sd_we,
                input wire         sd_detect,
                input wire [3:0]   fifo_status,
                input wire [31:0]  rx_fifo_status,
                input wire [31:0]  tx_fifo_status, 
                input wire [31:0]  data_out_tx_fifo,
                input              sd_cmd_to_host,
                input [3:0]        sd_dat_to_host,
                //---------------Output ports---------------
                output reg [31:0]  sd_cmd_resp_sel,
                output wire [31:0] data_in_rx_fifo,
                output             tx_rd_fifo,
                output             rx_wr_fifo,
                output wire [12:0] sd_transf_cnt, 
                output reg         sd_reset,
                output reg [7:0]   clock_divider_sd_clk,
                output reg         sd_data_rst,
                output reg         sd_clk_rst,
 output reg	    sd_cmd_oe,
 output reg	    sd_cmd_to_mem,
 output reg	    sd_dat_oe,
 output reg [3:0]   sd_dat_to_mem,
 output wire [31:0] sd_status
                );
   wire 	    sd_cmd_oe_pos;
   wire 	    sd_cmd_to_mem_pos;
   wire 	    sd_dat_oe_pos;
   wire [3:0] 	    sd_dat_to_mem_pos;

   reg                             sd_cmd_to_host_dly;
   reg [3:0]                       sd_dat_to_host_dly;
   
   wire [133:0]                    sd_cmd_response;
   wire [31:0] 	    sd_cmd_wait, sd_data_wait;
   wire [6:0]                      sd_cmd_crc_val;
   wire [47:0]                     sd_cmd_packet;
   wire                            sd_cmd_finish, sd_data_finish, sd_cmd_crc_ok, sd_cmd_index_ok;
   wire [4:0]                      sd_data_crc_s;
   wire [3:0]                      sd_data_crc_lane_ok;
   wire [15:0]                     sd_crc_din[3:0];
   wire [15:0]                     sd_crc_calc[3:0];
   
   reg [2:0]                       sd_data_start;
   reg [11:0]                      sd_blksize;
   
   reg [2:0]                       sd_cmd_setting;
   reg [5:0]                       sd_cmd_i;
   reg [31:0]                      sd_cmd_arg;
   reg [31:0]                      sd_cmd_timeout;
   reg                             sd_cmd_start, sd_cmd_rst, dmy;
   wire [5:0]                      sd_cmd_state;
   wire [6:0]                      sd_data_state;

always @(negedge sd_clk or negedge rstn)
   if (rstn == 0)
     begin
        sd_cmd_oe <= 1'b0;
        sd_cmd_to_mem <= 1'b0;
        sd_dat_oe <= 1'b0;
        sd_dat_to_mem <= 4'b0;
     end
   else
     begin
        sd_cmd_oe <= sd_cmd_oe_pos;
        sd_cmd_to_mem <= sd_cmd_to_mem_pos;
        sd_dat_oe <= sd_dat_oe_pos;
        sd_dat_to_mem <= sd_dat_to_mem_pos;
     end // else: !if(!rstn)
   
   always @(posedge msoc_clk or negedge rstn)
     if (rstn == 0)
       begin
          sd_blksize <= 0;
          sd_data_start <= 0;
          clock_divider_sd_clk <= 0;
          sd_cmd_i <= 0;
          sd_cmd_arg <= 0;
          sd_cmd_setting <= 0;
          sd_cmd_start <= 0;
          sd_reset <= 0;
          sd_data_rst <= 0;
          sd_cmd_rst <= 0;
          sd_clk_rst <= 0;
          sd_cmd_timeout <= 15;
       end
     else
       begin
          if (core_sd_we)
            case(core_lsu_addr[5:2])
              1: clock_divider_sd_clk <= core_lsu_wdata[7:0];
              2: sd_cmd_arg <= core_lsu_wdata;
              3: sd_cmd_i <= core_lsu_wdata[5:0];
              4: {sd_data_start,sd_cmd_setting} <= core_lsu_wdata[5:0];
              5: sd_cmd_start <= core_lsu_wdata[0];
              6: {sd_reset,sd_clk_rst,sd_data_rst,sd_cmd_rst} <= core_lsu_wdata[3:0];
              8: sd_blksize <= core_lsu_wdata[11:0];
              9: sd_cmd_timeout <= core_lsu_wdata;
            endcase
       end

   always_comb
     case(core_lsu_addr[6:2])
       0: sd_cmd_resp_sel = sd_cmd_response[38:7];
       1: sd_cmd_resp_sel = sd_cmd_response[70:39];
       2: sd_cmd_resp_sel = sd_cmd_response[102:71];
       3: sd_cmd_resp_sel = {1'b0,sd_cmd_response[133:103]};
       4: sd_cmd_resp_sel = sd_cmd_wait;
       5: sd_cmd_resp_sel = {sd_status[31:4],fifo_status[3:0]};
       6: sd_cmd_resp_sel = sd_cmd_packet[31:0];
       7: sd_cmd_resp_sel = {16'b0,sd_cmd_packet[47:32]};       
       8: sd_cmd_resp_sel = sd_data_wait;
       9: sd_cmd_resp_sel = {19'b0,sd_transf_cnt};
       10: sd_cmd_resp_sel = rx_fifo_status;
       11: sd_cmd_resp_sel = tx_fifo_status;
       12: sd_cmd_resp_sel = {31'b0,sd_detect};
       13: sd_cmd_resp_sel = {26'b0,sd_cmd_state};
       14: sd_cmd_resp_sel = {25'b0,sd_data_state};
       15: sd_cmd_resp_sel = {23'b0,sd_data_crc_s,sd_data_crc_lane_ok};
       16: sd_cmd_resp_sel = {32'b0};
       17: sd_cmd_resp_sel = {24'b0,clock_divider_sd_clk};
       18: sd_cmd_resp_sel = sd_cmd_arg;
       19: sd_cmd_resp_sel = {26'b0,sd_cmd_i};
       20: sd_cmd_resp_sel = {26'b0,sd_data_start,sd_cmd_setting[2:0]};
       21: sd_cmd_resp_sel = {31'b0,sd_cmd_start};
       22: sd_cmd_resp_sel = {28'b0,sd_reset,sd_clk_rst,sd_data_rst,sd_cmd_rst};
       23: sd_cmd_resp_sel = {32'b1};
       24: sd_cmd_resp_sel = {20'b0,sd_blksize};
       25: sd_cmd_resp_sel = sd_cmd_timeout;
       26: sd_cmd_resp_sel = {sd_crc_din[1],sd_crc_din[0]};
       27: sd_cmd_resp_sel = {sd_crc_din[3],sd_crc_din[2]};
       28: sd_cmd_resp_sel = {sd_crc_calc[1],sd_crc_calc[0]};
       29: sd_cmd_resp_sel = {sd_crc_calc[3],sd_crc_calc[2]};
       default: sd_cmd_resp_sel = 32'HDEADBEEF;
     endcase // case (core_lsu_addr[6:2])

   sd_top sdtop(
                .sd_clk     (sd_clk),
                .cmd_rst    (~(sd_cmd_rst&rstn)),
                .data_rst   (~(sd_data_rst&rstn)),
                .setting_i  (sd_cmd_setting),
                .timeout_i  (sd_cmd_timeout),
                .cmd_i      (sd_cmd_i),
                .arg_i      (sd_cmd_arg),
                .start_i    (sd_cmd_start),
                .sd_data_start_i(sd_data_start),
                .sd_blksize_i(sd_blksize),
                .sd_data_i(data_out_tx_fifo),
                .sd_dat_to_host(sd_dat_to_host),
                .sd_cmd_to_host(sd_cmd_to_host),
                .finish_cmd_o(sd_cmd_finish),
                .finish_data_o(sd_data_finish),
                .response0_o(sd_cmd_response[38:7]),
                .response1_o(sd_cmd_response[70:39]),
                .response2_o(sd_cmd_response[102:71]),
                .response3_o(sd_cmd_response[133:103]),
                .crc_ok_o   (sd_cmd_crc_ok),
                .index_ok_o (sd_cmd_index_ok),
                .sd_transf_cnt(sd_transf_cnt),
                .wait_o(sd_cmd_wait),
                .wait_data_o(sd_data_wait),
                .status_o(sd_status[31:4]),
                .packet0_o(sd_cmd_packet[31:0]),
                .packet1_o(sd_cmd_packet[47:32]),
                .crc_val_o(sd_cmd_crc_val),
                .crc_actual_o(sd_cmd_response[6:0]),
                .sd_rd_o(tx_rd_fifo),
                .sd_we_o(rx_wr_fifo),
                .sd_data_o(data_in_rx_fifo),    
				.sd_dat_to_mem(sd_dat_to_mem_pos),
				.sd_cmd_to_mem(sd_cmd_to_mem_pos),
				.sd_dat_oe(sd_dat_oe_pos),
				.sd_cmd_oe(sd_cmd_oe_pos),
                .sd_cmd_state(sd_cmd_state),
                .sd_data_state(sd_data_state),
                .sd_data_crc_s(sd_data_crc_s),
                .sd_data_crc_lane_ok(sd_data_crc_lane_ok),
                .sd_crc_din(sd_crc_din),
                .sd_crc_calc(sd_crc_calc)                                     
                );

endmodule // chip_top
`default_nettype wire
