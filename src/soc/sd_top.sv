// 
// (c) Copyright 2008 - 2013 Xilinx, Inc. All rights reserved.
// 
// This file contains confidential and proprietary information
// of Xilinx, Inc. and is protected under U.S. and
// international copyright and other intellectual property
// laws.
// 
// DISCLAIMER
// This disclaimer is not a license and does not grant any
// rights to the materials distributed herewith. Except as
// otherwise provided in a valid license issued to you by
// Xilinx, and to the maximum extent permitted by applicable
// law: (1) THESE MATERIALS ARE MADE AVAILABLE "AS IS" AND
// WITH ALL FAULTS, AND XILINX HEREBY DISCLAIMS ALL WARRANTIES
// AND CONDITIONS, EXPRESS, IMPLIED, OR STATUTORY, INCLUDING
// BUT NOT LIMITED TO WARRANTIES OF MERCHANTABILITY, NON-
// INFRINGEMENT, OR FITNESS FOR ANY PARTICULAR PURPOSE; and
// (2) Xilinx shall not be liable (whether in contract or tort,
// including negligence, or under any other theory of
// liability) for any loss or damage of any kind or nature
// related to, arising under or in connection with these
// materials, including for any direct, or any indirect,
// special, incidental, or consequential loss or damage
// (including loss of data, profits, goodwill, or any type of
// loss or damage suffered as a result of any action brought
// by a third party) even if such damage or loss was
// reasonably foreseeable or Xilinx had been advised of the
// possibility of the same.
// 
// CRITICAL APPLICATIONS
// Xilinx products are not designed or intended to be fail-
// safe, or for use in any application requiring fail-safe
// performance, such as life-support or safety devices or
// systems, Class III medical devices, nuclear facilities,
// applications related to the deployment of airbags, or any
// other applications that could lead to death, personal
// injury, or severe property or environmental damage
// (individually and collectively, "Critical
// Applications"). Customer assumes the sole risk and
// liability of any use of Xilinx products in Critical
// Applications, subject only to applicable laws and
// regulations governing limitations on product liability.
// 
// THIS COPYRIGHT NOTICE AND DISCLAIMER MUST BE RETAINED AS
// PART OF THIS FILE AT ALL TIMES.
// 

// Copyright 2015 ETH Zurich and University of Bologna.
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

module sd_top(
 input wire 		 sd_clk,
 input wire 		 cmd_rst,
 input wire 		 data_rst,
 input wire [2:0] 	 setting_i,
 input wire 		 start_i,
 input wire [31:0] 	 arg_i,
 input wire [5:0] 	 cmd_i,
 input wire [31:0] 	 timeout_i,
 input wire [2:0] 	 sd_data_start_i,
 input wire [1:0] 	 sd_align_i,
 input wire [15:0] 	 sd_blkcnt_i,
 input wire [11:0] 	 sd_blksize_i,
 input wire [31:0] 	 sd_data_i,
 input wire [3:0] 	 sd_dat_to_host,
 input wire 		 sd_cmd_to_host,
//---------------Output ports---------------
 output wire [31:0] 	 response0_o,
 output wire [63:32]  response1_o,
 output wire [95:64]  response2_o,
 output wire [126:96] response3_o,
 output wire [31:0] 	 wait_o,
 output wire [31:0] 	 wait_data_o,
 output wire [31:4] 	 status_o,
 output wire [31:0] 	 packet0_o,
 output wire [15:0] 	 packet1_o,
 output wire [6:0] 	 crc_val_o,
 output wire [6:0] 	 crc_actual_o,
 output wire 	 finish_cmd_o,
 output wire 	 finish_data_o,
 output wire 	 crc_ok_o,
 output wire 	 index_ok_o,
 output wire 	 sd_rd_o,
 output wire 	 sd_we_o,
 output wire [31:0] 	 sd_data_o,
 output wire [15:0] 	 transf_cnt_o,
 output wire [3:0] 	 sd_dat_to_mem,
 output wire 	 sd_cmd_to_mem,
 output wire 	 sd_cmd_oe,
 output wire 	 sd_dat_oe,
 output reg [9:0]  sd_xfr_addr);

   reg 		    sd_cmd_to_host_dly;
   reg [3:0] 	    sd_dat_to_host_dly;
		    
   wire		    start_data;
   wire 	    data_crc_ok;
   wire 	    sd_busy, sd_data_busy;
  
   assign status_o = {1'b0,crc_val_o[6:0],
		      1'b0,crc_actual_o[6:0],
		      5'b0,finish_data_o,sd_data_busy,finish_cmd_o,
		      index_ok_o,crc_ok_o,data_crc_ok,sd_busy};
	    
always @(negedge sd_clk)
  begin
     if (data_rst)
       sd_xfr_addr <= 0;
     else
       begin
        if (sd_rd_o|sd_we_o)
            sd_xfr_addr <= sd_xfr_addr + 1;          
       end
     sd_cmd_to_host_dly <= sd_cmd_to_host;
     sd_dat_to_host_dly <= sd_dat_to_host;
  end
   
sd_cmd_serial_host cmd_serial_host0(
    .sd_clk     (sd_clk),
    .rst        (cmd_rst),
    .setting_i  (setting_i),
    .cmd_i      ({cmd_i,arg_i}),
    .start_i    (start_i),
    .timeout_i  (timeout_i),
    .finish_o   (finish_cmd_o),
    .response_o ({response3_o,response2_o,response1_o,response0_o,crc_actual_o}),
    .crc_ok_o   (crc_ok_o),
    .crc_val_o  (crc_val_o),
    .packet_o	({packet1_o,packet0_o}),
    .index_ok_o (index_ok_o),
    .wait_reg_o (wait_o),
    .start_data_o(start_data),				    
    .cmd_dat_i  (sd_cmd_to_host_dly),
    .cmd_out_o  (sd_cmd_to_mem),
    .cmd_oe_o   (sd_cmd_oe)
    );

sd_data_serial_host data_serial_host0(
    .sd_clk         (sd_clk),
    .rst            (data_rst),
    .data_in        (sd_data_i),
    .rd             (sd_rd_o),
    .data_out       (sd_data_o),
    .we             (sd_we_o),
    .finish_o       (finish_data_o),
    .DAT_oe_o       (sd_dat_oe),
    .DAT_dat_o      (sd_dat_to_mem),
    .DAT_dat_i      (sd_dat_to_host_dly),
    .blksize        (sd_blksize_i),
    .bus_4bit       (sd_data_start_i[2]),
    .blkcnt         (sd_blkcnt_i),
    .start          (start_data ? sd_data_start_i[1:0] : 2'b00),
    .byte_alignment (sd_align_i),
    .timeout_i      (timeout_i),
    .sd_data_busy   (sd_data_busy),
    .busy           (sd_busy),
    .wait_reg_o     (wait_data_o),
    .crc_ok         (data_crc_ok),
    .transf_cnt_o   (transf_cnt_o)				      
    );
  
endmodule // chip_top
`default_nettype wire
