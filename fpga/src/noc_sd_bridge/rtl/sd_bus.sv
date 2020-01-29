// Copyright 2015 ETH Zurich, University of Bologna, and University of Cambridge
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

module sd_bus
  (
 input wire         clk_200MHz,
 input wire         msoc_clk,
 input wire         rstn,
 output wire        sd_sclk,
 input wire         sd_detect,
 inout wire [3:0]   sd_dat,
 inout wire         sd_cmd,
 output wire        sd_reset,
 output reg         sd_irq,
 input wire         spisd_en,
 input wire         spisd_we,
 input wire [7:0]   spisd_be,
 input wire [15:0]  spisd_addr,
 input wire [63:0]  spisd_wrdata,
 output wire [63:0] spisd_rddata
 );

 reg [15:0]         spisd_addr_0;
                                  
`include "piton_sd_define.vh"

 logic sys_clk, sd_clk_out, init_done;
// 4-bit full SD interface
 wire    [3:0]       sd_dat_dat_i;
 wire    [3:0]       sd_dat_out_o;
 wire                sd_dat_oe_o;
 wire                sd_cmd_dat_i;
 wire                sd_cmd_out_o;
 wire                sd_cmd_oe_o;
 wire                sd_int_cmd;
 wire                sd_int_data;

 // Request Slave
 logic [`SD_ADDR_WIDTH-1:0]    req_addr_sd;    // addr in SD 
 logic [`SD_ADDR_WIDTH-1:0]    req_addr_dma;   // addr in fake memory
 logic [`SD_ADDR_WIDTH-10:0]   req_blkcnt;

 logic                         req_wr;         // HIGH write
 logic                         req_rd;         // HIGH read
 logic                         req_wr_0;       // HIGH write delayed
 logic                         req_rd_0;       // HIGH read delayed
 logic                         req_wr_1;       // HIGH write delayed
 logic                         req_rd_1;       // HIGH read delayed
 logic [`SD_ADDR_WIDTH-1:0]    req_addr_sd_f;  // addr in SD 
 logic [`SD_ADDR_WIDTH-1:0]    req_addr_dma_f; // addr in fake DMA memory
 logic                         sd_irq_en;
  logic   [31:0]      core_buffer_addr;
  logic                core_buffer_ce;
  logic                core_buffer_wr;
  logic   [1:0]       core_buffer_sz;
  logic   [`NOC_DATA_BITS]    core_buffer_data;
  logic   [`NOC_DATA_BITS]    buffer_core_data;
 
  logic   [3:0] sys_rst_reg;
  
 wire                         req_rdy, is_hcxc;
 wire                         sys_rst = !(&sys_rst_reg) | !rstn;
 // Response Master
 wire                         resp_ok;    // HIGH ok; LOW err.
 wire                         resp_val;
logic                         resp_rdy;
logic [63:0]                  resp_vec, resp_data, spisd_wrdata_rev, spisd_rddata_norev, spisd_rddata_rev;
wire [7:0]                    init_state;
// compact FSM output
wire [23:0]                   counter;
wire [42:0]                   init_fsm; // {adr, dat, we, stb, counter_en}
wire  [5:0]                   tran_state;
// tran compact FSM output
wire [41:0]                   tran_fsm; // {adr, dat, we, stb}

for (genvar i = 0; i < 64; i += 8)
    begin
        assign spisd_wrdata_rev[i +: 8] = spisd_wrdata[(56-i) +: 8];
        assign spisd_rddata_rev[i +: 8] = spisd_rddata_norev[(56-i) +: 8];
    end
    
always @(posedge msoc_clk or negedge rstn)
  if (!rstn)
    begin
       sd_irq <= 0;
       sd_irq_en <= 0;
       resp_vec <= 0;
       sys_rst_reg <= 0;
       req_rd_0 <= 0;
       req_wr_0 <= 0;
       req_rd_1 <= 0;
       req_wr_1 <= 0;
       req_rd <= 0;
       req_wr <= 0;
       req_addr_sd <= 0;
       req_addr_dma <= 0;
   end
   else
     begin
        spisd_addr_0 <= spisd_addr;
        
        if (resp_val)
            resp_vec <= {resp_vec,resp_ok};
        resp_rdy <= resp_val;
        sd_irq <= sd_irq_en & req_rdy & (req_wr|req_rd);
        sys_rst_reg <= sys_rst_reg + sys_rst;
        req_rd_0 <= req_rd;
        req_wr_0 <= req_wr;
        req_rd_1 <= req_rd & ~req_rd_0;
        req_wr_1 <= req_wr & ~req_wr_0;
        
        if (spisd_en&(|spisd_we)&(spisd_addr[15:14]==2'b00))
	  case(spisd_addr[6:3])
	    0: req_addr_sd <= spisd_wrdata;
	    1: req_addr_dma <= spisd_wrdata;
	    2: begin resp_vec <= 0; req_blkcnt <= spisd_wrdata; end
	    3: req_rd <= spisd_wrdata;
	    4: req_wr <= spisd_wrdata;
	    5: sd_irq_en <= spisd_wrdata;
	    6: if (spisd_wrdata) sys_rst_reg <= 0;
	    default:;
	  endcase
	case(spisd_addr[7:3])
	    0: resp_data <= req_addr_sd_f;
	    1: resp_data <= req_addr_dma_f;
            2: resp_data <= {sd_detect,is_hcxc,init_done,req_rdy,sd_irq,sd_irq_en,req_wr,req_rd};
            3: resp_data <= resp_vec;
            4: resp_data <= init_state;
            5: resp_data <= counter;
            6: resp_data <= init_fsm;
            7: resp_data <= tran_state;
            8: resp_data <= tran_fsm;
            default: resp_data <= 32'HDEADBEEF;
        endcase
    end

`ifdef ILA_RESP

ila_1 ila_resp (
	.clk(msoc_clk), // input wire clk
	.probe0(req_addr_sd_f), // input wire [0:0]  probe0  
	.probe1(req_addr_dma_f), // input wire [0:0]  probe1 
	.probe2({sd_detect,is_hcxc,init_done,req_rdy,sd_irq,sd_irq_en,req_wr,req_rd}), // input wire [0:0]  probe2 
	.probe3(resp_vec), // input wire [3:0]  probe3 
	.probe4(init_state), // input wire [3:0]  probe4 
	.probe5(counter), // input wire [0:0]  probe5 
	.probe6(init_fsm), // input wire [0:0]  probe6 
	.probe7(tran_state), // input wire [0:0]  probe7 
	.probe8(tran_fsm), // input wire [0:0]  probe6 
	.probe9({sys_rst_reg,sd_irq_en,req_wr,req_rd}) // input wire [0:0]  probe6 
);

`endif

   assign  sd_cmd      =   sd_cmd_oe_o ? sd_cmd_out_o : 1'bz;
   assign  sd_dat      =   sd_dat_oe_o ? sd_dat_out_o : 4'bz;
   assign  sd_cmd_dat_i    =   sd_cmd;
   assign  sd_dat_dat_i    =   sd_dat;
   assign  sd_reset    =   sys_rst;

   wire    sd_clk_out_internal;

   ODDR sd_clk_oddr (
            .Q(sd_clk_out),
            .C(sd_clk_out_internal),
            .CE(1),
            .D1(1),
            .D2(0),
            .R(0),
            .S(0)
            );

piton_sd_top dut
(
    // Clock and reset
    .sys_clk(msoc_clk),
    .sd_clk(msoc_clk),
    .sys_rst(sys_rst),

    // SD interface
    .sd_cd(sd_detect),
    .sd_reset,
    .sd_clk_out(sd_clk_out_internal),
    .sd_cmd_dat_i,
    .sd_cmd_out_o,
    .sd_cmd_oe_o,
    .sd_dat_dat_i,
    .sd_dat_out_o,
    .sd_dat_oe_o,

    .init_done,
    .req_addr_sd            (req_addr_sd),
    .req_addr_dma           (req_addr_dma),
    .req_blkcnt             (req_blkcnt),
    .req_wr                 (req_wr_1),
    .req_val                (req_wr_1|req_rd_1),
    .req_rdy                (req_rdy),
    .req_addr_sd_f          (req_addr_sd_f),
    .req_addr_dma_f         (req_addr_dma_f),

    .resp_ok                (resp_ok),
    .resp_val               (resp_val),
    .resp_rdy               (resp_rdy),
    
    .core_buffer_addr(spisd_addr),
    .core_buffer_data(spisd_wrdata_rev),
    .core_buffer_ce(spisd_en & spisd_addr[15]),
    .core_buffer_wr(|spisd_we),
    .core_buffer_sz(3),
    .buffer_core_data(spisd_rddata_norev),

    .is_hcxc                (is_hcxc),
    .init_state             (init_state),
    // compact FSM output
    .counter,
    .init_fsm, // {adr, dat, we, stb, counter_en}
    .tran_state             (tran_state),
    // compact FSM output
    .tran_fsm               (tran_fsm) // {adr, dat, we, stb, counter_en}
 
    );

   assign             spisd_rddata = spisd_addr_0[15] ? spisd_rddata_rev : resp_data;  
   assign             sd_sclk = sd_clk_out;
   
endmodule // chip_top

`default_nettype wire
