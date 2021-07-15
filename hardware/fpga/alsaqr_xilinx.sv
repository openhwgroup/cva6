//-----------------------------------------------------------------------------
// Title         : PULPissimo Verilog Wrapper
//-----------------------------------------------------------------------------
// File          : alsaqr_xilinx.v
// Author        : Luca Valente <luca.valente@unibo.it>
// Created       : 15-07-2021
//-----------------------------------------------------------------------------
// Description :
// Verilog Wrapper of AlSaqr to use the module within Xilinx IP integrator.
//-----------------------------------------------------------------------------
// Copyright (C) 2021 ETH Zurich, University of Bologna
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//-----------------------------------------------------------------------------

module alsaqr_xilinx
  (
   input wire  ref_clk_p,
   input wire  ref_clk_n,

   inout wire  pad_uart_rx,
   inout wire  pad_uart_tx,
   
   inout       FMC_hyper_dqio0 ,
   inout       FMC_hyper_dqio1 ,
   inout       FMC_hyper_dqio2 ,
   inout       FMC_hyper_dqio3 ,
   inout       FMC_hyper_dqio4 ,
   inout       FMC_hyper_dqio5 ,
   inout       FMC_hyper_dqio6 ,
   inout       FMC_hyper_dqio7 ,
   inout       FMC_hyper_ck    ,
   inout       FMC_hyper_ckn   ,
   inout       FMC_hyper_csn0  ,
   inout       FMC_hyper_csn1  ,
   inout       FMC_hyper_rwds0 ,
   inout       FMC_hyper_reset ,

   input wire  pad_reset,

   input wire  pad_jtag_trst,
   input wire  pad_jtag_tck,
   input wire  pad_jtag_tdi,
   output wire pad_jtag_tdo,
   input wire  pad_jtag_tms
  );

   wire        ref_clk;
   
   //Differential to single ended clock conversion
   IBUFGDS
     #(
       .IOSTANDARD("LVDS"),
       .DIFF_TERM("FALSE"),
       .IBUF_LOW_PWR("FALSE"))
   i_sysclk_iobuf
     (
      .I(ref_clk_p),
      .IB(ref_clk_n),
      .O(ref_clk)
      );
   logic       s_locked;
   logic       s_clk;
   
   xilinx_clk_mngr i_clk_manager
    (
     .resetn(reset_n),
     .clk_in1(ref_clk),
     .clk_out1(s_clk),
     .locked(s_locked)
     );

   // ---------------
   // RTC for CLINT
   // ---------------
   // divide clock by two
   logic       rtc;
   
   always_ff @(posedge s_clk or negedge ndmreset_n) begin
     if (~ndmreset_n) begin
       rtc <= 0;
     end else begin
       rtc <= rtc ^ 1'b1;
     end
   end   

   logic       reset_n;

   assign reset_n = ~pad_reset & pad_jtag_trst;

   wire [7:0] s_pad_hyper_dq0;

   assign s_pad_hyper_dq0[0] = FMC_hyper_dqio0;
   assign s_pad_hyper_dq0[1] = FMC_hyper_dqio1;
   assign s_pad_hyper_dq0[2] = FMC_hyper_dqio2;
   assign s_pad_hyper_dq0[3] = FMC_hyper_dqio3;
   assign s_pad_hyper_dq0[4] = FMC_hyper_dqio4;
   assign s_pad_hyper_dq0[5] = FMC_hyper_dqio5;
   assign s_pad_hyper_dq0[6] = FMC_hyper_dqio6;
   assign s_pad_hyper_dq0[7] = FMC_hyper_dqio7;
   
    al_saqr #(
        .JtagEnable        ( 1'b1          )
    ) i_alsaqr (
        .clk_i                ( s_clk           ),
        .rst_ni               ( reset_n         ),
        .rtc_i                ( rtc             ),
        .dmi_req_valid        (                 ),
        .dmi_req_ready        (                 ),
        .dmi_req_bits_addr    (                 ),
        .dmi_req_bits_op      (                 ),
        .dmi_req_bits_data    (                 ),
        .dmi_resp_valid       (                 ),
        .dmi_resp_ready       (                 ),
        .dmi_resp_bits_resp   (                 ),
        .dmi_resp_bits_data   (                 ),                      
        .jtag_TCK             ( pad_jtag_tck    ),
        .jtag_TMS             ( pad_jtag_tms    ),
        .jtag_TDI             ( pad_jtag_tdi    ),
        .jtag_TRSTn           ( pad_jtag_trst   ),
        .jtag_TDO_data        ( pad_jtag_tdo    ),
        .jtag_TDO_driven      (                 ),
        .pad_hyper_dq0        (                 ),
        .pad_hyper_dq1        (                 ),
        .pad_hyper_ck         (                 ),
        .pad_hyper_ckn        (                 ),
        .pad_hyper_csn0       (                 ),
        .pad_hyper_csn1       (                 ),
        .pad_hyper_rwds0      (                 ),
        .pad_hyper_rwds1      (                 ),
        .pad_hyper_reset      (                 ),
        .pad_gpio             (                 ),
        .cva6_uart_rx_i       ( pad_uart_rx     ),
        .cva6_uart_tx_o       ( pad_uart_tx     ),
        .pad_axi_hyper_dq0    ( s_pad_hyper_dq0 ),
        .pad_axi_hyper_dq1    (                 ),
        .pad_axi_hyper_ck     ( FMC_hyper_ck    ),
        .pad_axi_hyper_ckn    ( FMC_hyper_ckn   ),
        .pad_axi_hyper_csn0   ( FMC_hyper_csn0  ),
        .pad_axi_hyper_csn1   ( FMC_hyper_csn1  ),
        .pad_axi_hyper_rwds0  ( FMC_hyper_rwds0 ),
        .pad_axi_hyper_rwds1  (                 ),
        .pad_axi_hyper_reset  ( FMC_hyper_reset )
   );


endmodule
