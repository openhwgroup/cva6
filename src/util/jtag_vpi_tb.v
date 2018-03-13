/*
 * Test bench for VPI JTAG Interface
 *
 * Copyright (C) 2012 Franck Jullien, <franck.jullien@gmail.com>
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation  and/or other materials provided with the distribution.
 * 3. Neither the names of the copyright holders nor the names of any
 *    contributors may be used to endorse or promote products derived from this
 *    software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE
 * LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
 * CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
 * SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
 * INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
 * CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
 * ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
 * POSSIBILITY OF SUCH DAMAGE.
 */

`timescale 1ns/1ps

//`define FPGA_FULL
//`define ADD_PHY_DDR
`define NEXYS4

module jtag_vpi_tb;

wire		tdo_pad_o;
wire		tck_pad_i;
wire		tms_pad_i;
wire		tdi_pad_i;

wire		jtag_tap_tdo;
wire		jtag_tap_shift_dr;
wire		jtag_tap_pause_dr;
wire		jtag_tap_update_dr;
wire		jtag_tap_capture_dr;
wire		user1_select;
wire		user2_select;
wire		user3_select;
wire		user4_select;

wire	[31:0]	wb_adr;
wire	[31:0]	wb_dat;
wire	[3:0]	wb_sel;
wire		wb_we;
wire	[1:0]	wb_bte;
wire	[2:0]	wb_cti;
wire		wb_cyc;
wire		wb_stb;
wire		wb_ack;
wire		wb_err;
wire	[31:0]	wb_sdt;

reg		sys_clock = 0;
reg		sys_reset = 0;

initial begin
	$dumpfile("jtag_vpi.vcd");
	$dumpvars(0);
end

always
	#20 sys_clock <= ~sys_clock;

initial begin
	#100 sys_reset <= 1;
	#200 sys_reset <= 0;
end

jtag_vpi #(.DEBUG_INFO(0))
jtag_vpi0
(
	.tms(tms_pad_i),
	.tck(tck_pad_i),
	.tdi(tdi_pad_i),
	.tdo(tdo_pad_o),

	.enable(1'b1),
	.init_done(1'b1)
);

jtag_tap jtag_tap0
(
	.tdo_pad_o			(tdo_pad_o),
	.tms_pad_i			(tms_pad_i),
	.tck_pad_i			(tck_pad_i),
	.trst_pad_i			(1'b0),
	.tdi_pad_i			(tdi_pad_i),

	.tdo_padoe_o			(),

	.tdo_o				(jtag_tap_tdo),

	.shift_dr_o			(jtag_tap_shift_dr),
	.pause_dr_o			(jtag_tap_pause_dr),
	.update_dr_o			(jtag_tap_update_dr),
	.capture_dr_o			(jtag_tap_capture_dr),

	.user1_select_o		        (user1_select),
	.user2_select_o		        (user2_select),
	.user3_select_o		        (user3_select),
	.user4_select_o		        (user4_select),
 
	.extest_select_o		(),
	.sample_preload_select_o	(),

	.user1_tdi_i			(glbl.JTAG_USER_TDO1_GLBL),
	.user2_tdi_i			(glbl.JTAG_USER_TDO2_GLBL),
	.user3_tdi_i			(glbl.JTAG_USER_TDO3_GLBL),
	.user4_tdi_i			(glbl.JTAG_USER_TDO4_GLBL),

	.bs_chain_tdi_i			(1'b0)
);

   assign glbl.JTAG_CAPTURE_GLBL = jtag_tap_capture_dr;
   assign glbl.JTAG_RESET_GLBL = sys_reset;
   assign glbl.JTAG_SHIFT_GLBL = jtag_tap_shift_dr;
   assign glbl.JTAG_UPDATE_GLBL = jtag_tap_update_dr;
   assign glbl.JTAG_RUNTEST_GLBL = 1'b0;
   assign glbl.JTAG_TCK_GLBL = tck_pad_i;
   assign glbl.JTAG_TDI_GLBL = jtag_tap_tdo;
   assign glbl.JTAG_TMS_GLBL = tms_pad_i;
   assign glbl.JTAG_TRST_GLBL = 1'b0;
   assign glbl.JTAG_SEL1_GLBL = user1_select;
   assign glbl.JTAG_SEL2_GLBL = user2_select;
   assign glbl.JTAG_SEL3_GLBL = user3_select;
   assign glbl.JTAG_SEL4_GLBL = user4_select;
   
   logic clk, rst;

   wrap_top DUT
     (
      .*,
      .clk_p        ( clk       ),
      .clk_n        ( !clk      ),
      .rst_top      ( !rst      )         // NEXYS4's cpu_reset is active low
      );

   initial begin
      rst = 1;
      #130;
      rst = 0;
   end

   initial begin
      clk = 0;
      forever clk = #5 !clk;
   end // initial begin

    // 7-segment display
   wire       CA;
   wire       CB;
   wire       CC;
   wire       CD;
   wire       CE;
   wire       CF;
   wire       CG;
   wire       DP;
   wire [7:0] AN;

   wire [15:0]  ddr_dq;
   wire [1:0]   ddr_dqs_n;
   wire [1:0]   ddr_dqs_p;
   logic [12:0] ddr_addr;
   logic [2:0]  ddr_ba;
   logic        ddr_ras_n;
   logic        ddr_cas_n;
   logic        ddr_we_n;
   logic        ddr_ck_p;
   logic        ddr_ck_n;
   logic        ddr_cke;
   logic        ddr_cs_n;
   wire [1:0]   ddr_dm;
   logic        ddr_odt;

   // behavioural DDR2 RAM
   ddr2_model u_comp_ddr2
     (
      .ck      ( ddr_ck_p        ),
      .ck_n    ( ddr_ck_n        ),
      .cke     ( ddr_cke         ),
      .cs_n    ( ddr_cs_n        ),
      .ras_n   ( ddr_ras_n       ),
      .cas_n   ( ddr_cas_n       ),
      .we_n    ( ddr_we_n        ),
      .dm_rdqs ( ddr_dm          ),
      .ba      ( ddr_ba          ),
      .addr    ( ddr_addr        ),
      .dq      ( ddr_dq          ),
      .dqs     ( ddr_dqs_p       ),
      .dqs_n   ( ddr_dqs_n       ),
      .rdqs_n  (                 ),
      .odt     ( ddr_odt         )
      );

   wire         rxd;
   wire         txd;
   wire         rts;
   wire         cts;

   assign rxd = 'b1;
   assign cts = 'b1;

reg u_trans;
reg [15:0] u_baud;
wire received, recv_err, is_recv, is_trans, u_tx, u_rx;
wire [7:0] u_rx_byte;
reg  [7:0] u_tx_byte;

   assign u_trans = received;
   assign u_tx_byte = u_rx_byte;
   assign u_baud = 16'd52;
   assign u_rx = txd;
   
uart i_uart(
    .clk(clk), // The master clock for this module
    .rst(rst), // Synchronous reset.
    .rx(u_rx), // Incoming serial line
    .tx(u_tx), // Outgoing serial line
    .transmit(u_trans), // Signal to transmit
    .tx_byte(u_tx_byte), // Byte to transmit
    .received(received), // Indicated that a byte has been received.
    .rx_byte(u_rx_byte), // Byte received
    .is_receiving(is_recv), // Low when receive line is idle.
    .is_transmitting(is_trans), // Low when transmit line is idle.
    .recv_error(recv_err), // Indicates error in receiving packet.
    .baud(u_baud),
    .recv_ack(received)
    );

   // 4-bit full SD interface
   wire         sd_sclk;
   wire         sd_detect = 1'b0; // Simulate SD-card always there
   wire [3:0]   sd_dat_to_host;
   wire         sd_cmd_to_host;
   wire         sd_reset, oeCmd, oeDat;
   wand [3:0]   sd_dat = oeDat ? sd_dat_to_host : 4'b1111;
   wand         sd_cmd = oeCmd ? sd_cmd_to_host : 4'b1;

sd_verilator_model sdflash1 (
             .sdClk(sd_sclk),
             .cmd(sd_cmd),
             .cmdOut(sd_cmd_to_host),
             .dat(sd_dat),
             .datOut(sd_dat_to_host),
             .oeCmd(oeCmd),
             .oeDat(oeDat)
);

   // LED and DIP switch
   wire [7:0]   o_led;
   wire [15:0]   i_dip;

   assign i_dip = 16'h0;

   // push button array
   wire         GPIO_SW_C;
   wire         GPIO_SW_W;
   wire         GPIO_SW_E;
   wire         GPIO_SW_N;
   wire         GPIO_SW_S;

   assign GPIO_SW_C = 'b1;
   assign GPIO_SW_W = 'b1;
   assign GPIO_SW_E = 'b1;
   assign GPIO_SW_N = 'b1;
   assign GPIO_SW_S = 'b1;

   //keyboard
   wire         PS2_CLK;
   wire         PS2_DATA;

   assign PS2_CLK = 'bz;
   assign PS2_DATA = 'bz;

  // display
   wire        VGA_HS_O;
   wire        VGA_VS_O;
   wire [3:0]  VGA_RED_O;
   wire [3:0]  VGA_BLUE_O;
   wire [3:0]  VGA_GREEN_O;

   // vcd
   initial begin
         $dumpfile("test.vcd");
         $dumpvars(0, jtag_vpi_tb);
         $dumpon;
      end

  wire         o_erefclk; // RMII clock out
  wire [1:0]   i_erxd ;
  wire         i_erx_dv ;
  wire         i_erx_er ;
  wire         i_emdint ;
  wire [1:0]   o_etxd ;
  wire         o_etx_en ;
  wire         o_emdc ;
  wire         io_emdio ;
  wire         o_erstn ;

   assign i_emdint = 1'b1;
   assign i_erx_dv = o_etx_en;
   assign i_erxd = o_etxd;
   assign i_erx_er = 1'b0;
   
endmodule
