//////////////////////////////////////////////////////////////////////
////                                                              ////
//// WISHBONE SD Card Controller IP Core                          ////
////                                                              ////
//// sd_fifo_filler.v                                             ////
////                                                              ////
//// This file is part of the WISHBONE SD Card                    ////
//// Controller IP Core project                                   ////
//// http://opencores.org/project,sd_card_controller              ////
////                                                              ////
//// Description                                                  ////
//// Fifo interface between sd card and wishbone clock domains    ////
//// and DMA engine eble to write/read to/from CPU memory         ////
////                                                              ////
//// Author(s):                                                   ////
////     - Marek Czerski, ma.czerski@gmail.com                    ////
////                                                              ////
//////////////////////////////////////////////////////////////////////
////                                                              ////
//// Copyright (C) 2013 Authors                                   ////
////                                                              ////
//// Based on original work by                                    ////
////     Adam Edvardsson (adam.edvardsson@orsoc.se)               ////
////                                                              ////
////     Copyright (C) 2009 Authors                               ////
////                                                              ////
//// This source file may be used and distributed without         ////
//// restriction provided that this copyright statement is not    ////
//// removed from the file and that any derivative work contains  ////
//// the original copyright notice and the associated disclaimer. ////
////                                                              ////
//// This source file is free software; you can redistribute it   ////
//// and/or modify it under the terms of the GNU Lesser General   ////
//// Public License as published by the Free Software Foundation; ////
//// either version 2.1 of the License, or (at your option) any   ////
//// later version.                                               ////
////                                                              ////
//// This source is distributed in the hope that it will be       ////
//// useful, but WITHOUT ANY WARRANTY; without even the implied   ////
//// warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR      ////
//// PURPOSE. See the GNU Lesser General Public License for more  ////
//// details.                                                     ////
////                                                              ////
//// You should have received a copy of the GNU Lesser General    ////
//// Public License along with this source; if not, download it   ////
//// from http://www.opencores.org/lgpl.shtml                     ////
////                                                              ////
//////////////////////////////////////////////////////////////////////

module sd_fifo_filler(
           input wb_clk,
           input rst,
           //WB Signals
           output reg [31:0] wbm_adr_o,
           output wbm_we_o,
           output [31:0] wbm_dat_o,
           input [31:0] wbm_dat_i,
           output wbm_cyc_o,
           output wbm_stb_o,
           input wbm_ack_i,
           //Data Master Control signals
           input en_rx_i,
           input en_tx_i,
           input [31:0] adr_i,
           //Data Serial signals
           input sd_clk,
           input [31:0] dat_i,
           output [31:0] dat_o,
           input wr_i,
           input rd_i,
           output sd_full_o,
           output sd_empty_o,
           output wb_full_o,
           output wb_empty_o
       );

`define FIFO_MEM_ADR_SIZE 4
`define MEM_OFFSET 4

wire reset_fifo;
wire fifo_rd;
reg fifo_rd_ack;
reg fifo_rd_reg;

assign fifo_rd = wbm_cyc_o & wbm_ack_i;
assign reset_fifo = !en_rx_i & !en_tx_i;

assign wbm_we_o = en_rx_i & !wb_empty_o;
assign wbm_cyc_o = en_rx_i ? en_rx_i & !wb_empty_o : en_tx_i & !wb_full_o;
assign wbm_stb_o = en_rx_i ? wbm_cyc_o & fifo_rd_ack : wbm_cyc_o;

    `ifdef PITON_FPGA_SYNTH
xpm_fifo_async #(
  .FIFO_WRITE_DEPTH(16),   // DECIMAL
  .READ_DATA_WIDTH(32),      // DECIMAL
  .WRITE_DATA_WIDTH(32)     // DECIMAL
) sd2wb (
  .almost_empty(),
  .almost_full(),
  .data_valid(),
  .dbiterr(),
  .dout(wbm_dat_o),
  .empty(wb_empty_o),
  .full(sd_full_o),
  .overflow(),
  .prog_empty(),
  .prog_full(),
  .rd_data_count(),
  .rd_rst_busy(),
  .sbiterr(),
  .underflow(),
  .wr_ack(),
  .wr_data_count(),
  .wr_rst_busy(),
  .din(dat_i),
  .injectdbiterr(1'b0),
  .injectsbiterr(1'b0),
  .rd_clk(wb_clk),
  .rd_en(en_rx_i & wbm_cyc_o & wbm_ack_i),
  .rst(rst | reset_fifo),
  .sleep(1'b0),
  .wr_clk(sd_clk),
  .wr_en(wr_i)
);
    `else
generic_fifo_dc_gray #(
    .dw(32),
    .aw(`FIFO_MEM_ADR_SIZE)
    ) generic_fifo_dc_gray0 (
    .rd_clk(wb_clk),
    .wr_clk(sd_clk),
    .rst(!(rst | reset_fifo)),
    .clr(1'b0),
    .din(dat_i),
    .we(wr_i),
    .dout(wbm_dat_o),
    .re(en_rx_i & wbm_cyc_o & wbm_ack_i),
    .full(sd_full_o),
    .empty(wb_empty_o),
    .wr_level(),
    .rd_level()
    );
    `endif

    `ifndef PITON_FPGA_SYNTH
xpm_fifo_async #(
  .FIFO_WRITE_DEPTH(16),   // DECIMAL
  .READ_DATA_WIDTH(32),      // DECIMAL
  .WRITE_DATA_WIDTH(32)     // DECIMAL
) sd2wb (
  .almost_empty(),
  .almost_full(),
  .data_valid(),
  .dbiterr(),
  .dout(dat_o),
  .empty(sd_empty_o),
  .full(wb_full_o),
  .overflow(),
  .prog_empty(),
  .prog_full(),
  .rd_data_count(),
  .rd_rst_busy(),
  .sbiterr(),
  .underflow(),
  .wr_ack(),
  .wr_data_count(),
  .wr_rst_busy(),
  .din(wbm_dat_i),
  .injectdbiterr(1'b0),
  .injectsbiterr(1'b0),
  .rd_clk(sd_clk),
  .rd_en(rd_i),
  .rst(rst | reset_fifo),
  .sleep(1'b0),
  .wr_clk(wb_clk),
  .wr_en(en_tx_i & wbm_cyc_o & wbm_stb_o & wbm_ack_i)
);
    `else
generic_fifo_dc_gray #(
    .dw(32),
    .aw(`FIFO_MEM_ADR_SIZE)
) generic_fifo_dc_gray1 (
    .rd_clk(sd_clk),
    .wr_clk(wb_clk),
    .rst(!(rst | reset_fifo)),
    .clr(1'b0),
    .din(wbm_dat_i),
    .we(en_tx_i & wbm_cyc_o & wbm_stb_o & wbm_ack_i),
    .dout(dat_o),
    .re(rd_i),
    .full(wb_full_o),
    .empty(sd_empty_o),
    .wr_level(),
    .rd_level()
);
    `endif

always @(posedge wb_clk or posedge rst)
    if (rst) begin
        wbm_adr_o <= 0;
        fifo_rd_reg <= 0;
        fifo_rd_ack <= 1;
    end
    else begin
        fifo_rd_reg <= fifo_rd;
        fifo_rd_ack <= fifo_rd_reg | !fifo_rd;
        if (wbm_cyc_o & wbm_stb_o & wbm_ack_i)
            wbm_adr_o <= wbm_adr_o + `MEM_OFFSET;
        else if (reset_fifo)
            wbm_adr_o <= adr_i;
    end

endmodule


