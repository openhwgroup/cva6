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

`include "sd_defines.h"

module sd_fifo_filler(
           input wb_clk,
           input rst,
           //WB Signals
           output reg [31:0] wbm_adr_o,
           output reg wbm_we_o,
           output [31:0] wbm_dat_o,
           input [31:0] wbm_dat_i,
           output wbm_cyc_o,
           output wbm_stb_o,
           input wbm_ack_i,
           //Data Master Control signals
           input en_rx_i,
           input en_tx_i,
           input [31:0] adr_i,
           input [`BLKSIZE_W+`BLKCNT_W-1:0] xfersize,
           //Data Serial signals
           input sd_clk,
           input [31:0] dat_i,
           output [31:0] dat_o,
           input wr_i,
           input rd_i,
           output sd_full_o,
           output sd_empty_o
       );

`define FIFO_MEM_ADR_SIZE 4
`define MEM_OFFSET 4

reg [`BLKSIZE_W+`BLKCNT_W-1:0] xfersize_f;
reg wb2sd_wr_en;

always @(posedge wb_clk or posedge rst) begin
    if (rst) begin
        wbm_adr_o       <=  0;
        wbm_we_o        <=  0;
        xfersize_f      <=  0;
    end else begin
        if (en_rx_i) begin  // RX is reading from SD and writing to wishbone
            wbm_we_o    <=  1'b1;
        end else if (en_tx_i) begin
            wbm_we_o    <=  1'b0;
        end

        if (en_rx_i || en_tx_i) begin
            wbm_adr_o   <=  adr_i;
            xfersize_f  <=  xfersize[`BLKSIZE_W+`BLKCNT_W-1:2] - ((xfersize[1:0] == 2'b0) ? 1 : 0);
        end else if ((wbm_we_o && wbm_cyc_o && wbm_ack_i) || (~wbm_we_o && wb2sd_wr_en)) begin
            wbm_adr_o   <=  wbm_adr_o + `MEM_OFFSET;
            xfersize_f  <=  xfersize_f - 1;
        end
    end
end

reg sd2wb_rd_en;
reg sd2wb_wb_cyc_o;
wire sd2wb_empty;

localparam SD2WB_STATE_IDLE = 2'd0;
localparam SD2WB_STATE_READ_PENDING = 2'd1;
localparam SD2WB_STATE_WRITE_PENDING = 2'd2;

reg [1:0] sd2wb_state;

sd_data_fifo sd2wb_fifo (
    .rst(rst)
    ,.wr_clk(sd_clk)
    ,.wr_en(wr_i)
    ,.din(dat_i)
    ,.full(sd_full_o)
    ,.rd_clk(wb_clk)
    ,.rd_en(sd2wb_rd_en)
    ,.dout(wbm_dat_o)
    ,.empty(sd2wb_empty)
    );

always @(posedge wb_clk or posedge rst) begin
    if (rst) begin
        sd2wb_state     <=  SD2WB_STATE_IDLE;
    end else begin
        case (sd2wb_state)
            SD2WB_STATE_IDLE: begin
                if (en_rx_i) begin
                    sd2wb_state     <=  SD2WB_STATE_READ_PENDING;
                end
            end
            SD2WB_STATE_READ_PENDING: begin
                if (sd2wb_rd_en) begin
                    sd2wb_state     <=  SD2WB_STATE_WRITE_PENDING;
                end
            end
            SD2WB_STATE_WRITE_PENDING: begin
                if (wbm_cyc_o & wbm_ack_i) begin
                    if (xfersize_f == 0) begin
                        sd2wb_state <=  SD2WB_STATE_IDLE;
                    end else begin
                        sd2wb_state <=  SD2WB_STATE_READ_PENDING;
                    end
                end
            end
        endcase
    end
end

always @* begin
    sd2wb_rd_en = 1'b0;
    sd2wb_wb_cyc_o = 1'b0;

    case (sd2wb_state)
        SD2WB_STATE_READ_PENDING: begin
            sd2wb_rd_en = !sd2wb_empty;
        end
        SD2WB_STATE_WRITE_PENDING: begin
            sd2wb_wb_cyc_o = !en_rx_i && !en_tx_i;
        end
    endcase
end

reg wb2sd_wb_cyc_o;
reg [31:0] wb2sd_din_f;
wire wb2sd_full;

localparam WB2SD_STATE_IDLE = 2'd0;
localparam WB2SD_STATE_READ_PENDING = 2'd1;
localparam WB2SD_STATE_WRITE_PENDING = 2'd2;

reg [1:0] wb2sd_state;

sd_data_fifo wb2sd_fifo (
    .rst(rst)
    ,.wr_clk(wb_clk)
    ,.wr_en(wb2sd_wr_en)
    ,.din(wb2sd_din_f)
    ,.full(wb2sd_full)
    ,.rd_clk(sd_clk)
    ,.rd_en(rd_i)
    ,.dout(dat_o)
    ,.empty(sd_empty_o)
    );

always @(posedge wb_clk or posedge rst) begin
    if (rst) begin
        wb2sd_din_f     <=  0;
        wb2sd_state     <=  WB2SD_STATE_IDLE;
    end else begin
        if (wbm_cyc_o & wbm_ack_i) begin
            wb2sd_din_f <=  wbm_dat_i;
        end

        case (wb2sd_state)
            WB2SD_STATE_IDLE: begin
                if (en_tx_i) begin
                    wb2sd_state     <=  WB2SD_STATE_READ_PENDING;
                end
            end
            WB2SD_STATE_READ_PENDING: begin
                if (wbm_cyc_o & wbm_ack_i) begin
                    wb2sd_state     <=  WB2SD_STATE_WRITE_PENDING;
                end
            end
            WB2SD_STATE_WRITE_PENDING: begin
                if (wb2sd_wr_en) begin
                    if (xfersize_f == 0) begin
                        wb2sd_state <=  WB2SD_STATE_IDLE;
                    end else begin
                        wb2sd_state <=  WB2SD_STATE_READ_PENDING;
                    end
                end
            end
        endcase
    end
end

always @* begin
    wb2sd_wr_en = 1'b0;
    wb2sd_wb_cyc_o = 1'b0;

    case (wb2sd_state)
        WB2SD_STATE_READ_PENDING: begin
            wb2sd_wb_cyc_o = !en_rx_i && !en_tx_i;
        end
        WB2SD_STATE_WRITE_PENDING: begin
            wb2sd_wr_en = !wb2sd_full;
        end
    endcase
end

assign wbm_cyc_o = wbm_we_o ? sd2wb_wb_cyc_o : wb2sd_wb_cyc_o;
assign wbm_stb_o = wbm_cyc_o;

endmodule
