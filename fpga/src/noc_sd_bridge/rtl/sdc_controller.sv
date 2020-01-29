//////////////////////////////////////////////////////////////////////
////                                                              ////
//// WISHBONE SD Card Controller IP Core                          ////
////                                                              ////
//// sdc_controller.v                                             ////
////                                                              ////
//// This file is part of the WISHBONE SD Card                    ////
//// Controller IP Core project                                   ////
//// http://opencores.org/project,sd_card_controller              ////
////                                                              ////
//// Description                                                  ////
//// Top level entity.                                            ////
//// This core is based on the "sd card controller" project from  ////
//// http://opencores.org/project,sdcard_mass_storage_controller  ////
//// but has been largely rewritten. A lot of effort has been     ////
//// made to make the core more generic and easily usable         ////
//// with OSs like Linux.                                         ////
//// - data transfer commands are not fixed                       ////
//// - data transfer block size is configurable                   ////
//// - multiple block transfer support                            ////
//// - R2 responses (136 bit) support                             ////
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

module sdc_controller(
           // WISHBONE common
           wb_clk_i, 
           wb_rst_i, 
           // WISHBONE slave
           wb_dat_i, 
           wb_dat_o,
           wb_adr_i, 
           wb_sel_i, 
           wb_we_i, 
           wb_cyc_i, 
           wb_stb_i, 
           wb_ack_o,
           // WISHBONE master
           m_wb_dat_o,
           m_wb_dat_i,
           m_wb_adr_o, 
           m_wb_sel_o, 
           m_wb_we_o,
           m_wb_cyc_o,
           m_wb_stb_o, 
           m_wb_ack_i,
           m_wb_cti_o, 
           m_wb_bte_o,
           //SD BUS
           sd_cmd_dat_i, 
           sd_cmd_out_o, 
           sd_cmd_oe_o, 
           //card_detect,
           sd_dat_dat_i, 
           sd_dat_out_o, 
           sd_dat_oe_o, 
           sd_clk_o_pad,
           sd_clk_i_pad,
           int_cmd, 
           int_data
       );

input wb_clk_i;
input wb_rst_i;
input [31:0] wb_dat_i;
output [31:0] wb_dat_o;
//input card_detect;
input [7:0] wb_adr_i;
input [3:0] wb_sel_i;
input wb_we_i;
input wb_cyc_i;
input wb_stb_i;
output wb_ack_o;
output [31:0] m_wb_adr_o;
output [3:0] m_wb_sel_o;
output m_wb_we_o;
input [31:0] m_wb_dat_i;
output [31:0] m_wb_dat_o;
output m_wb_cyc_o;
output m_wb_stb_o;
input m_wb_ack_i;
output [2:0] m_wb_cti_o;
output [1:0] m_wb_bte_o;
input wire [3:0] sd_dat_dat_i;
output wire [3:0] sd_dat_out_o;
output wire sd_dat_oe_o;
input wire sd_cmd_dat_i;
output wire sd_cmd_out_o;
output wire sd_cmd_oe_o;
output sd_clk_o_pad;
input wire sd_clk_i_pad;
output int_cmd;
output int_data;

//SD clock
wire sd_clk_o; //Sd_clk used in the system
wire [3:0] wr_wbm_sel;
wire [`BLKSIZE_W+`BLKCNT_W-1:0] xfersize;
wire [31:0] wbm_adr;

wire go_idle;
wire cmd_start_wb_clk;
reg cmd_start_sd_clk;
wire [1:0] cmd_setting;
wire cmd_start_tx;
wire [39:0] cmd;
wire [119:0] cmd_response;
wire cmd_crc_ok;
wire cmd_index_ok;
wire cmd_finish;

wire d_write;
wire d_read;
wire [31:0] data_in_rx_fifo;
wire [31:0] data_out_tx_fifo;
wire tx_fifo_empty;
wire rx_fifo_full;
wire sd_data_busy;
wire data_busy;
wire data_crc_ok;
wire rd_fifo;
wire we_fifo;

wire data_start_rx;
wire data_start_tx;
wire cmd_int_rst_sd_clk;
wire cmd_int_rst;
wire data_int_rst_sd_clk;
wire data_int_rst;

wire wb2sd_fifo_wr_en;
wire wb2sd_fifo_rd_en;
reg wb2sd_fifo_rd_en_f;
wire wb2sd_fifo_full;
wire wb2sd_fifo_empty;
wire [39:0] wb2sd_fifo_din;
wire [39:0] wb2sd_fifo_dout;

reg sd2wb_fifo_wr_en;
wire sd2wb_fifo_rd_en;
reg sd2wb_fifo_rd_en_f;
wire sd2wb_fifo_full;
wire sd2wb_fifo_empty;
reg [39:0] sd2wb_fifo_din;
wire [39:0] sd2wb_fifo_dout;

//wb accessible registers
wire [31:0] argument_reg_wb_clk;
wire [`CMD_REG_SIZE-1:0] command_reg_wb_clk;
wire [`CMD_TIMEOUT_W-1:0] cmd_timeout_reg_wb_clk;
wire [`DATA_TIMEOUT_W-1:0] data_timeout_reg_wb_clk;
wire [0:0] software_reset_reg_wb_clk;
reg [31:0] response_0_reg_wb_clk;
reg [31:0] response_1_reg_wb_clk;
reg [31:0] response_2_reg_wb_clk;
reg [31:0] response_3_reg_wb_clk;
wire [`BLKSIZE_W-1:0] block_size_reg_wb_clk;
wire [0:0] controll_setting_reg_wb_clk;
reg [`INT_CMD_SIZE-1:0] cmd_int_status_reg_wb_clk;
reg [`INT_DATA_SIZE-1:0] data_int_status_reg_wb_clk;
wire [`INT_CMD_SIZE-1:0] cmd_int_enable_reg_wb_clk;
wire [`INT_DATA_SIZE-1:0] data_int_enable_reg_wb_clk;
wire [`BLKCNT_W-1:0] block_count_reg_wb_clk;
wire [31:0] dma_addr_reg_wb_clk;
wire [7:0] clock_divider_reg_wb_clk;

reg [31:0] argument_reg_sd_clk;
reg [`CMD_REG_SIZE-1:0] command_reg_sd_clk;
reg [`CMD_TIMEOUT_W-1:0] cmd_timeout_reg_sd_clk;
reg [`DATA_TIMEOUT_W-1:0] data_timeout_reg_sd_clk;
reg [0:0] software_reset_reg_sd_clk;
wire [31:0] response_0_reg_sd_clk;
wire [31:0] response_1_reg_sd_clk;
wire [31:0] response_2_reg_sd_clk;
wire [31:0] response_3_reg_sd_clk;
reg [`BLKSIZE_W-1:0] block_size_reg_sd_clk;
reg [0:0] controll_setting_reg_sd_clk;
wire [`INT_CMD_SIZE-1:0] cmd_int_status_reg_sd_clk;
reg [`INT_CMD_SIZE-1:0] cmd_int_status_reg_sd_clk_f;
wire [`INT_DATA_SIZE-1:0] data_int_status_reg_sd_clk;
reg [`INT_DATA_SIZE-1:0] data_int_status_reg_sd_clk_f;
reg [`BLKCNT_W-1:0] block_count_reg_sd_clk;
reg [1:0] dma_addr_reg_sd_clk;
reg [7:0] clock_divider_reg_sd_clk;

sd_clock_divider clock_divider0(
    .CLK (sd_clk_i_pad),
    .DIVIDER (clock_divider_reg_sd_clk),
    .RST  (wb_rst_i),
    .SD_CLK  (sd_clk_o)
    );

assign sd_clk_o_pad  = sd_clk_o ;

sd_cmd_master sd_cmd_master0(
    .sd_clk       (sd_clk_o),
    .rst          (wb_rst_i | software_reset_reg_sd_clk[0]),
    .start_i      (cmd_start_sd_clk),
    .int_status_rst_i(cmd_int_rst_sd_clk),
    .setting_o    (cmd_setting),
    .start_xfr_o  (cmd_start_tx),
    .go_idle_o    (go_idle),
    .cmd_o        (cmd),
    .response_i   (cmd_response),
    .crc_ok_i     (cmd_crc_ok),
    .index_ok_i   (cmd_index_ok),
    .busy_i       (sd_data_busy),
    .finish_i     (cmd_finish),
    .argument_i   (argument_reg_sd_clk),
    .command_i    (command_reg_sd_clk),
    .timeout_i    (cmd_timeout_reg_sd_clk),
    .int_status_o (cmd_int_status_reg_sd_clk),
    .response_0_o (response_0_reg_sd_clk),
    .response_1_o (response_1_reg_sd_clk),
    .response_2_o (response_2_reg_sd_clk),
    .response_3_o (response_3_reg_sd_clk)
    );

sd_cmd_serial_host cmd_serial_host0(
    .sd_clk     (sd_clk_o),
    .rst        (wb_rst_i | 
                 software_reset_reg_sd_clk[0] | 
                 go_idle),
    .setting_i  (cmd_setting),
    .cmd_i      (cmd),
    .start_i    (cmd_start_tx),
    .finish_o   (cmd_finish),
    .response_o (cmd_response),
    .crc_ok_o   (cmd_crc_ok),
    .index_ok_o (cmd_index_ok),
    .cmd_dat_i  (sd_cmd_dat_i),
    .cmd_out_o  (sd_cmd_out_o),
    .cmd_oe_o   (sd_cmd_oe_o)
    );

sd_data_master sd_data_master0(
    .sd_clk           (sd_clk_o),
    .rst              (wb_rst_i | 
                       software_reset_reg_sd_clk[0]),
    .start_tx_i       (data_start_tx),
    .start_rx_i       (data_start_rx),
    .timeout_i		  (data_timeout_reg_sd_clk),
    .d_write_o        (d_write),
    .d_read_o         (d_read),
    .tx_fifo_rd_en_i  (rd_fifo),
    .tx_fifo_empty_i  (tx_fifo_empty),
    .rx_fifo_wr_en_i  (we_fifo),
    .rx_fifo_full_i   (rx_fifo_full),
    .xfr_complete_i   (!data_busy),
    .crc_ok_i         (data_crc_ok),
    .int_status_o     (data_int_status_reg_sd_clk),
    .int_status_rst_i (data_int_rst_sd_clk)
    );

sd_data_serial_host sd_data_serial_host0(
    .sd_clk         (sd_clk_o),
    .rst            (wb_rst_i | software_reset_reg_sd_clk[0]),
    .data_in        (data_out_tx_fifo),
    .rd             (rd_fifo),
    .data_out       (data_in_rx_fifo),
    .we             (we_fifo),
    .DAT_oe_o       (sd_dat_oe_o),
    .DAT_dat_o      (sd_dat_out_o),
    .DAT_dat_i      (sd_dat_dat_i),
    .blksize        (block_size_reg_sd_clk),
    .bus_4bit       (controll_setting_reg_sd_clk[0]),
    .blkcnt         (block_count_reg_sd_clk),
    .start          ({d_read, d_write}),
    .byte_alignment (dma_addr_reg_sd_clk),
    .sd_data_busy   (sd_data_busy),
    .busy           (data_busy),
    .crc_ok         (data_crc_ok)
    );
           
sd_fifo_filler sd_fifo_filler0(
    .wb_clk    (wb_clk_i),
    .rst       (wb_rst_i | software_reset_reg_sd_clk[0]),
    .wbm_adr_o (wbm_adr),
    .wbm_we_o  (m_wb_we_o),
    .wbm_dat_o (m_wb_dat_o),
    .wbm_dat_i (m_wb_dat_i),
    .wbm_cyc_o (m_wb_cyc_o),
    .wbm_stb_o (m_wb_stb_o),
    .wbm_ack_i (m_wb_ack_i),
    .en_rx_i   (cmd_start_wb_clk & (command_reg_wb_clk[`CMD_WITH_DATA] == 2'b01)),
    .en_tx_i   (cmd_start_wb_clk & (command_reg_wb_clk[`CMD_WITH_DATA] == 2'b10)),
    .adr_i     (dma_addr_reg_wb_clk),
    .xfersize  (xfersize),
    .sd_clk    (sd_clk_o),
    .dat_i     (data_in_rx_fifo),
    .dat_o     (data_out_tx_fifo),
    .wr_i      (we_fifo),
    .rd_i      (rd_fifo),
    .sd_empty_o   (tx_fifo_empty),
    .sd_full_o   (rx_fifo_full)
    );

assign xfersize = (block_size_reg_wb_clk + 1'b1) * (block_count_reg_wb_clk + 1'b1);
sd_wb_sel_ctrl sd_wb_sel_ctrl0(
        .wb_clk         (wb_clk_i),
        .rst            (wb_rst_i | software_reset_reg_sd_clk[0]),
        .ena            (cmd_start_wb_clk & (command_reg_wb_clk[`CMD_WITH_DATA] == 2'b01)),
        .base_adr_i     (dma_addr_reg_wb_clk),
        .wbm_adr_i      (wbm_adr),
        .xfersize       (xfersize),
        .wbm_sel_o      (wr_wbm_sel)
        );

sd_data_xfer_trig sd_data_xfer_trig0 (
    .sd_clk                (sd_clk_o),
    .rst                   (wb_rst_i | software_reset_reg_sd_clk[0]),
    .cmd_with_data_start_i (cmd_start_sd_clk & 
                            (command_reg_sd_clk[`CMD_WITH_DATA] != 
                             2'b00)),
    .r_w_i                 (command_reg_sd_clk[`CMD_WITH_DATA] == 
                            2'b01),
    .cmd_int_status_i      (cmd_int_status_reg_sd_clk),
    .start_tx_o            (data_start_tx),
    .start_rx_o            (data_start_rx)
    );

sd_controller_wb sd_controller_wb0(
    .wb_clk_i                       (wb_clk_i),
    .wb_rst_i                       (wb_rst_i),
    .wb_dat_i                       (wb_dat_i),
    .wb_dat_o                       (wb_dat_o),
    .wb_adr_i                       (wb_adr_i),
    .wb_sel_i                       (wb_sel_i),
    .wb_we_i                        (wb_we_i),
    .wb_stb_i                       (wb_stb_i),
    .wb_cyc_i                       (wb_cyc_i),
    .wb_ack_o                       (wb_ack_o),
    .cmd_start                      (cmd_start_wb_clk),
    .data_int_rst                   (data_int_rst),
    .cmd_int_rst                    (cmd_int_rst),
    .argument_reg                   (argument_reg_wb_clk),
    .command_reg                    (command_reg_wb_clk),
    .response_0_reg                 (response_0_reg_wb_clk),
    .response_1_reg                 (response_1_reg_wb_clk),
    .response_2_reg                 (response_2_reg_wb_clk),
    .response_3_reg                 (response_3_reg_wb_clk),
    .software_reset_reg             (software_reset_reg_wb_clk),
    .cmd_timeout_reg                (cmd_timeout_reg_wb_clk),
    .data_timeout_reg               (data_timeout_reg_wb_clk),
    .block_size_reg                 (block_size_reg_wb_clk),
    .controll_setting_reg           (controll_setting_reg_wb_clk),
    .cmd_int_status_reg             (cmd_int_status_reg_wb_clk),
    .cmd_int_enable_reg             (cmd_int_enable_reg_wb_clk),
    .clock_divider_reg              (clock_divider_reg_wb_clk),
    .block_count_reg                (block_count_reg_wb_clk),
    .dma_addr_reg                   (dma_addr_reg_wb_clk),
    .data_int_status_reg            (data_int_status_reg_wb_clk),
    .data_int_enable_reg            (data_int_enable_reg_wb_clk),
    .wb2sd_fifo_full                (wb2sd_fifo_full),
    .wb2sd_fifo_wr_en               (wb2sd_fifo_wr_en),
    .wb2sd_fifo_din                 (wb2sd_fifo_din)
    );

// wb -> sd interruptions
cdc_pulse data_int_rst_cross(wb_rst_i, wb_clk_i, data_int_rst, sd_clk_o, data_int_rst_sd_clk);
cdc_pulse cmd_int_rst_cross(wb_rst_i, wb_clk_i, cmd_int_rst, sd_clk_o, cmd_int_rst_sd_clk);

// wb -> sd register synchronization

sd_ctrl_fifo wb2sd_fifo (
    .rst(wb_rst_i)
    ,.wr_clk(wb_clk_i)
    ,.wr_en(wb2sd_fifo_wr_en)
    ,.din(wb2sd_fifo_din)
    ,.full(wb2sd_fifo_full)
    ,.rd_clk(sd_clk_o)
    ,.rd_en(wb2sd_fifo_rd_en)
    ,.dout(wb2sd_fifo_dout)
    ,.empty(wb2sd_fifo_empty)
    );
assign wb2sd_fifo_rd_en = !wb2sd_fifo_empty;
always @(posedge sd_clk_o or posedge wb_rst_i) begin
    if (wb_rst_i) begin
        argument_reg_sd_clk <= 32'd0;
        command_reg_sd_clk <= {`CMD_REG_SIZE{1'b0}};
        software_reset_reg_sd_clk <= 1'b0;
        cmd_timeout_reg_sd_clk <= {`CMD_TIMEOUT_W{1'b0}};
        data_timeout_reg_sd_clk <= {`DATA_TIMEOUT_W{1'b0}};
        block_size_reg_sd_clk <= `RESET_BLOCK_SIZE;
        controll_setting_reg_sd_clk <= 1'b0;
        clock_divider_reg_sd_clk <= 8'd0;
        block_count_reg_sd_clk <= {`BLKCNT_W{1'b0}};
        dma_addr_reg_sd_clk <= 32'd0;
        wb2sd_fifo_rd_en_f <= 1'b0;
        cmd_start_sd_clk <= 1'b0;
    end else begin
        wb2sd_fifo_rd_en_f <= wb2sd_fifo_rd_en;

        if (wb2sd_fifo_rd_en_f) begin
            if (wb2sd_fifo_dout[39:32] == `argument) begin
                cmd_start_sd_clk <= 1'b1;
            end else begin
                cmd_start_sd_clk <= 1'b0;
            end

            case (wb2sd_fifo_dout[39:32])
                `argument: argument_reg_sd_clk <= wb2sd_fifo_dout[31:0];
                `command: command_reg_sd_clk <= wb2sd_fifo_dout[`CMD_REG_SIZE-1:0];
                `reset: software_reset_reg_sd_clk <= wb2sd_fifo_dout[0];
                `cmd_timeout: cmd_timeout_reg_sd_clk <= wb2sd_fifo_dout[`CMD_TIMEOUT_W-1:0];
                `data_timeout: data_timeout_reg_sd_clk <= wb2sd_fifo_dout[`DATA_TIMEOUT_W-1:0];
                `blksize: block_size_reg_sd_clk <= wb2sd_fifo_dout[`BLKSIZE_W-1:0];
                `controller: controll_setting_reg_sd_clk <= wb2sd_fifo_dout[0];
                `clock_d: clock_divider_reg_sd_clk <= wb2sd_fifo_dout[7:0];
                `blkcnt: block_count_reg_sd_clk <= wb2sd_fifo_dout[`BLKCNT_W-1:0];
                `dst_src_addr: dma_addr_reg_sd_clk <= wb2sd_fifo_dout[31:0];
            endcase
        end else begin
            cmd_start_sd_clk <= 1'b0;
        end
    end
end


// wb -> sd register synchronization
sd_ctrl_fifo sd2wb_fifo (
    .rst(wb_rst_i)
    ,.wr_clk(sd_clk_o)
    ,.wr_en(sd2wb_fifo_wr_en)
    ,.din(sd2wb_fifo_din)
    ,.full(sd2wb_fifo_full)
    ,.rd_clk(wb_clk_i)
    ,.rd_en(sd2wb_fifo_rd_en)
    ,.dout(sd2wb_fifo_dout)
    ,.empty(sd2wb_fifo_empty)
    );
assign sd2wb_fifo_rd_en = !sd2wb_fifo_empty;
always @(posedge wb_clk_i or posedge wb_rst_i) begin
    if (wb_rst_i) begin
        response_0_reg_wb_clk <= 32'd0;
        response_1_reg_wb_clk <= 32'd0;
        response_2_reg_wb_clk <= 32'd0;
        response_3_reg_wb_clk <= 32'd0;
        cmd_int_status_reg_wb_clk <= {`INT_CMD_SIZE{1'b0}};
        data_int_status_reg_wb_clk <= {`INT_DATA_SIZE{1'b0}};
        sd2wb_fifo_rd_en_f <= 1'b0;
    end else begin
        sd2wb_fifo_rd_en_f <= sd2wb_fifo_rd_en;

        if (sd2wb_fifo_rd_en_f) begin
            case (sd2wb_fifo_dout[39:32])
                `resp0: response_0_reg_wb_clk <= sd2wb_fifo_dout[31:0];
                `resp1: response_1_reg_wb_clk <= sd2wb_fifo_dout[31:0];
                `resp2: response_2_reg_wb_clk <= sd2wb_fifo_dout[31:0];
                `resp3: response_3_reg_wb_clk <= sd2wb_fifo_dout[31:0];
                `cmd_isr: cmd_int_status_reg_wb_clk <= sd2wb_fifo_dout[`INT_CMD_SIZE-1:0];
                `data_isr: data_int_status_reg_wb_clk <= sd2wb_fifo_dout[`INT_DATA_SIZE-1:0];
            endcase
        end
    end
end

localparam SD2WB_STATE_IDLE = 3'd0;
localparam SD2WB_STATE_RESP0 = 3'd1;
localparam SD2WB_STATE_RESP1 = 3'd2;
localparam SD2WB_STATE_RESP2 = 3'd3;
localparam SD2WB_STATE_RESP3 = 3'd4;
localparam SD2WB_STATE_CMD_ISR = 3'd5;
localparam SD2WB_STATE_DATA_ISR = 3'd6;

reg [2:0] sd2wb_state;

always @(posedge sd_clk_o or posedge wb_rst_i) begin
    if (wb_rst_i) begin
        sd2wb_state <= SD2WB_STATE_IDLE;
        cmd_int_status_reg_sd_clk_f <= {`INT_CMD_SIZE{1'b0}};
        data_int_status_reg_sd_clk_f <= {`INT_DATA_SIZE{1'b0}};
    end else begin
        case (sd2wb_state)
            SD2WB_STATE_IDLE: begin
                if (cmd_int_status_reg_sd_clk != cmd_int_status_reg_sd_clk_f) begin
                    if (cmd_int_status_reg_sd_clk == {`INT_CMD_SIZE{1'b0}}) begin
                        sd2wb_state <= SD2WB_STATE_CMD_ISR;
                    end else begin
                        sd2wb_state <= SD2WB_STATE_RESP0;
                    end
                end else if (data_int_status_reg_sd_clk != data_int_status_reg_sd_clk_f) begin
                    sd2wb_state <= SD2WB_STATE_DATA_ISR;
                end
            end
            SD2WB_STATE_RESP0: begin
                if (sd2wb_fifo_wr_en) begin
                    sd2wb_state <= SD2WB_STATE_RESP1;
                end
            end
            SD2WB_STATE_RESP1: begin
                if (sd2wb_fifo_wr_en) begin
                    sd2wb_state <= SD2WB_STATE_RESP2;
                end
            end
            SD2WB_STATE_RESP2: begin
                if (sd2wb_fifo_wr_en) begin
                    sd2wb_state <= SD2WB_STATE_RESP3;
                end
            end
            SD2WB_STATE_RESP3: begin
                if (sd2wb_fifo_wr_en) begin
                    sd2wb_state <= SD2WB_STATE_CMD_ISR;
                end
            end
            SD2WB_STATE_CMD_ISR: begin
                if (sd2wb_fifo_wr_en) begin
                    cmd_int_status_reg_sd_clk_f <= cmd_int_status_reg_sd_clk;
                    sd2wb_state <= SD2WB_STATE_IDLE;
                end
            end
            SD2WB_STATE_DATA_ISR: begin
                if (sd2wb_fifo_wr_en) begin
                    data_int_status_reg_sd_clk_f <= data_int_status_reg_sd_clk;
                    sd2wb_state <= SD2WB_STATE_IDLE;
                end
            end
        endcase
    end
end

always @* begin
    case (sd2wb_state)
        SD2WB_STATE_RESP0: begin
            sd2wb_fifo_din = {`resp0, response_0_reg_sd_clk};
            sd2wb_fifo_wr_en = ~sd2wb_fifo_full;
        end
        SD2WB_STATE_RESP1: begin
            sd2wb_fifo_din = {`resp1, response_1_reg_sd_clk};
            sd2wb_fifo_wr_en = ~sd2wb_fifo_full;
        end
        SD2WB_STATE_RESP2: begin
            sd2wb_fifo_din = {`resp2, response_2_reg_sd_clk};
            sd2wb_fifo_wr_en = ~sd2wb_fifo_full;
        end
        SD2WB_STATE_RESP3: begin
            sd2wb_fifo_din = {`resp3, response_3_reg_sd_clk};
            sd2wb_fifo_wr_en = ~sd2wb_fifo_full;
        end
        SD2WB_STATE_CMD_ISR: begin
            sd2wb_fifo_din = {`cmd_isr, {(32 - `INT_CMD_SIZE){1'b0}}, cmd_int_status_reg_sd_clk};
            sd2wb_fifo_wr_en = ~sd2wb_fifo_full;
        end
        SD2WB_STATE_DATA_ISR: begin
            sd2wb_fifo_din = {`data_isr, {(32 - `INT_DATA_SIZE){1'b0}}, data_int_status_reg_sd_clk};
            sd2wb_fifo_wr_en = ~sd2wb_fifo_full;
        end
        default: begin
            sd2wb_fifo_din = 40'd0;
            sd2wb_fifo_wr_en = 1'b0;
        end
    endcase
end


assign m_wb_cti_o = 3'b000;
assign m_wb_bte_o = 2'b00;

assign int_cmd =  |(cmd_int_status_reg_wb_clk & cmd_int_enable_reg_wb_clk);
assign int_data =  |(data_int_status_reg_wb_clk & data_int_enable_reg_wb_clk);

assign m_wb_sel_o = m_wb_cyc_o & m_wb_we_o ? wr_wbm_sel : 4'b1111;
assign m_wb_adr_o = {wbm_adr[31:2], 2'b00};

`ifdef ILA_SD

ila_0 ila_sd (
	.clk(sd_clk_o_pad), // input wire clk
	.probe0(sd_cmd_dat_i), // input wire [0:0]  probe0  
	.probe1(sd_cmd_out_o), // input wire [0:0]  probe1 
	.probe2(sd_cmd_oe_o), // input wire [0:0]  probe2 
	.probe3(sd_dat_dat_i), // input wire [3:0]  probe3 
	.probe4(sd_dat_out_o), // input wire [3:0]  probe4 
	.probe5(sd_dat_oe_o), // input wire [0:0]  probe5 
	.probe6(int_cmd), // input wire [0:0]  probe6 
	.probe7(int_data) // input wire [0:0]  probe7 
);

`endif
endmodule
