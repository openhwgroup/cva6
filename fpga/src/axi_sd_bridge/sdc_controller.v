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
output int_cmd, int_data;

//SD clock
wire sd_clk_o; //Sd_clk used in the system
wire [3:0] wr_wbm_sel;
wire [`BLKSIZE_W+`BLKCNT_W-1:0] xfersize;
wire [31:0] wbm_adr;

wire go_idle;
wire cmd_start_wb_clk;
wire cmd_start_sd_clk;
wire cmd_start;
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
wire start_tx_fifo;
wire start_rx_fifo;
wire tx_fifo_empty;
wire tx_fifo_full;
wire rx_fifo_full;
wire sd_data_busy;
wire data_busy;
wire data_crc_ok;
wire rd_fifo;
wire we_fifo;

wire data_start_rx;
wire data_start_tx;
wire cmd_int_rst_wb_clk;
wire cmd_int_rst_sd_clk;
wire cmd_int_rst;
wire data_int_rst_wb_clk;
wire data_int_rst_sd_clk;
wire data_int_rst;

//wb accessible registers
wire [31:0] argument_reg_wb_clk;
wire [`CMD_REG_SIZE-1:0] command_reg_wb_clk;
wire [`CMD_TIMEOUT_W-1:0] cmd_timeout_reg_wb_clk;
wire [`DATA_TIMEOUT_W-1:0] data_timeout_reg_wb_clk;
wire [0:0] software_reset_reg_wb_clk;
wire [31:0] response_0_reg_wb_clk;
wire [31:0] response_1_reg_wb_clk;
wire [31:0] response_2_reg_wb_clk;
wire [31:0] response_3_reg_wb_clk;
wire [`BLKSIZE_W-1:0] block_size_reg_wb_clk;
wire [0:0] controll_setting_reg_wb_clk;
wire [`INT_CMD_SIZE-1:0] cmd_int_status_reg_wb_clk;
wire [`INT_DATA_SIZE-1:0] data_int_status_reg_wb_clk;
wire [`INT_CMD_SIZE-1:0] cmd_int_enable_reg_wb_clk;
wire [`INT_DATA_SIZE-1:0] data_int_enable_reg_wb_clk;
wire [`BLKCNT_W-1:0] block_count_reg_wb_clk;
wire [31:0] dma_addr_reg_wb_clk;
wire [7:0] clock_divider_reg_wb_clk;

wire [31:0] argument_reg_sd_clk;
wire [`CMD_REG_SIZE-1:0] command_reg_sd_clk;
wire [`CMD_TIMEOUT_W-1:0] cmd_timeout_reg_sd_clk;
wire [`DATA_TIMEOUT_W-1:0] data_timeout_reg_sd_clk;
wire [0:0] software_reset_reg_sd_clk;
wire [31:0] response_0_reg_sd_clk;
wire [31:0] response_1_reg_sd_clk;
wire [31:0] response_2_reg_sd_clk;
wire [31:0] response_3_reg_sd_clk;
wire [`BLKSIZE_W-1:0] block_size_reg_sd_clk;
wire [0:0] controll_setting_reg_sd_clk;
wire [`INT_CMD_SIZE-1:0] cmd_int_status_reg_sd_clk;
wire [`INT_DATA_SIZE-1:0] data_int_status_reg_sd_clk;
wire [`BLKCNT_W-1:0] block_count_reg_sd_clk;
wire [1:0] dma_addr_reg_sd_clk;
wire [7:0] clock_divider_reg_sd_clk;

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
    .start_tx_fifo_o  (start_tx_fifo),
    .start_rx_fifo_o  (start_rx_fifo),
    .tx_fifo_empty_i  (tx_fifo_empty),
    .tx_fifo_full_i   (tx_fifo_full),
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
    .en_rx_i   (start_rx_fifo),
    .en_tx_i   (start_tx_fifo),
    .adr_i     (dma_addr_reg_wb_clk),
    .sd_clk    (sd_clk_o),
    .dat_i     (data_in_rx_fifo),
    .dat_o     (data_out_tx_fifo),
    .wr_i      (we_fifo),
    .rd_i      (rd_fifo),
    .sd_empty_o   (tx_fifo_empty),
    .sd_full_o   (rx_fifo_full),
    .wb_empty_o   (),
    .wb_full_o    (tx_fifo_full)
    );

assign xfersize = (block_size_reg_wb_clk + 1'b1) * (block_count_reg_wb_clk + 1'b1);
sd_wb_sel_ctrl sd_wb_sel_ctrl0(
        .wb_clk         (wb_clk_i),
        .rst            (wb_rst_i | software_reset_reg_sd_clk[0]),
        .ena            (start_rx_fifo),
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
    .cmd_start                      (cmd_start),
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
    .data_int_enable_reg            (data_int_enable_reg_wb_clk)
    );

//clock domain crossing regiters
//assign cmd_start_sd_clk = cmd_start_wb_clk;
//assign data_int_rst_sd_clk = data_int_rst_wb_clk;
//assign cmd_int_rst_sd_clk = cmd_int_rst_wb_clk;
//assign argument_reg_sd_clk = argument_reg_wb_clk;
//assign command_reg_sd_clk = command_reg_wb_clk;
//assign response_0_reg_wb_clk = response_0_reg_sd_clk;
//assign response_1_reg_wb_clk = response_1_reg_sd_clk;
//assign response_2_reg_wb_clk = response_2_reg_sd_clk;
//assign response_3_reg_wb_clk = response_3_reg_sd_clk;
//assign software_reset_reg_sd_clk = software_reset_reg_wb_clk;
//assign timeout_reg_sd_clk = timeout_reg_wb_clk;
//assign block_size_reg_sd_clk = block_size_reg_wb_clk;
//assign controll_setting_reg_sd_clk = controll_setting_reg_wb_clk;
//assign cmd_int_status_reg_wb_clk = cmd_int_status_reg_sd_clk;
//assign clock_divider_reg_sd_clk = clock_divider_reg_wb_clk;
//assign block_count_reg_sd_clk = block_count_reg_wb_clk;
//assign dma_addr_reg_sd_clk = dma_addr_reg_wb_clk;
//assign data_int_status_reg_wb_clk = data_int_status_reg_sd_clk;

edge_detect_oc cmd_start_edge(.rst(wb_rst_i), .clk(wb_clk_i), .sig(cmd_start), .rise(cmd_start_wb_clk), .fall());
edge_detect_oc data_int_rst_edge(.rst(wb_rst_i), .clk(wb_clk_i), .sig(data_int_rst), .rise(data_int_rst_wb_clk), .fall());
edge_detect_oc cmd_int_rst_edge(.rst(wb_rst_i), .clk(wb_clk_i), .sig(cmd_int_rst), .rise(cmd_int_rst_wb_clk), .fall());
monostable_domain_cross cmd_start_cross(wb_rst_i, wb_clk_i, cmd_start_wb_clk, sd_clk_o, cmd_start_sd_clk);
monostable_domain_cross data_int_rst_cross(wb_rst_i, wb_clk_i, data_int_rst_wb_clk, sd_clk_o, data_int_rst_sd_clk);
monostable_domain_cross cmd_int_rst_cross(wb_rst_i, wb_clk_i, cmd_int_rst_wb_clk, sd_clk_o, cmd_int_rst_sd_clk);
bistable_domain_cross #(32) argument_reg_cross(wb_rst_i, wb_clk_i, argument_reg_wb_clk, sd_clk_o, argument_reg_sd_clk);
bistable_domain_cross #(`CMD_REG_SIZE) command_reg_cross(wb_rst_i, wb_clk_i, command_reg_wb_clk, sd_clk_o, command_reg_sd_clk);
bistable_domain_cross #(32) response_0_reg_cross(wb_rst_i, sd_clk_o, response_0_reg_sd_clk, wb_clk_i, response_0_reg_wb_clk);
bistable_domain_cross #(32) response_1_reg_cross(wb_rst_i, sd_clk_o, response_1_reg_sd_clk, wb_clk_i, response_1_reg_wb_clk);
bistable_domain_cross #(32) response_2_reg_cross(wb_rst_i, sd_clk_o, response_2_reg_sd_clk, wb_clk_i, response_2_reg_wb_clk);
bistable_domain_cross #(32) response_3_reg_cross(wb_rst_i, sd_clk_o, response_3_reg_sd_clk, wb_clk_i, response_3_reg_wb_clk);
bistable_domain_cross software_reset_reg_cross(wb_rst_i, wb_clk_i, software_reset_reg_wb_clk, sd_clk_o, software_reset_reg_sd_clk);
bistable_domain_cross #(`CMD_TIMEOUT_W) cmd_timeout_reg_cross(wb_rst_i, wb_clk_i, cmd_timeout_reg_wb_clk, sd_clk_o, cmd_timeout_reg_sd_clk);
bistable_domain_cross #(`DATA_TIMEOUT_W) data_timeout_reg_cross(wb_rst_i, wb_clk_i, data_timeout_reg_wb_clk, sd_clk_o, data_timeout_reg_sd_clk);
bistable_domain_cross #(`BLKSIZE_W) block_size_reg_cross(wb_rst_i, wb_clk_i, block_size_reg_wb_clk, sd_clk_o, block_size_reg_sd_clk);
bistable_domain_cross #(1) controll_setting_reg_cross(wb_rst_i, wb_clk_i, controll_setting_reg_wb_clk, sd_clk_o, controll_setting_reg_sd_clk);
bistable_domain_cross #(`INT_CMD_SIZE) cmd_int_status_reg_cross(wb_rst_i, sd_clk_o, cmd_int_status_reg_sd_clk, wb_clk_i, cmd_int_status_reg_wb_clk);
bistable_domain_cross #(8) clock_divider_reg_cross(wb_rst_i, wb_clk_i, clock_divider_reg_wb_clk, sd_clk_i_pad, clock_divider_reg_sd_clk);
bistable_domain_cross #(`BLKCNT_W) block_count_reg_cross(wb_rst_i, wb_clk_i, block_count_reg_wb_clk, sd_clk_o, block_count_reg_sd_clk);
bistable_domain_cross #(2) dma_addr_reg_cross(wb_rst_i, wb_clk_i, dma_addr_reg_wb_clk[1:0], sd_clk_o, dma_addr_reg_sd_clk);
bistable_domain_cross #(`INT_DATA_SIZE) data_int_status_reg_cross(wb_rst_i, sd_clk_o, data_int_status_reg_sd_clk, wb_clk_i, data_int_status_reg_wb_clk);

assign m_wb_cti_o = 3'b000;
assign m_wb_bte_o = 2'b00;

assign int_cmd =  |(cmd_int_status_reg_wb_clk & cmd_int_enable_reg_wb_clk);
assign int_data =  |(data_int_status_reg_wb_clk & data_int_enable_reg_wb_clk);

assign m_wb_sel_o = m_wb_cyc_o & m_wb_we_o ? wr_wbm_sel : 4'b1111;
assign m_wb_adr_o = {wbm_adr[31:2], 2'b00};

endmodule
