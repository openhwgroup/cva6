// ========== Copyright Header Begin ============================================
// Copyright (c) 2015 Princeton University
// All rights reserved.
//
// Redistribution and use in source and binary forms, with or without
// modification, are permitted provided that the following conditions are met:
//     * Redistributions of source code must retain the above copyright
//       notice, this list of conditions and the following disclaimer.
//     * Redistributions in binary form must reproduce the above copyright
//       notice, this list of conditions and the following disclaimer in the
//       documentation and/or other materials provided with the distribution.
//     * Neither the name of Princeton University nor the
//       names of its contributors may be used to endorse or promote products
//       derived from this software without specific prior written permission.
//
// THIS SOFTWARE IS PROVIDED BY PRINCETON UNIVERSITY "AS IS" AND
// ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
// WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
// DISCLAIMED. IN NO EVENT SHALL PRINCETON UNIVERSITY BE LIABLE FOR ANY
// DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
// (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
// LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
// ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
// (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
// SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
// ========== Copyright Header End ============================================

//==================================================================================================
//  Filename      : piton_sd_init.v
//  Created On    : 2017-03-10
//  Last Modified : 2017-06-17 23:08:59
//  Revision      :
//  Author        : Ang Li
//  Company       : Princeton University
//  Email         : angl@princeton.edu
//
//  Description   : Initialization module for the SD card controller. This
//                  module initializes the SD card controller, and also the SD
//                  card itself. After `init_done` signal asserted high, the
//                  controller/SD card is ready to operate at high-frequency
//                  4-bit mode.
//==================================================================================================

`include "sd_defines.h"
`include "piton_sd_define.vh"

module piton_sd_init (
    input   wire                    clk,
    input   wire                    rst,

    // Wishbone Master Channels
    output  wire    [31:0]          m_wb_dat_o,
    input   wire    [31:0]          m_wb_dat_i,
    output  wire    [7:0]           m_wb_adr_o,
    output  wire    [3:0]           m_wb_sel_o,
    output  wire                    m_wb_we_o,
    output  wire                    m_wb_cyc_o,
    output  wire                    m_wb_stb_o,
    input   wire                    m_wb_ack_i,

    // SD controller interrupt  engine
    input  wire                     sd_int_cmd,
    input  wire                     sd_int_data,

    // Initialization done signal
    output  wire                    init_done,
    output  reg                     is_hcxc     // output if the card is a SDHC/SDXC card
    );

    // ------ Common Local Parameters ------ //
    localparam  y   =   1'b1;
    localparam  n   =   1'b0;

    localparam  dat_no  =   2'h0;
    localparam  dat_rd  =   2'h1;
    localparam  dat_wr  =   2'h2;

    localparam  resp_no =   2'h0;
    localparam  resp_sh =   2'h1;   // wait for 48-bits response.
    localparam  resp_lg =   2'h2;   // wait for 136-bits response.

    localparam  TIME_WAIT_POWER_STABLE      =   24'd3_000_000;
    localparam  TIME_WAIT_ACMD41_REISSUE    =   24'd15_000_000;

    // ------ FSM States ------ //
    // Refer to "leon575777642.github.io/leon/hardware/MMC-SD-Hardware-Control/"
    localparam  ST_CI_EN_SW_RST     =   8'h0;
    localparam  ST_CI_DAT_TIMEOUT   =   8'h1;
    localparam  ST_CI_BUS_WIDTH     =   8'h2;
    localparam  ST_CI_CMD_TIMEOUT   =   8'h3;
    localparam  ST_CI_CMD_ISER      =   8'h4;
    localparam  ST_CI_DAT_ISER      =   8'h5;
    localparam  ST_CI_BLK_SIZE      =   8'h6;
    localparam  ST_CI_BLK_COUNT     =   8'h7;
    localparam  ST_CI_CLOCK_DIV     =   8'h8;
    localparam  ST_CI_DE_SW_RST     =   8'h9;
    localparam  ST_CI_WAIT_POWER    =   8'ha;

    localparam  ST_CMD0_CLR_CMD_ISR =   8'h10;
    localparam  ST_CMD0_WAIT_CLR    =   8'h11;
    localparam  ST_CMD0_CMD         =   8'h12;
    localparam  ST_CMD0_ARG         =   8'h13;
    localparam  ST_CMD0_WAIT_INT    =   8'h14;
    localparam  ST_CMD0_RD_CMD_ISR  =   8'h15;

    localparam  ST_CMD8_CLR_CMD_ISR =   8'h20;
    localparam  ST_CMD8_WAIT_CLR    =   8'h21;
    localparam  ST_CMD8_CMD         =   8'h22;
    localparam  ST_CMD8_ARG         =   8'h23;
    localparam  ST_CMD8_WAIT_INT    =   8'h24;
    localparam  ST_CMD8_RD_CMD_ISR  =   8'h25;
    localparam  ST_CMD8_RD_RESP0    =   8'h26;

    localparam  ST_ACMD41_CMD55_CLR_CMD_ISR =   8'h30;
    localparam  ST_ACMD41_CMD55_WAIT_CLR    =   8'h31;
    localparam  ST_ACMD41_CMD55_CMD         =   8'h32;
    localparam  ST_ACMD41_CMD55_ARG         =   8'h33;
    localparam  ST_ACMD41_CMD55_WAIT_INT    =   8'h34;
    localparam  ST_ACMD41_CMD55_RD_CMD_ISR  =   8'h35;
    localparam  ST_ACMD41_CMD55_RD_RESP0    =   8'h36;

    localparam  ST_ACMD41_CLR_CMD_ISR       =   8'h40;
    localparam  ST_ACMD41_WAIT_CLR          =   8'h41;
    localparam  ST_ACMD41_CMD               =   8'h42;
    localparam  ST_ACMD41_ARG               =   8'h43;
    localparam  ST_ACMD41_WAIT_INT          =   8'h44;
    localparam  ST_ACMD41_RD_CMD_ISR        =   8'h45;
    localparam  ST_ACMD41_RD_RESP0          =   8'h46;
    localparam  ST_ACMD41_WAIT_INTERVAL     =   8'h47;

    localparam  ST_CMD2_CLR_CMD_ISR =   8'h50;
    localparam  ST_CMD2_WAIT_CLR    =   8'h51;
    localparam  ST_CMD2_CMD         =   8'h52;
    localparam  ST_CMD2_ARG         =   8'h53;
    localparam  ST_CMD2_WAIT_INT    =   8'h54;
    localparam  ST_CMD2_RD_CMD_ISR  =   8'h55;

    localparam  ST_CMD3_CLR_CMD_ISR =   8'h60;
    localparam  ST_CMD3_WAIT_CLR    =   8'h61;
    localparam  ST_CMD3_CMD         =   8'h62;
    localparam  ST_CMD3_ARG         =   8'h63;
    localparam  ST_CMD3_WAIT_INT    =   8'h64;
    localparam  ST_CMD3_RD_CMD_ISR  =   8'h65;
    localparam  ST_CMD3_RD_RESP0    =   8'h66;

    localparam  ST_HS_EN_SW_RST     =   8'h70;
    localparam  ST_HS_CLOCK_DIV     =   8'h71;
    localparam  ST_HS_DE_SW_RST     =   8'h72;

    localparam  ST_CMD7_CLR_CMD_ISR =   8'h80;
    localparam  ST_CMD7_WAIT_CLR    =   8'h81;
    localparam  ST_CMD7_CMD         =   8'h82;
    localparam  ST_CMD7_ARG         =   8'h83;
    localparam  ST_CMD7_WAIT_INT    =   8'h84;
    localparam  ST_CMD7_RD_CMD_ISR  =   8'h85;
    localparam  ST_CMD7_RD_RESP0    =   8'h86;

    localparam  ST_ACMD6_CMD55_CLR_CMD_ISR  =   8'h90;
    localparam  ST_ACMD6_CMD55_WAIT_CLR     =   8'h91;
    localparam  ST_ACMD6_CMD55_CMD          =   8'h92;
    localparam  ST_ACMD6_CMD55_ARG          =   8'h93;
    localparam  ST_ACMD6_CMD55_WAIT_INT     =   8'h94;
    localparam  ST_ACMD6_CMD55_RD_CMD_ISR   =   8'h95;
    localparam  ST_ACMD6_CMD55_RD_RESP0     =   8'h96;

    localparam  ST_ACMD6_CLR_CMD_ISR        =   8'ha0;
    localparam  ST_ACMD6_WAIT_CLR           =   8'ha1;
    localparam  ST_ACMD6_CMD                =   8'ha2;
    localparam  ST_ACMD6_ARG                =   8'ha3;
    localparam  ST_ACMD6_WAIT_INT           =   8'ha4;
    localparam  ST_ACMD6_RD_CMD_ISR         =   8'ha5;
    localparam  ST_ACMD6_RD_RESP0           =   8'ha6;

    localparam  ST_FIN_CLR_CMD_ISR          =   8'hb0;
    localparam  ST_FIN_CLR_DAT_ISR          =   8'hb1;

    localparam  ST_INIT_DONE                =   8'hf0;
    localparam  ST_INIT_ERR                 =   8'hff;

    // ------ Signals Declaration ------ //
    reg [15:0]  rca;

    (* dont_touch="true" *) reg [7:0]   state;
    reg [7:0]   state_next;

    wire        counter_en;
    reg [23:0]  counter;

    reg         is_card_spec_v1;

    // compact FSM output
    reg [42:0]  fsm; // {adr, dat, we, stb, counter_en}

    // ------ Static Logic ------ //
    assign  init_done   =   state   ==  ST_INIT_DONE;
    assign  m_wb_adr_o  =   fsm[42:35];
    assign  m_wb_dat_o  =   fsm[34:3];
    assign  m_wb_we_o   =   fsm[2];
    assign  m_wb_stb_o  =   fsm[1];
    assign  m_wb_sel_o  =   4'hf;
    assign  m_wb_cyc_o  =   1'b1;
    assign  counter_en  =   fsm[0];

    // ------ Sequential Logic ------ //
    always @(posedge clk or posedge rst) begin  //{{{
        if (rst) begin
            rca             <=  32'h0;
            state           <=  ST_CI_EN_SW_RST;
            counter         <=  24'd0;
            is_card_spec_v1 <=  1'b0;
            is_hcxc         <=  1'b0;
        end
        else begin
            state   <=  state_next;

            if (state   ==  ST_CMD3_RD_RESP0 && m_wb_ack_i) begin
                rca         <=  m_wb_dat_i[31:16];
            end

            if (state   ==  ST_CMD8_RD_CMD_ISR && m_wb_ack_i) begin
                if (m_wb_dat_i[`INT_CMD_CTE]) begin
                    is_card_spec_v1 <=  1'b1;
                end
            end
            else if (state   ==  ST_CMD8_RD_RESP0 && m_wb_ack_i) begin
                if (m_wb_dat_i[11:0] == 12'h15a) begin
                    is_card_spec_v1 <=  1'b0;
                end
                else begin
                    is_card_spec_v1 <=  1'b1;
                end
            end

            if (state == ST_ACMD41_RD_RESP0 && m_wb_ack_i) begin
                if (~is_card_spec_v1 && m_wb_dat_i[30]) begin
                    is_hcxc         <=  1'b1;
                end
                else begin
                    is_hcxc         <=  1'b0;
                end
            end

            if (counter_en) begin
                counter     <=  counter + 1;
            end
            else begin
                counter     <=  24'd0;
            end
        end
    end //}}}

    // ------ FSM Transition ------ //
    always @* begin //{{{
        state_next  =   state;

        case (state)
            // Core Initialization
            ST_CI_EN_SW_RST: begin
                if (m_wb_ack_i) state_next  =   ST_CI_DAT_TIMEOUT;
            end
            ST_CI_DAT_TIMEOUT: begin
                if (m_wb_ack_i) state_next  =   ST_CI_BUS_WIDTH;
            end
            ST_CI_BUS_WIDTH: begin
                if (m_wb_ack_i) state_next  =   ST_CI_CMD_TIMEOUT;
            end
            ST_CI_CMD_TIMEOUT: begin
                if (m_wb_ack_i) state_next  =   ST_CI_CMD_ISER;
            end
            ST_CI_CMD_ISER: begin
                if (m_wb_ack_i) state_next  =   ST_CI_DAT_ISER;
            end
            ST_CI_DAT_ISER: begin
                if (m_wb_ack_i) state_next  =   ST_CI_BLK_SIZE;
            end
            ST_CI_BLK_SIZE: begin
                if (m_wb_ack_i) state_next  =   ST_CI_BLK_COUNT;
            end
            ST_CI_BLK_COUNT: begin
                if (m_wb_ack_i) state_next  =   ST_CI_CLOCK_DIV;
            end
            ST_CI_CLOCK_DIV: begin
                if (m_wb_ack_i) state_next  =   ST_CI_DE_SW_RST;
            end
            ST_CI_DE_SW_RST: begin
                if (m_wb_ack_i) state_next  =   ST_CI_WAIT_POWER;
            end
            ST_CI_WAIT_POWER: begin
                if (counter == TIME_WAIT_POWER_STABLE) begin
                    state_next  =   ST_CMD0_CLR_CMD_ISR;
                end
            end
            // Sending CMD0
            ST_CMD0_CLR_CMD_ISR: begin
                if (m_wb_ack_i) state_next  =   ST_CMD0_WAIT_CLR;
            end
            ST_CMD0_WAIT_CLR: begin
                if (~sd_int_cmd) state_next =   ST_CMD0_CMD;
            end
            ST_CMD0_CMD: begin
                if (m_wb_ack_i) state_next  =   ST_CMD0_ARG;
            end
            ST_CMD0_ARG: begin
                if (m_wb_ack_i) state_next  =   ST_CMD0_WAIT_INT;
            end
            ST_CMD0_WAIT_INT: begin
                if (sd_int_cmd) state_next  =   ST_CMD0_RD_CMD_ISR;
            end
            ST_CMD0_RD_CMD_ISR: begin
                if (m_wb_ack_i) begin
                    if (m_wb_dat_i[`INT_CMD_CC]) begin
                        state_next  =   ST_CMD8_CLR_CMD_ISR;
                    end
                    else begin
                        state_next  =   ST_CMD0_CLR_CMD_ISR;
                    end
                end
            end
            ST_CMD8_CLR_CMD_ISR: begin
                if (m_wb_ack_i) state_next  =   ST_CMD8_WAIT_CLR;
            end
            ST_CMD8_WAIT_CLR: begin
                if (~sd_int_cmd) state_next =   ST_CMD8_CMD;
            end
            ST_CMD8_CMD: begin
                if (m_wb_ack_i) state_next  =   ST_CMD8_ARG;
            end
            ST_CMD8_ARG: begin
                if (m_wb_ack_i) state_next  =   ST_CMD8_WAIT_INT;
            end
            ST_CMD8_WAIT_INT: begin
                if (sd_int_cmd) state_next  =   ST_CMD8_RD_CMD_ISR;
            end
            ST_CMD8_RD_CMD_ISR: begin
                if (m_wb_ack_i) begin
                    if (m_wb_dat_i[`INT_CMD_CC]) begin
                        // Success.
                        state_next  =   ST_CMD8_RD_RESP0;
                    end
                    else if (m_wb_dat_i[`INT_CMD_CTE]) begin
                        // Timeout. Suppose card spec v1.
                        state_next  =   ST_ACMD41_CMD55_CLR_CMD_ISR;
                    end
                    else begin
                        // Failed.
                        state_next  =   ST_CMD8_CLR_CMD_ISR;
                    end
                end
            end
            ST_CMD8_RD_RESP0: begin
                if (m_wb_ack_i) begin
                    if (m_wb_dat_i[11:0] ==  12'h15a) begin
                        state_next  =   ST_ACMD41_CMD55_CLR_CMD_ISR;
                    end
                    else begin
                        state_next  =   ST_CMD8_CLR_CMD_ISR;
                    end
                end
            end
            // Sending pre-ACMD41 CMD55
            ST_ACMD41_CMD55_CLR_CMD_ISR: begin
                if (m_wb_ack_i) state_next  =   ST_ACMD41_CMD55_WAIT_CLR;
            end
            ST_ACMD41_CMD55_WAIT_CLR: begin
                if (~sd_int_cmd) state_next =   ST_ACMD41_CMD55_CMD;
            end
            ST_ACMD41_CMD55_CMD: begin
                if (m_wb_ack_i) state_next  =   ST_ACMD41_CMD55_ARG;
            end
            ST_ACMD41_CMD55_ARG: begin
                if (m_wb_ack_i) state_next  =   ST_ACMD41_CMD55_WAIT_INT;
            end
            ST_ACMD41_CMD55_WAIT_INT: begin
                if (sd_int_cmd) state_next  =   ST_ACMD41_CMD55_RD_CMD_ISR;
            end
            ST_ACMD41_CMD55_RD_CMD_ISR: begin
                if (m_wb_ack_i) begin
                    if (m_wb_dat_i[`INT_CMD_CC]) begin
                        state_next  =   ST_ACMD41_CMD55_RD_RESP0;
                    end
                    else begin
                        state_next  =   ST_ACMD41_CMD55_CLR_CMD_ISR;
                    end
                end
            end
            ST_ACMD41_CMD55_RD_RESP0: begin
                if (m_wb_ack_i) begin
                    if (~(|m_wb_dat_i[31:19]) & ~(|m_wb_dat_i[16:13]) & m_wb_dat_i[5]) begin
                        state_next  =   ST_ACMD41_CLR_CMD_ISR;
                    end
                    else begin
                        state_next  =   ST_ACMD41_CMD55_CLR_CMD_ISR;
                    end
                end
            end
            // Sending ACMD41
            ST_ACMD41_CLR_CMD_ISR: begin
                if (m_wb_ack_i) state_next  =   ST_ACMD41_WAIT_CLR;
            end
            ST_ACMD41_WAIT_CLR: begin
                if (~sd_int_cmd) state_next =   ST_ACMD41_CMD;
            end
            ST_ACMD41_CMD: begin
                if (m_wb_ack_i) state_next  =   ST_ACMD41_ARG;
            end
            ST_ACMD41_ARG: begin
                if (m_wb_ack_i) state_next  =   ST_ACMD41_WAIT_INT;
            end
            ST_ACMD41_WAIT_INT: begin
                if (sd_int_cmd) state_next  =   ST_ACMD41_RD_CMD_ISR;
            end
            ST_ACMD41_RD_CMD_ISR: begin
                if (m_wb_ack_i) begin
                    if (m_wb_dat_i[`INT_CMD_CC]) begin
                        state_next  =   ST_ACMD41_RD_RESP0;
                    end
                    else begin
                        state_next  =   ST_ACMD41_WAIT_INTERVAL;
                    end
                end
            end
            ST_ACMD41_RD_RESP0: begin
                if (m_wb_ack_i) begin
                    if (m_wb_dat_i[31] & (|m_wb_dat_i[21:20])) begin
                        state_next  =   ST_CMD2_CLR_CMD_ISR;
                    end
                    else begin
                        state_next  =   ST_ACMD41_WAIT_INTERVAL;
                    end
                end
            end
            ST_ACMD41_WAIT_INTERVAL: begin
                if (counter == TIME_WAIT_ACMD41_REISSUE) begin
                    state_next  =   ST_ACMD41_CMD55_CLR_CMD_ISR;
                end
            end
            // Sending CMD2
            ST_CMD2_CLR_CMD_ISR: begin
                if (m_wb_ack_i) state_next  =   ST_CMD2_WAIT_CLR;
            end
            ST_CMD2_WAIT_CLR: begin
                if (~sd_int_cmd) state_next =   ST_CMD2_CMD;
            end
            ST_CMD2_CMD: begin
                if (m_wb_ack_i) state_next  =   ST_CMD2_ARG;
            end
            ST_CMD2_ARG: begin
                if (m_wb_ack_i) state_next  =   ST_CMD2_WAIT_INT;
            end
            ST_CMD2_WAIT_INT: begin
                if (sd_int_cmd) state_next  =   ST_CMD2_RD_CMD_ISR;
            end
            ST_CMD2_RD_CMD_ISR: begin
                if (m_wb_ack_i) begin
                    if (m_wb_dat_i[`INT_CMD_CC]) begin
                        state_next  =   ST_CMD3_CLR_CMD_ISR;
                    end
                    else begin
                        state_next  =   ST_CMD2_CLR_CMD_ISR;
                    end
                end
            end
            // Sending CMD3
            ST_CMD3_CLR_CMD_ISR: begin
                if (m_wb_ack_i) state_next  =   ST_CMD3_WAIT_CLR;
            end
            ST_CMD3_WAIT_CLR: begin
                if (~sd_int_cmd) state_next =   ST_CMD3_CMD;
            end
            ST_CMD3_CMD: begin
                if (m_wb_ack_i) state_next  =   ST_CMD3_ARG;
            end
            ST_CMD3_ARG: begin
                if (m_wb_ack_i) state_next  =   ST_CMD3_WAIT_INT;
            end
            ST_CMD3_WAIT_INT: begin
                if (sd_int_cmd) state_next  =   ST_CMD3_RD_CMD_ISR;
            end
            ST_CMD3_RD_CMD_ISR: begin
                if (m_wb_ack_i) begin
                    if (m_wb_dat_i[`INT_CMD_CC]) begin
                        state_next  =   ST_CMD3_RD_RESP0;
                    end
                    else begin
                        state_next  =   ST_CMD3_CLR_CMD_ISR;
                    end
                end
            end
            ST_CMD3_RD_RESP0: begin
                if (m_wb_ack_i) begin
                    if (~(|m_wb_dat_i[15:13])) begin
                        state_next  =   ST_HS_EN_SW_RST;
                    end
                    else begin
                        state_next  =   ST_CMD3_CLR_CMD_ISR;
                    end
                end
            end
            // Changing clock speed
            ST_HS_EN_SW_RST: begin
                if (m_wb_ack_i) state_next  =   ST_HS_CLOCK_DIV;
            end
            ST_HS_CLOCK_DIV: begin
                if (m_wb_ack_i) state_next  =   ST_HS_DE_SW_RST;
            end
            ST_HS_DE_SW_RST: begin
                if (m_wb_ack_i) state_next  =   ST_CMD7_CLR_CMD_ISR;
            end
            // Sending CMD7
            ST_CMD7_CLR_CMD_ISR: begin
                if (m_wb_ack_i) state_next  =   ST_CMD7_WAIT_CLR;
            end
            ST_CMD7_WAIT_CLR: begin
                if (~sd_int_cmd) state_next =   ST_CMD7_CMD;
            end
            ST_CMD7_CMD: begin
                if (m_wb_ack_i) state_next  =   ST_CMD7_ARG;
            end
            ST_CMD7_ARG: begin
                if (m_wb_ack_i) state_next  =   ST_CMD7_WAIT_INT;
            end
            ST_CMD7_WAIT_INT: begin
                if (sd_int_cmd) state_next  =   ST_CMD7_RD_CMD_ISR;
            end
            ST_CMD7_RD_CMD_ISR: begin
                if (m_wb_ack_i) begin
                    if (m_wb_dat_i[`INT_CMD_CC]) begin
                        state_next  =   ST_CMD7_RD_RESP0;
                    end
                    else begin
                        state_next  =   ST_CMD7_CLR_CMD_ISR;
                    end
                end
            end
            ST_CMD7_RD_RESP0: begin
                if (m_wb_ack_i) begin
                    if (~(|m_wb_dat_i[31:19]) & ~(|m_wb_dat_i[16:13])) begin
                        state_next  =   ST_ACMD6_CMD55_CLR_CMD_ISR;
                    end
                    else begin
                        state_next  =   ST_CMD7_CLR_CMD_ISR;
                    end
                end
            end
            // Sending pre-ACMD6 CMD55
            ST_ACMD6_CMD55_CLR_CMD_ISR: begin
                if (m_wb_ack_i) state_next  =   ST_ACMD6_CMD55_WAIT_CLR;
            end
            ST_ACMD6_CMD55_WAIT_CLR: begin
                if (~sd_int_cmd) state_next =   ST_ACMD6_CMD55_CMD;
            end
            ST_ACMD6_CMD55_CMD: begin
                if (m_wb_ack_i) state_next  =   ST_ACMD6_CMD55_ARG;
            end
            ST_ACMD6_CMD55_ARG: begin
                if (m_wb_ack_i) state_next  =   ST_ACMD6_CMD55_WAIT_INT;
            end
            ST_ACMD6_CMD55_WAIT_INT: begin
                if (sd_int_cmd) state_next  =   ST_ACMD6_CMD55_RD_CMD_ISR;
            end
            ST_ACMD6_CMD55_RD_CMD_ISR: begin
                if (m_wb_ack_i) begin
                    if (m_wb_dat_i[`INT_CMD_CC]) begin
                        state_next  =   ST_ACMD6_CMD55_RD_RESP0;
                    end
                    else begin
                        state_next  =   ST_ACMD6_CMD55_CLR_CMD_ISR;
                    end
                end
            end
            ST_ACMD6_CMD55_RD_RESP0: begin
                if (m_wb_ack_i) begin
                    if (~(|m_wb_dat_i[31:19]) & ~(|m_wb_dat_i[16:13]) & m_wb_dat_i[5]) begin
                        state_next  =   ST_ACMD6_CLR_CMD_ISR;
                    end
                    else begin
                        state_next  =   ST_ACMD6_CMD55_CLR_CMD_ISR;
                    end
                end
            end
            // Sending ACMD6
            ST_ACMD6_CLR_CMD_ISR: begin
                if (m_wb_ack_i) state_next  =   ST_ACMD6_WAIT_CLR;
            end
            ST_ACMD6_WAIT_CLR: begin
                if (~sd_int_cmd) state_next =   ST_ACMD6_CMD;
            end
            ST_ACMD6_CMD: begin
                if (m_wb_ack_i) state_next  =   ST_ACMD6_ARG;
            end
            ST_ACMD6_ARG: begin
                if (m_wb_ack_i) state_next  =   ST_ACMD6_WAIT_INT;
            end
            ST_ACMD6_WAIT_INT: begin
                if (sd_int_cmd) state_next  =   ST_ACMD6_RD_CMD_ISR;
            end
            ST_ACMD6_RD_CMD_ISR: begin
                if (m_wb_ack_i) begin
                    if (m_wb_dat_i[`INT_CMD_CC]) begin
                        state_next  =   ST_ACMD6_RD_RESP0;
                    end
                    else begin
                        state_next  =   ST_ACMD6_CMD55_CLR_CMD_ISR;
                    end
                end
            end
            ST_ACMD6_RD_RESP0: begin
                if (m_wb_ack_i) begin
                    if (~(|m_wb_dat_i[31:19]) & ~(|m_wb_dat_i[16:13])) begin
                        state_next  =   ST_FIN_CLR_CMD_ISR;
                    end
                    else begin
                        state_next  =   ST_ACMD6_CMD55_CLR_CMD_ISR;
                    end
                end
            end
            ST_FIN_CLR_CMD_ISR: begin
                if (m_wb_ack_i) state_next  =   ST_FIN_CLR_DAT_ISR;
            end
            ST_FIN_CLR_DAT_ISR: begin
                if (m_wb_ack_i) state_next  =   ST_INIT_DONE;
            end
            ST_INIT_DONE: begin
                state_next  =   ST_INIT_DONE;
            end
            default: begin
                state_next  =   ST_CI_EN_SW_RST;
            end
        endcase
    end //}}}

    // ------ FSM Output ------ //
    always @* begin //{{{
        //  state                               register adr,   data,                                                   we, stb, counter_en
        case (state)
            ST_CI_EN_SW_RST,
            ST_HS_EN_SW_RST:            fsm = {`reset,          32'h1,                                                  y,  y,      n};
            ST_CI_DAT_TIMEOUT:          fsm = {`data_timeout,   32'd10_000_000,                                         y,  y,      n};
            ST_CI_BUS_WIDTH:            fsm = {`controller,     32'h1,                                                  y,  y,      n};
            ST_CI_CMD_TIMEOUT:          fsm = {`cmd_timeout,    32'd20_000,                                             y,  y,      n};
            ST_CI_CMD_ISER:             fsm = {`cmd_iser,       32'h1f,                                                 y,  y,      n};
            ST_CI_DAT_ISER:             fsm = {`data_iser,      32'h1f,                                                 y,  y,      n};
            ST_CI_BLK_SIZE:             fsm = {`blksize,        32'd511,                                                y,  y,      n};
            ST_CI_BLK_COUNT:            fsm = {`blkcnt,         32'b0,                                                  y,  y,      n};
            ST_CI_CLOCK_DIV:            fsm = {`clock_d,        32'd99,                                                 y,  y,      n};
            ST_CI_WAIT_POWER:           fsm = {8'bx,            32'bx,                                                  n,  n,      y};
            ST_CI_DE_SW_RST,
            ST_HS_DE_SW_RST:            fsm = {`reset,          32'h0,                                                  y,  y,      n};
            ST_ACMD41_WAIT_INTERVAL:    fsm = {8'bx,            32'bx,                                                  n,  n,      y};
            ST_HS_CLOCK_DIV:            fsm = {`clock_d,        32'd0,                                                  y,  y,      n};
            // Argument
            ST_CMD0_ARG:                fsm = {`argument,       32'b0,                                                  y,  y,      n};
            ST_CMD8_ARG:                fsm = {`argument,       20'b0, 4'h1, 8'h5a,                                     y,  y,      n};
            ST_ACMD41_CMD55_ARG:        fsm = {`argument,       32'b0,                                                  y,  y,      n};
            ST_ACMD41_ARG:              fsm = {`argument,       1'b0, ~is_card_spec_v1, 1'b0, y, 3'b0, n, 24'h300_000,  y,  y,      n};
            ST_CMD2_ARG:                fsm = {`argument,       32'b0,                                                  y,  y,      n};
            ST_CMD3_ARG:                fsm = {`argument,       32'b0,                                                  y,  y,      n};
            ST_CMD7_ARG:                fsm = {`argument,       rca, 16'b0,                                             y,  y,      n};
            ST_ACMD6_CMD55_ARG:         fsm = {`argument,       rca, 16'b0,                                             y,  y,      n};
            ST_ACMD6_ARG:               fsm = {`argument,       30'b0, 2'h2,                                            y,  y,      n};
            // Command:                                         RESV   CMD    RESV  DATA    IDX CRC BUSY RESP
            //                                                         INDEX                CHK CHK CHK  FMT
            ST_CMD0_CMD:                fsm = {`command,        18'b0, 6'd0,  1'b0, dat_no, n,  n,  n,   resp_no,       y,  y,      n};
            ST_CMD8_CMD:                fsm = {`command,        18'b0, 6'd8,  1'b0, dat_no, y,  y,  n,   resp_sh,       y,  y,      n};
            ST_ACMD41_CMD55_CMD:        fsm = {`command,        18'b0, 6'd55, 1'b0, dat_no, y,  y,  n,   resp_sh,       y,  y,      n};
            ST_ACMD41_CMD:              fsm = {`command,        18'b0, 6'd41, 1'b0, dat_no, n,  y,  n,   resp_sh,       y,  y,      n};
            ST_CMD2_CMD:                fsm = {`command,        18'b0, 6'd2,  1'b0, dat_no, n,  y,  n,   resp_lg,       y,  y,      n};
            ST_CMD3_CMD:                fsm = {`command,        18'b0, 6'd3,  1'b0, dat_no, y,  y,  n,   resp_sh,       y,  y,      n};
            ST_CMD7_CMD:                fsm = {`command,        18'b0, 6'd7,  1'b0, dat_no, y,  y,  y,   resp_sh,       y,  y,      n};
            ST_ACMD6_CMD55_CMD:         fsm = {`command,        18'b0, 6'd55, 1'b0, dat_no, y,  y,  n,   resp_sh,       y,  y,      n};
            ST_ACMD6_CMD:               fsm = {`command,        18'b0, 6'd6,  1'b0, dat_no, n,  y,  n,   resp_sh,       y,  y,      n};
            // Clear command event flags
            ST_CMD0_CLR_CMD_ISR,
            ST_CMD8_CLR_CMD_ISR,
            ST_ACMD41_CMD55_CLR_CMD_ISR,
            ST_ACMD41_CLR_CMD_ISR,
            ST_CMD2_CLR_CMD_ISR,
            ST_CMD3_CLR_CMD_ISR,
            ST_CMD7_CLR_CMD_ISR,
            ST_ACMD6_CMD55_CLR_CMD_ISR,
            ST_ACMD6_CLR_CMD_ISR,
            ST_FIN_CLR_CMD_ISR:         fsm = {`cmd_isr,        32'b0,                                                  y,  y,      n};
            // Clear data event flags
            ST_FIN_CLR_DAT_ISR:         fsm = {`data_isr,       32'b0,                                                  y,  y,      n};
            // Wait for command event interruption signal to be unset
            ST_CMD0_WAIT_CLR,
            ST_CMD8_WAIT_CLR,
            ST_ACMD41_CMD55_WAIT_CLR,
            ST_ACMD41_WAIT_CLR,
            ST_CMD2_WAIT_CLR,
            ST_CMD3_WAIT_CLR,
            ST_CMD7_WAIT_CLR,
            ST_ACMD6_CMD55_WAIT_CLR,
            ST_ACMD6_WAIT_CLR:          fsm = {8'bx,            32'bx,                                                  n,  n,      n};
            // Wait for completion interrupt
            ST_CMD0_WAIT_INT,
            ST_CMD8_WAIT_INT,
            ST_ACMD41_CMD55_WAIT_INT,
            ST_ACMD41_WAIT_INT,
            ST_CMD2_WAIT_INT,
            ST_CMD3_WAIT_INT,
            ST_CMD7_WAIT_INT,
            ST_ACMD6_CMD55_WAIT_INT,
            ST_ACMD6_WAIT_INT:          fsm = {8'bx,            32'bx,                                                  n,  n,      n};
            // Read command event flags
            ST_CMD0_RD_CMD_ISR,
            ST_CMD8_RD_CMD_ISR,
            ST_ACMD41_CMD55_RD_CMD_ISR,
            ST_ACMD41_RD_CMD_ISR,
            ST_CMD2_RD_CMD_ISR,
            ST_CMD3_RD_CMD_ISR,
            ST_CMD7_RD_CMD_ISR,
            ST_ACMD6_CMD55_RD_CMD_ISR,
            ST_ACMD6_RD_CMD_ISR:        fsm = {`cmd_isr,        32'bx,                                                  n,  y,      n};
            // Read response register 0
            ST_CMD8_RD_RESP0,
            ST_ACMD41_CMD55_RD_RESP0,
            ST_ACMD41_RD_RESP0,
            ST_CMD3_RD_RESP0,
            ST_CMD7_RD_RESP0,
            ST_ACMD6_CMD55_RD_RESP0,
            ST_ACMD6_RD_RESP0:          fsm = {`resp0,          32'bx,                                                  n,  y,      n};
            // Default
            default:                    fsm = {8'bx,            32'bx,                                                  n,  n,      n};
        endcase
    end //}}}

endmodule
