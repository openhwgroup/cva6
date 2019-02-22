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
//  Filename      : piton_sd_top.v
//  Created On    : 2017-05-23
//  Last Modified : 2017-07-26 11:40:38
//  Revision      :
//  Author        : Ang Li
//  Company       : Princeton University
//  Email         : angl@princeton.edu
//
//  Description   : Top level entity of the 4bit SD Reader.
//==================================================================================================
`include "piton_sd_define.vh"

module piton_sd_top (
    // Clock and reset
    input  wire                             sys_clk,
    input  wire                             sd_clk,
    input  wire                             sys_rst,

    // NOC interface
    input  wire                             splitter_sd_val,
    input  wire [`ARIANE_DATA_WIDTH-1:0]    splitter_sd_data,
    output wire                             sd_splitter_rdy,

    output wire                             sd_splitter_val,
    output wire [`ARIANE_DATA_WIDTH-1:0]    sd_splitter_data,
    input  wire                             splitter_sd_rdy,

    // SD interface
    input  wire                             sd_cd,
    output wire                             sd_reset,
    output wire                             sd_clk_out,
    inout  wire                             sd_cmd,
    inout  wire [3:0]                       sd_dat
    );

    // Aggregated reset signal
    wire    rst =   sys_rst | sd_cd;
    wire    [31:0]      m_wb_dat_o;
    wire    [31:0]      m_wb_dat_i;
    wire    [7:0]       m_wb_adr_o;
    wire    [3:0]       m_wb_sel_o;
    wire                m_wb_we_o;
    wire                m_wb_cyc_o;
    wire                m_wb_stb_o;
    wire                m_wb_ack_i;

    // Wishbone SD Controller <-> SD Buffer
    wire    [31:0]      s_wb_dat_i;
    wire    [31:0]      s_wb_dat_o;
    wire    [31:0]      s_wb_adr_i;
    wire    [3:0]       s_wb_sel_i;
    wire                s_wb_we_i;
    wire                s_wb_cyc_i;
    wire                s_wb_stb_i;
    wire                s_wb_ack_o;

    // SD Card Interface
    wire    [3:0]       sd_dat_dat_i;
    wire    [3:0]       sd_dat_out_o;
    wire                sd_dat_oe_o;
    wire                sd_cmd_dat_i;
    wire                sd_cmd_out_o;
    wire                sd_cmd_oe_o;
    wire                sd_int_cmd;
    wire                sd_int_data;

    // Init <-> Others
    wire                init_done;
    wire                is_hcxc;

    // Init <-> Wishbone SD Controller
    wire    [31:0]      m_wb_dat_o_init;
    wire    [7:0]       m_wb_adr_o_init;
    wire                m_wb_we_o_init;
    wire                m_wb_stb_o_init;

    // Core <-> Buffer
    wire    [31:0]      core_buffer_addr;
    wire                core_buffer_ce;
    wire                core_buffer_wr;
    wire    [1:0]       core_buffer_sz;
    wire    [`NOC_DATA_BITS]    core_buffer_data;
    wire    [`NOC_DATA_BITS]    buffer_core_data;

    // Core <-> Cache Manager
    wire                            core_cache_lock_acquire;
    wire                            core_cache_lock_release;
    wire                            cache_core_lock_status;
    wire                            core_cache_we;
    wire    [`PHY_BLOCK_BITS]       core_cache_addr;
    wire                            cache_core_rdy;
    wire    [`CACHE_ENTRY_BITS]     cache_core_entry;

    // Cache Manager <-> Transaction Manager
    wire    [31:0]      cache_tm_addr_sd;
    wire    [31:0]      cache_tm_addr_dma;
    wire                cache_tm_wr;
    wire                cache_tm_val;
    wire                tm_cache_rdy;
    wire                tm_cache_ok;
    wire                tm_cache_val;
    wire                cache_tm_rdy;

    // Transaction Manager <-> Wishbone SD Controller
    wire    [31:0]      m_wb_dat_o_tm;
    wire    [7:0]       m_wb_adr_o_tm;
    wire                m_wb_we_o_tm;
    wire                m_wb_stb_o_tm;

    assign  m_wb_dat_o  =   init_done ? m_wb_dat_o_tm : m_wb_dat_o_init;
    assign  m_wb_adr_o  =   init_done ? m_wb_adr_o_tm : m_wb_adr_o_init;
    assign  m_wb_sel_o  =   4'hf;
    assign  m_wb_cyc_o  =   1'b1;
    assign  m_wb_we_o   =   init_done ? m_wb_we_o_tm : m_wb_we_o_init;
    assign  m_wb_stb_o  =   init_done ? m_wb_stb_o_tm : m_wb_stb_o_init;

    assign  sd_cmd      =   sd_cmd_oe_o ? sd_cmd_out_o : 1'bz;
    assign  sd_dat      =   sd_dat_oe_o ? sd_dat_out_o : 4'bz;
    assign  sd_cmd_dat_i    =   sd_cmd;
    assign  sd_dat_dat_i    =   sd_dat;
    assign  sd_reset    =   sys_rst;

    piton_sd_core_ctrl sd_core_ctrl (
        .clk                    (sys_clk),
        .rst                    (~init_done | rst),

        .splitter_bridge_val    (splitter_sd_val),
        .splitter_bridge_data   (splitter_sd_data),
        .bridge_splitter_rdy    (sd_splitter_rdy),

        .bridge_splitter_val    (sd_splitter_val),
        .bridge_splitter_data   (sd_splitter_data),
        .splitter_bridge_rdy    (splitter_sd_rdy),

        .core_buffer_addr       (core_buffer_addr),
        .core_buffer_ce         (core_buffer_ce),
        .core_buffer_wr         (core_buffer_wr),
        .core_buffer_sz         (core_buffer_sz),
        .buffer_core_data       (buffer_core_data),
        .core_buffer_data       (core_buffer_data),

        .cache_lock_acquire     (core_cache_lock_acquire),
        .cache_lock_release     (core_cache_lock_release),
        .cache_lock_status      (cache_core_lock_status),
        .core_cache_we          (core_cache_we),
        .core_cache_addr        (core_cache_addr),
        .cache_core_rdy         (cache_core_rdy),
        .cache_core_entry       (cache_core_entry)
        );

    piton_sd_cache_manager  cache_manager (
        .clk                    (sys_clk),
        .rst                    (~init_done | rst),

        .lock_acquire           (core_cache_lock_acquire),
        .lock_release           (core_cache_lock_release),
        .lock_status            (cache_core_lock_status),

        .core_cache_we          (core_cache_we),
        .core_cache_addr        (core_cache_addr),
        .cache_core_rdy         (cache_core_rdy),
        .cache_core_entry       (cache_core_entry),

        .cache_tm_addr_sd       (cache_tm_addr_sd),
        .cache_tm_addr_dma      (cache_tm_addr_dma),
        .cache_tm_wr            (cache_tm_wr),
        .cache_tm_val           (cache_tm_val),
        .tm_cache_rdy           (tm_cache_rdy),

        .tm_cache_ok            (tm_cache_ok),
        .tm_cache_val           (tm_cache_val),
        .cache_tm_rdy           (cache_tm_rdy),

        .is_hcxc                (is_hcxc)
        );

    piton_sd_buffer sd_buffer (
        .clk                    (sys_clk),
        .rst                    (~init_done | rst),

        .s_wb_dat_i             (s_wb_dat_i),
        .s_wb_dat_o             (s_wb_dat_o),
        .s_wb_adr_i             (s_wb_adr_i),
        .s_wb_sel_i             (s_wb_sel_i),
        .s_wb_we_i              (s_wb_we_i),
        .s_wb_cyc_i             (s_wb_cyc_i),
        .s_wb_stb_i             (s_wb_stb_i),
        .s_wb_ack_o             (s_wb_ack_o),

        .buf_addr_i             (core_buffer_addr),
        .buf_data_i             (core_buffer_data),
        .buf_ce_i               (core_buffer_ce),
        .buf_we_i               (core_buffer_wr),
        .buf_data_sz            (core_buffer_sz),
        .buf_data_o             (buffer_core_data)
        );

    piton_sd_init sd_init (
        .clk                    (sys_clk),
        .rst                    (rst),

        .m_wb_dat_o             (m_wb_dat_o_init),
        .m_wb_dat_i             (m_wb_dat_i),
        .m_wb_adr_o             (m_wb_adr_o_init),
        .m_wb_sel_o             (),
        .m_wb_we_o              (m_wb_we_o_init),
        .m_wb_cyc_o             (),
        .m_wb_stb_o             (m_wb_stb_o_init),
        .m_wb_ack_i             (m_wb_ack_i),

        .sd_int_cmd             (sd_int_cmd),
        .sd_int_data            (sd_int_data),

        .init_done              (init_done),
        .is_hcxc                (is_hcxc)
        );

    piton_sd_transaction_manager sd_tm (
        .clk                    (sys_clk),
        .rst                    (~init_done | rst),

        .req_addr_sd            (cache_tm_addr_sd),
        .req_addr_dma           (cache_tm_addr_dma),
        .req_wr                 (cache_tm_wr),
        .req_val                (cache_tm_val),
        .req_rdy                (tm_cache_rdy),

        .resp_ok                (tm_cache_ok),
        .resp_val               (tm_cache_val),
        .resp_rdy               (cache_tm_rdy),

        .m_wb_dat_o             (m_wb_dat_o_tm),
        .m_wb_dat_i             (m_wb_dat_i),
        .m_wb_adr_o             (m_wb_adr_o_tm),
        .m_wb_sel_o             (),
        .m_wb_we_o              (m_wb_we_o_tm),
        .m_wb_cyc_o             (),
        .m_wb_stb_o             (m_wb_stb_o_tm),
        .m_wb_ack_i             (m_wb_ack_i),

        .sd_int_cmd             (sd_int_cmd),
        .sd_int_data            (sd_int_data)
        );

    sdc_controller sdc_controller (
        .wb_clk_i               (sys_clk),
        .wb_rst_i               (rst),

        .wb_dat_i               (m_wb_dat_o),
        .wb_dat_o               (m_wb_dat_i),
        .wb_adr_i               (m_wb_adr_o),
        .wb_sel_i               (m_wb_sel_o),
        .wb_we_i                (m_wb_we_o),
        .wb_cyc_i               (m_wb_cyc_o),
        .wb_stb_i               (m_wb_stb_o),
        .wb_ack_o               (m_wb_ack_i),

        .m_wb_dat_o			    (s_wb_dat_i),
        .m_wb_dat_i			    (s_wb_dat_o),
        .m_wb_adr_o			    (s_wb_adr_i),
        .m_wb_sel_o			    (s_wb_sel_i),
        .m_wb_we_o			    (s_wb_we_i),
        .m_wb_cyc_o			    (s_wb_cyc_i),
        .m_wb_stb_o			    (s_wb_stb_i),
        .m_wb_ack_i			    (s_wb_ack_o),
        .m_wb_cti_o			    (),
        .m_wb_bte_o			    (),

        .sd_cmd_dat_i			(sd_cmd_dat_i),
        .sd_cmd_out_o			(sd_cmd_out_o),
        .sd_cmd_oe_o			(sd_cmd_oe_o),
        .sd_dat_dat_i			(sd_dat_dat_i),
        .sd_dat_out_o			(sd_dat_out_o),
        .sd_dat_oe_o			(sd_dat_oe_o),

        .sd_clk_o_pad			(sd_clk_out),
        .sd_clk_i_pad			(sd_clk),
        .int_cmd				(sd_int_cmd),
        .int_data				(sd_int_data)
        );

endmodule
