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

module piton_sd_top #(
    parameter AxiAddrWidth = 64,
    parameter AxiDataWidth = 64,
    parameter AxiIdWidth   = 5,
    parameter AxiUserWidth = 1
) (
    // Clock and reset
    input wire                       sys_clk,
    input wire                       sd_clk,
    input wire                       sys_rst,

    // SD interface
    input wire                       sd_cd,
    output wire                      sd_reset,
    output wire                      sd_clk_out,
    input [3:0]                      sd_dat_dat_i,
    output [3:0]                     sd_dat_out_o,
    output                           sd_dat_oe_o,
    input                            sd_cmd_dat_i,
    output                           sd_cmd_out_o,
    output                           sd_cmd_oe_o,

    output                           init_done,
    output wire                      is_hcxc,     // output if the card is a SDHC/SDXC card

    // Request Slave
    input wire [`SD_ADDR_WIDTH-1:0]  req_addr_sd, // addr in SD 
    input wire [`SD_ADDR_WIDTH-1:0]  req_addr_dma, // addr in fake memory
    input wire [`SD_ADDR_WIDTH-10:0] req_blkcnt,
    input wire                       req_wr, // HIGH write; LOW read.
    input wire                       req_val,
    output wire                      req_rdy,
    output wire [`SD_ADDR_WIDTH-1:0] req_addr_sd_f,
    output wire [`SD_ADDR_WIDTH-1:0] req_addr_dma_f,

    // Response Master
    output wire                      resp_ok, // HIGH ok; LOW err.
    output wire                      resp_val,
    input wire                       resp_rdy,
   
    // Core <-> Buffer
    input wire    [31:0]      core_buffer_addr,
    input wire                core_buffer_ce,
    input wire                core_buffer_wr,
    input wire    [1:0]       core_buffer_sz,
    input wire    [`NOC_DATA_BITS]    core_buffer_data,
    output wire   [`NOC_DATA_BITS]    buffer_core_data,
    // init debug
    output wire [7:0]                 init_state,
    // init compact FSM output
    output wire [23:0]               counter,
    output wire [42:0]               init_fsm, // {adr, dat, we, stb, counter_en}
    // tran debug
    output wire [5:0]                tran_state,
    // tran compact FSM output
    output wire [41:0]               tran_fsm // {adr, dat, we, stb}
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
    wire                sd_int_cmd;
    wire                sd_int_data;

    // Init <-> Wishbone SD Controller
    wire    [31:0]      m_wb_dat_o_init;
    wire    [7:0]       m_wb_adr_o_init;
    wire                m_wb_we_o_init;
    wire                m_wb_stb_o_init;

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

    assign  sd_reset    =   sys_rst;

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
        .is_hcxc                (is_hcxc),
        .init_state             (init_state),
        // compact FSM output
        .counter,
        .fsm                     (init_fsm) // {adr, dat, we, stb, counter_en}
        );

    piton_sd_transaction_manager sd_tm (
        .clk                    (sys_clk),
        .rst                    (~init_done | rst),

        .req_addr_sd            (req_addr_sd),
        .req_addr_dma           (req_addr_dma),
        .req_blkcnt             (req_blkcnt),
        .req_wr                 (req_wr),
        .req_val                (req_val),
        .req_rdy                (req_rdy),
        .req_addr_sd_f          (req_addr_sd_f),
        .req_addr_dma_f         (req_addr_dma_f),

        .resp_ok                (resp_ok),
        .resp_val               (resp_val),
        .resp_rdy               (resp_rdy),

        .m_wb_dat_o             (m_wb_dat_o_tm),
        .m_wb_dat_i             (m_wb_dat_i),
        .m_wb_adr_o             (m_wb_adr_o_tm),
        .m_wb_sel_o             (),
        .m_wb_we_o              (m_wb_we_o_tm),
        .m_wb_cyc_o             (),
        .m_wb_stb_o             (m_wb_stb_o_tm),
        .m_wb_ack_i             (m_wb_ack_i),

        .sd_int_cmd             (sd_int_cmd),
        .sd_int_data            (sd_int_data),
        .tran_state             (tran_state),
        // compact FSM output
        .fsm                    (tran_fsm) // {adr, dat, we, stb, counter_en}
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
