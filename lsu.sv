// Author: Florian Zaruba, ETH Zurich
// Date: 19.04.2017
// Description: Load Store Unit, handles address calculation and memory interface signals
//
// Copyright (C) 2017 ETH Zurich, University of Bologna
// All rights reserved.
//
// This code is under development and not yet released to the public.
// Until it is released, the code is under the copyright of ETH Zurich and
// the University of Bologna, and may contain confidential and/or unpublished
// work. Any reuse/redistribution is strictly forbidden without written
// permission from ETH Zurich.
//
// Bug fixes and contributions will eventually be released under the
// SolderPad open hardware license in the context of the PULP platform
// (http://www.pulp-platform.org), under the copyright of ETH Zurich and the
// University of Bologna.
//
import ariane_pkg::*;

module lsu #(
    parameter int ASID_WIDTH = 1
    )(
    input  logic                     clk_i,
    input  logic                     rst_ni,

    input  fu_op                     operator_i,
    input  logic [63:0]              operand_a_i,
    input  logic [63:0]              operand_b_i,
    input  logic [63:0]              imm_i,
    output logic                     lsu_ready_o,      // FU is ready e.g. not busy
    input  logic                     lsu_valid_i,      // Input is valid
    input  logic [TRANS_ID_BITS-1:0] lsu_trans_id_i,   // transaction id, needed for WB
    output logic [TRANS_ID_BITS-1:0] lsu_trans_id_o,   // ID of scoreboard entry at which to write back
    output logic                     lsu_valid_o,      // transaction id for which the output is the requested one

    input  logic                     enable_translation_i,

    input  logic                     fetch_req_i,
    output logic                     fetch_gnt_o,
    output logic                     fetch_valid_o,
    output logic                     fetch_err_o,
    input  logic [63:0]              fetch_vaddr_i,
    output logic [31:0]              fetch_rdata_o,

    input  priv_lvl_t                priv_lvl_i,
    input  logic                     flag_pum_i,
    input  logic                     flag_mxr_i,
    input  logic [37:0]              pd_ppn_i,
    input  logic [ASID_WIDTH-1:0]    asid_i,
    input  logic                     flush_tlb_i,

    mem_if.Slave                     instr_if,
    mem_if.Slave                     data_if,

    output exception                 lsu_exception_o   // to WB, signal exception status LD/ST exception

);
    assign lsu_trans_id_o = lsu_trans_id_i;
    assign lsu_valid_o = 1'b0;

    logic [63:0] vaddr;

    // ---------------
    // Memory Arbiter
    // ---------------
    logic [2:0][63:0] address_i;
    logic [2:0][63:0] data_wdata_i;
    logic [2:0] data_req_i;
    logic [2:0] data_we_i;
    logic [2:0][7:0] data_be_i;
    logic [2:0] data_gnt_o;
    logic [2:0] data_rvalid_o;
    logic [2:0][63:0] data_rdata_o;

    mem_arbiter i_mem_arbiter (
        .clk_i        ( clk_i               ),
        .rst_ni       ( rst_ni              ),

        // to D$
        .address_o    ( data_if.address     ),
        .data_wdata_o ( data_if.data_wdata  ),
        .data_req_o   ( data_if.data_req    ),
        .data_we_o    ( data_if.data_we     ),
        .data_be_o    ( data_if.data_be     ),
        .data_gnt_i   ( data_if.data_gnt    ),
        .data_rvalid_i( data_if.data_rvalid ),
        .data_rdata_i ( data_if.data_rdata  ),

        // from PTW, Load logic and store queue
        .address_i    ( address_i           ),
        .data_wdata_i ( data_wdata_i        ),
        .data_req_i   ( data_req_i          ),
        .data_we_i    ( data_we_i           ),
        .data_be_i    ( data_be_i           ),
        .data_gnt_o   ( data_gnt_o          ),
        .data_rvalid_o( data_rvalid_o       ),
        .data_rdata_o ( data_rdata_o        )
    );

    // -------------------
    // MMU e.g.: TLBs/PTW
    // -------------------
    logic lsu_req_i;
    logic [63:0] lsu_vaddr_i;
    logic lsu_ready_wb_i;

    mmu #(
        .INSTR_TLB_ENTRIES      ( 16                   ),
        .DATA_TLB_ENTRIES       ( 16                   ),
        .ASID_WIDTH             ( ASID_WIDTH           )
    ) i_mmu (
        .lsu_req_i              ( lsu_req_i            ),
        .lsu_vaddr_i            ( lsu_vaddr_i          ),
        .lsu_valid_o            (           ),
        .*
    );

    // ---------------
    // Store Queue
    // ---------------

    // ---------------
    // Sign Extend
    // ---------------

    // ------------------------------
    // Address Generation Unit (AGU)
    // ------------------------------
    assign vaddr = imm_i + operand_a_i;
    assign data_if.address = vaddr;

    // ------------------
    // LSU Control
    // ------------------

    // ------------------
    // Exception Control
    // ------------------
    // misaligned detector
    // page fault, privilege exception

endmodule