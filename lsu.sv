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
    input  logic                  clk_i,
    input  logic                  rst_ni,

    input  fu_op                  operator_i,
    input  logic [63:0]           operand_a_i,
    input  logic [63:0]           operand_b_i,
    input  logic [63:0]           imm_i,
    output logic                  lsu_ready_o,      // FU is ready e.g. not busy
    input  logic                  lsu_valid_i,      // Input is valid
    input  logic                  lsu_trans_id_i,   // transaction id, needed for WB
    output logic [4:0]            lsu_trans_id_o,   // ID of scoreboard entry at which to write back
    output logic                  lsu_valid_o,      // transaction id for which the output is the requested one

    input  logic                  enable_translation_i,

    input  logic                  fetch_req_i,
    output logic                  fetch_gnt_o,
    output logic                  fetch_valid_o,
    output logic                  fetch_err_o,
    input  logic [63:0]           fetch_vaddr_i,
    output logic [31:0]           fetch_rdata_o,

    input  priv_lvl_t             priv_lvl_i,
    input  logic                  flag_pum_i,
    input  logic                  flag_mxr_i,
    input  logic [19:0]           pd_ppn_i,
    input  logic [ASID_WIDTH-1:0] asid_i,
    input  logic                  flush_tlb_i,
    mem_if.Slave                  instr_if,
    mem_if.Slave                  data_if,

    output exception              lsu_exception_o   // to writeback, signal exception status ld/st exception

);
    logic [63:0] vaddr;

    // dummy implementation
    // instruction interface
    assign instr_if.data_req       = fetch_req_i;
    assign fetch_gnt_o             = instr_if.data_gnt;
    assign fetch_valid_o           = instr_if.data_rvalid;
    assign instr_if.address        = fetch_vaddr_i;
    assign fetch_rdata_o           = instr_if.data_rdata;
    assign fetch_err_o             = 1'b0;

    // -------------------
    // MMU e.g.: TLBs/PTW
    // -------------------

    // ---------------
    // Memory Arbiter
    // ---------------

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