// Author: Florian Zaruba, ETH Zurich / David Schaffenrath, TU Graz
// Date: 19/04/2017
// Description: Memory Management Unit for Ariane, contains TLB and
//              address translation unit. SV39 as defined in RISC-V
//              privilege specification 1.9
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

module mmu #(
      parameter int INSTR_TLB_ENTRIES = 4,
      parameter int DATA_TLB_ENTRIES = 4,
      parameter int ASID_WIDTH = 1
    )
    (
        input logic                             clk_i,
        input logic                             rst_ni,
        input logic                             enable_translation_i,
        // IF interface
        input  logic                            fetch_req_i,
        output logic                            fetch_gnt_o,
        output logic                            fetch_valid_o,
        output logic                            fetch_err_o,
        input  logic [63:0]                     fetch_vaddr_i,
        output logic [31:0]                     fetch_rdata_o, // pass-through because of interfaces
        // LSU interface
        input  logic                            lsu_req_i,
        output logic                            lsu_gnt_o,
        output logic                            lsu_valid_o,
        input  logic                            lsu_we_i,
        input  logic [7:0]                      lsu_be_i,
        output logic                            lsu_err_o,
        input  logic [63:0]                     lsu_vaddr_i,
        input  logic [63:0]                     lsu_wdata_i, // pass-through because of interfaces
        output logic [63:0]                     lsu_rdata_o, // pass-through because of interfaces
        // General control signals
        input priv_lvl_t                        priv_lvl_i,
        input logic                             flag_pum_i,
        input logic                             flag_mxr_i,
        // input logic flag_mprv_i,
        input logic [19:0]                      pd_ppn_i,
        input logic [ASID_WIDTH-1:0]            asid_i,
        input logic                             flush_tlb_i,
        input logic                             lsu_ready_wb_i,
        // Memory interfaces
        // Instruction memory interface
        mem_if.Slave                            instr_if,
        // Data memory interface
        mem_if.Slave                            data_if
);

    // dummy implementation
    // instruction interface
    assign instr_if.data_req       = fetch_req_i;
    assign fetch_gnt_o             = instr_if.data_gnt;
    assign fetch_valid_o           = instr_if.data_rvalid;
    assign instr_if.address        = fetch_vaddr_i;
    assign fetch_rdata_o           = instr_if.data_rdata;
    assign fetch_err_o             = 1'b0;
endmodule