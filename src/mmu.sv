// Author: Florian Zaruba, ETH Zurich
// Date: 19/04/2017
// Description: Memory Management Unit for Ariane, contains TLB and
//              address translation unit. SV39 as defined in RISC-V
//              privilege specification 1.11-WIP
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
      parameter int DATA_TLB_ENTRIES  = 4,
      parameter int ASID_WIDTH        = 1
    )
    (
        input  logic                            clk_i,
        input  logic                            rst_ni,
        input  logic                            flush_i,
        input  logic                            enable_translation_i,
        input  logic                            en_ld_st_translation_i,   // enable virtual memory translation for load/stores

        // IF interface
        input  logic                            fetch_req_i,
        output logic                            fetch_gnt_o,
        output logic                            fetch_valid_o,
        input  logic [63:0]                     fetch_vaddr_i,
        output logic [63:0]                     fetch_rdata_o,  // pass-through because of interfaces
        output exception                        fetch_ex_o,     // write-back fetch exceptions (e.g.: bus faults, page faults, etc.)
        // LSU interface
        // this is a more minimalistic interface because the actual addressing logic is handled
        // in the LSU as we distinguish load and stores, what we do here is simple address translation
        input  exception                        misaligned_ex_i,
        input  logic                            lsu_req_i,        // request address translation
        input  logic [63:0]                     lsu_vaddr_i,      // virtual address in
        input  logic                            lsu_is_store_i,   // the translation is requested by a store
        // if we need to walk the page table we can't grant in the same cycle
        // Cycle 0
        output logic                            lsu_dtlb_hit_o,   // sent in the same cycle as the request if translation hits in the DTLB
        // Cycle 1
        output logic                            lsu_valid_o,      // translation is valid
        output logic [63:0]                     lsu_paddr_o,      // translated address
        output exception                        lsu_exception_o,  // address translation threw an exception
        // General control signals
        input priv_lvl_t                        priv_lvl_i,
        input priv_lvl_t                        ld_st_priv_lvl_i,
        input logic                             sum_i,
        input logic                             mxr_i,
        // input logic flag_mprv_i,
        input logic [43:0]                      satp_ppn_i,
        input logic [ASID_WIDTH-1:0]            asid_i,
        input logic                             flush_tlb_i,
        // Memory interfaces
        // Instruction memory/cache
        output logic [63:0]                     instr_if_address_o,
        output logic                            instr_if_data_req_o,
        output logic [3:0]                      instr_if_data_be_o,
        input  logic                            instr_if_data_gnt_i,
        input  logic                            instr_if_data_rvalid_i,
        input  logic [63:0]                     instr_if_data_rdata_i,
        // Data memory/cache
        output logic [11:0]                     address_index_o,
        output logic [43:0]                     address_tag_o,
        output logic [63:0]                     data_wdata_o,
        output logic                            data_req_o,
        output logic                            data_we_o,
        output logic [7:0]                      data_be_o,
        output logic                            kill_req_o,
        output logic                            tag_valid_o,
        input  logic                            data_gnt_i,
        input  logic                            data_rvalid_i,
        input  logic [63:0]                     data_rdata_i
);
    // instruction error
    // instruction error valid signal and exception, delayed one cycle
    logic        ierr_valid_q, ierr_valid_n;
    exception    fetch_ex_q,   fetch_ex_n;

    logic        iaccess_err;   // insufficient privilege to access this instruction page
    logic        daccess_err;   // insufficient privilege to access this data page
    logic        ptw_active;    // PTW is currently walking a page table
    logic        walking_instr; // PTW is walking because of an ITLB miss
    logic        ptw_error;     // PTW threw an exception

    logic        update_is_2M;
    logic        update_is_1G;
    logic [38:0] update_vaddr;
    logic [0:0]  update_asid;
    pte_t        update_content;

    logic        itlb_update;
    logic        itlb_lu_access;
    pte_t        itlb_content;
    logic        itlb_is_2M;
    logic        itlb_is_1G;
    logic        itlb_lu_hit;

    logic        dtlb_update;
    logic        dtlb_lu_access;
    pte_t        dtlb_content;
    logic        dtlb_is_2M;
    logic        dtlb_is_1G;
    logic        dtlb_lu_hit;

    // Assignments
    assign itlb_lu_access = fetch_req_i;
    assign dtlb_lu_access = lsu_req_i;
    assign fetch_rdata_o  = instr_if_data_rdata_i;
    assign fetch_ex_o     = fetch_ex_q;

    tlb #(
        .TLB_ENTRIES      ( INSTR_TLB_ENTRIES          ),
        .ASID_WIDTH       ( ASID_WIDTH                 )
    ) itlb_i (
        .clk_i            ( clk_i                      ),
        .rst_ni           ( rst_ni                     ),
        .flush_i          ( flush_tlb_i                ),
        .update_is_2M_i   ( update_is_2M               ),
        .update_is_1G_i   ( update_is_1G               ),
        .update_vpn_i     ( update_vaddr[38:12]        ),
        .update_asid_i    ( update_asid                ),
        .update_content_i ( update_content             ),
        .update_tlb_i     ( itlb_update                ),

        .lu_access_i      ( itlb_lu_access             ),
        .lu_asid_i        ( asid_i                     ),
        .lu_vaddr_i       ( fetch_vaddr_i              ),
        .lu_content_o     ( itlb_content               ),
        .lu_is_2M_o       ( itlb_is_2M                 ),
        .lu_is_1G_o       ( itlb_is_1G                 ),
        .lu_hit_o         ( itlb_lu_hit                )
    );

    tlb #(
        .TLB_ENTRIES(DATA_TLB_ENTRIES),
        .ASID_WIDTH(ASID_WIDTH))
    dtlb_i (
        .clk_i            ( clk_i                       ),
        .rst_ni           ( rst_ni                      ),
        .flush_i          ( flush_tlb_i                 ),
        .update_is_2M_i   ( update_is_2M                ),
        .update_is_1G_i   ( update_is_1G                ),
        .update_vpn_i     ( update_vaddr[38:12]         ),
        .update_asid_i    ( update_asid                 ),
        .update_content_i ( update_content              ),
        .update_tlb_i     ( dtlb_update                 ),

        .lu_access_i      ( dtlb_lu_access              ),
        .lu_asid_i        ( asid_i                      ),
        .lu_vaddr_i       ( lsu_vaddr_i                 ),
        .lu_content_o     ( dtlb_content                ),
        .lu_is_2M_o       ( dtlb_is_2M                  ),
        .lu_is_1G_o       ( dtlb_is_1G                  ),
        .lu_hit_o         ( dtlb_lu_hit                 )
    );


    ptw  #(
        .ASID_WIDTH             ( ASID_WIDTH            )
    ) ptw_i
    (
        .clk_i                  ( clk_i                 ),
        .rst_ni                 ( rst_ni                ),
        .ptw_active_o           ( ptw_active            ),
        .walking_instr_o        ( walking_instr         ),
        .ptw_error_o            ( ptw_error             ),
        .enable_translation_i   ( enable_translation_i  ),

        .itlb_update_o          ( itlb_update           ),
        .dtlb_update_o          ( dtlb_update           ),
        .update_content_o       ( update_content        ),
        .update_is_2M_o         ( update_is_2M          ),
        .update_is_1G_o         ( update_is_1G          ),
        .update_vaddr_o         ( update_vaddr          ),
        .update_asid_o          ( update_asid           ),

        .itlb_access_i          ( itlb_lu_access        ),
        .itlb_miss_i            ( ~itlb_lu_hit          ),
        .itlb_vaddr_i           ( fetch_vaddr_i         ),

        .dtlb_access_i          ( dtlb_lu_access        ),
        .dtlb_miss_i            ( ~dtlb_lu_hit          ),
        .dtlb_vaddr_i           ( lsu_vaddr_i           ),
        .*
     );

    //-----------------------
    // Instruction Interface
    //-----------------------
    // This is a full memory interface, e.g.: it handles all signals to the I$
    // Exceptions are always signaled together with the fetch_valid_o signal
    always_comb begin : instr_interface
        // MMU disabled: just pass through
        instr_if_data_req_o = fetch_req_i;
        instr_if_address_o  = fetch_vaddr_i; // play through in case we disabled address translation
        fetch_gnt_o         = instr_if_data_gnt_i;
        // two potential exception sources:
        // 1. HPTW threw an exception -> signal with a page fault exception
        // 2. We got an access error because of insufficient permissions -> throw an access exception
        fetch_ex_n    = '0;
        ierr_valid_n  = 1'b0; // we keep a separate valid signal in case of an error
        // Check whether we are allowed to access this memory region from a fetch perspective
        iaccess_err   = fetch_req_i && (((priv_lvl_i == PRIV_LVL_U) && ~itlb_content.u)
                                     || ((priv_lvl_i == PRIV_LVL_S) && itlb_content.u));

        // check that the upper-most bits (63-39) are the same, otherwise throw a page fault exception...
        if (!((&fetch_vaddr_i[63:39]) == 1'b1 || (|fetch_vaddr_i[63:39]) == 1'b0)) begin
            fetch_ex_n   = {INSTR_PAGE_FAULT, fetch_vaddr_i, 1'b1};
            ierr_valid_n = 1'b1;
            fetch_gnt_o  = 1'b1;
        end
        // MMU enabled: address from TLB, request delayed until hit. Error when TLB
        // hit and no access right or TLB hit and translated address not valid (e.g.
        // AXI decode error), or when PTW performs walk due to ITLB miss and raises
        // an error.
        if (enable_translation_i) begin
            instr_if_data_req_o = 1'b0;

            // 4K page
            instr_if_address_o = {itlb_content.ppn, fetch_vaddr_i[11:0]};
            // Mega page
            if (itlb_is_2M) begin
                instr_if_address_o[20:12] = fetch_vaddr_i[20:12];
            end
            // Giga page
            if (itlb_is_1G) begin
                instr_if_address_o[29:12] = fetch_vaddr_i[29:12];
            end

            // ---------
            // ITLB Hit
            // --------
            // if we hit the ITLB output the request signal immediately
            if (itlb_lu_hit) begin
                instr_if_data_req_o = fetch_req_i;
                // we got an access error
                if (iaccess_err) begin
                  // immediately grant a fetch which threw an exception, and stop the request from happening
                  instr_if_data_req_o = 1'b0;
                  fetch_gnt_o         = 1'b1;
                  ierr_valid_n        = 1'b1;
                  // throw a page fault
                  fetch_ex_n          = {INSTR_ACCESS_FAULT, fetch_vaddr_i, 1'b1};
                end
            end else
            // ---------
            // ITLB Miss
            // ---------
            // watch out for exceptions happening during walking the page table
            if (ptw_active && walking_instr) begin
                // on an error pass through fetch with an error signaled
                fetch_gnt_o  = ptw_error;
                ierr_valid_n = ptw_error; // signal valid/error on next cycle
                fetch_ex_n   = {INSTR_PAGE_FAULT, {25'b0, update_vaddr}, 1'b1};
            end
        end
        // the fetch is valid if we either got an error in the previous cycle or the I$ gave us a valid signal.
        fetch_valid_o = instr_if_data_rvalid_i || ierr_valid_q;
    end
    // ----------
    // Registers
    // ----------
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if(~rst_ni) begin
            ierr_valid_q <= 1'b0;
            fetch_ex_q   <= '0;
        end else begin
            ierr_valid_q <= ierr_valid_n;
            fetch_ex_q   <= fetch_ex_n;
        end
    end

    //-----------------------
    // Data Interface
    //-----------------------
    logic [63:0] lsu_vaddr_n,     lsu_vaddr_q;
    pte_t        dtlb_pte_n,      dtlb_pte_q;
    exception    misaligned_ex_n, misaligned_ex_q;
    logic        lsu_req_n,       lsu_req_q;
    logic        lsu_is_store_n,  lsu_is_store_q;
    logic        dtlb_hit_n,      dtlb_hit_q;
    logic        dtlb_is_2M_n,    dtlb_is_2M_q;
    logic        dtlb_is_1G_n,    dtlb_is_1G_q;

    // check if we need to do translation or if we are always ready (e.g.: we are not translating anything)
    assign lsu_dtlb_hit_o = (en_ld_st_translation_i) ? dtlb_lu_hit :  1'b1;

    // The data interface is simpler and only consists of a request/response interface
    always_comb begin : data_interface
        // save request and DTLB response
        lsu_vaddr_n           = lsu_vaddr_i;
        lsu_req_n             = lsu_req_i;
        misaligned_ex_n       = misaligned_ex_i;
        dtlb_pte_n            = dtlb_content;
        dtlb_hit_n            = dtlb_lu_hit;
        lsu_is_store_n        = lsu_is_store_i;
        dtlb_is_2M_n          = dtlb_is_2M;
        dtlb_is_1G_n          = dtlb_is_1G;

        lsu_paddr_o           = lsu_vaddr_q;
        lsu_valid_o           = lsu_req_q;
        lsu_exception_o       = misaligned_ex_q;
        // mute misaligned exceptions if there is no request otherwise they will throw accidental exceptions
        misaligned_ex_n.valid = misaligned_ex_i.valid & lsu_req_i;

        // Check if the User flag is set, then we may only access it in supervisor mode
        // if SUM is enabled
        daccess_err = (ld_st_priv_lvl_i == PRIV_LVL_S && !sum_i && dtlb_pte_q.u) || // SUM is not set and we are trying to access a user page in supervisor mode
                      (ld_st_priv_lvl_i == PRIV_LVL_U && !dtlb_pte_q.u);            // this is not a user page but we are in user mode and trying to access it
        // translation is enabled and no misaligned exception occurred
        if (en_ld_st_translation_i && !misaligned_ex_q.valid) begin
            lsu_valid_o = 1'b0;
            // 4K page
            lsu_paddr_o = {dtlb_pte_q.ppn, lsu_vaddr_q[11:0]};
            // Mega page
            if (dtlb_is_2M_q) begin
              lsu_paddr_o[20:12] = lsu_vaddr_q[20:12];
            end
            // Giga page
            if (dtlb_is_1G_q) begin
                lsu_paddr_o[29:12] = lsu_vaddr_q[29:12];
            end
            // ---------
            // DTLB Hit
            // --------
            if (dtlb_hit_q && lsu_req_q) begin
                lsu_valid_o = 1'b1;
                // this is a store
                if (lsu_is_store_q) begin
                    // check if the page is write-able and we are not violating privileges
                    if (!dtlb_pte_q.w || daccess_err) begin
                        lsu_exception_o = {ST_ACCESS_FAULT, lsu_vaddr_q, 1'b1};
                    end
                    // check if the dirty flag is set
                    if (!dtlb_pte_q.d) begin
                        lsu_exception_o = {STORE_PAGE_FAULT, lsu_vaddr_q, 1'b1};
                    end
                // this is a load, check for sufficient access privileges
                end else if (daccess_err) begin
                    lsu_exception_o = {LD_ACCESS_FAULT, lsu_vaddr_q, 1'b1};
                end
            end else

            // ---------
            // DTLB Miss
            // ---------
            // watch out for exceptions
            if (ptw_active && !walking_instr) begin
                // page table walker threw an exception
                if (ptw_error) begin
                    // an error makes the translation valid
                    lsu_valid_o = 1'b1;
                    // the page table walker can only throw page faults
                    if (lsu_is_store_q) begin
                        lsu_exception_o = {STORE_PAGE_FAULT, {25'b0, update_vaddr}, 1'b1};
                    end else begin
                        lsu_exception_o = {LOAD_PAGE_FAULT, {25'b0, update_vaddr}, 1'b1};
                    end
                end
            end
        end
    end
    // ----------
    // Registers
    // ----------
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if(~rst_ni) begin
            lsu_vaddr_q      <= '0;
            lsu_req_q        <= '0;
            misaligned_ex_q  <= '0;
            dtlb_pte_q       <= '0;
            dtlb_hit_q       <= '0;
            lsu_is_store_q   <= '0;
            dtlb_is_2M_q     <= '0;
            dtlb_is_1G_q     <= '0;
        end else begin
            lsu_vaddr_q      <=  lsu_vaddr_n;
            lsu_req_q        <=  lsu_req_n;
            misaligned_ex_q  <=  misaligned_ex_n;
            dtlb_pte_q       <=  dtlb_pte_n;
            dtlb_hit_q       <=  dtlb_hit_n;
            lsu_is_store_q   <=  lsu_is_store_n;
            dtlb_is_2M_q     <=  dtlb_is_2M_n;
            dtlb_is_1G_q     <=  dtlb_is_1G_n;
        end
    end
endmodule