// Author: David Schaffenrath, TU Graz - Florian Zaruba, ETH Zurich
// Date: 24.4.2017
// Description: Hardware-PTW
//
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
/* verilator lint_off WIDTH */
import ariane_pkg::*;

module ptw #(
        parameter int ASID_WIDTH = 1
    )
    (
    input  logic                    clk_i,    // Clock
    input  logic                    rst_ni,   // Asynchronous reset active low
    input  logic                    flush_i,  // flush everything, we need to do this because
                                              // actually everything we do is speculative at this stage
                                              // e.g.: there could be a CSR instruction that changes everything
    output logic                    ptw_active_o,
    output logic                    walking_instr_o, // set when walking for TLB
    output logic                    ptw_error_o, // set when an error occured
    input  logic                    enable_translation_i,
    // memory port
    output logic [11:0]             address_index_o,
    output logic [43:0]             address_tag_o,
    output logic [63:0]             data_wdata_o,
    output logic                    data_req_o,
    output logic                    data_we_o,
    output logic [7:0]              data_be_o,
    output logic                    kill_req_o,
    output logic                    tag_valid_o,
    input  logic                    data_gnt_i,
    input  logic                    data_rvalid_i,
    input  logic [63:0]             data_rdata_i,
    // to TLBs, update logic
    output logic                    itlb_update_o,
    output logic                    dtlb_update_o,
    output pte_t                    update_content_o,

    output logic                    update_is_2M_o,
    output logic                    update_is_1G_o,
    output logic [26:0]             update_vpn_o,
    output logic [ASID_WIDTH-1:0]   update_asid_o,
    input  logic [ASID_WIDTH-1:0]   asid_i,
    // from TLBs
    // did we miss?
    input  logic                    itlb_access_i,
    input  logic                    itlb_miss_i,
    input  logic [63:0]             itlb_vaddr_i,

    input  logic                    dtlb_access_i,
    input  logic                    dtlb_miss_i,
    input  logic [63:0]             dtlb_vaddr_i,
    // from CSR file
    input  logic [43:0]             satp_ppn_i, // ppn from satp
    input  logic                    mxr_i

);

    pte_t pte;
    assign pte = pte_t'(data_rdata_i);

    enum logic[1:0] {
      PTW_READY,
      PTW_WAIT_GRANT,
      PTW_PTE_LOOKUP,
      PTW_PROPAGATE_ERROR
    } ptw_state_q, ptw_state_n;

    // SV39 defines three levels of page tables
    enum logic [1:0] {
        LVL1, LVL2, LVL3
    } ptw_lvl_q, ptw_lvl_n;

    // is this an instruction page table walk?
    logic is_instr_ptw_q,   is_instr_ptw_n;
    logic global_mapping_q, global_mapping_n;
    // latched tag signal
    logic tag_valid_n,    tag_valid_q;

    assign ptw_active_o    = (ptw_state_q != PTW_READY);
    assign walking_instr_o = is_instr_ptw_q;

    // register the ASID
    logic [ASID_WIDTH-1:0] tlb_update_asid_q, tlb_update_asid_n;
    // register the VPN we need to walk
    logic [26:0] tlb_update_vpn_q, tlb_update_vpn_n;
    // 4 byte aligned physical pointer
    logic[55:0] ptw_pptr_q,        ptw_pptr_n;
    // directly output the correct physical address
    // ------
    // TODO
    // -------
    // assign address_o = {ptw_pptr_q, 4'b0}; TODO
    assign address_index_o = ptw_pptr_q[11:0];
    assign address_tag_o   = ptw_pptr_q[55:12];
    // we are never going to kill this request
    assign kill_req_o      = '0;
    // we are never going to write with the HPTW
    assign data_wdata_o    = 64'b0;
    // update the correct page table level
    assign update_is_2M_o = (ptw_lvl_q == LVL2);
    assign update_is_1G_o = (ptw_lvl_q == LVL1);
    // output the correct VPN and ASID
    assign update_vpn_o  = tlb_update_vpn_q;
    assign update_asid_o = tlb_update_asid_q;
    // set the global mapping bit
    assign update_content_o = pte || (global_mapping_q << 5);
    assign tag_valid_o      = tag_valid_q;

    //-------------------
    // Page table walker
    //-------------------
    // A virtual address va is translated into a physical address pa as follows:
    // 1. Let a be sptbr.ppn × PAGESIZE, and let i = LEVELS-1. (For Sv39,
    //    PAGESIZE=2^12 and LEVELS=3.)
    // 2. Let pte be the value of the PTE at address a+va.vpn[i]×PTESIZE. (For
    //    Sv32, PTESIZE=4.)
    // 3. If pte.v = 0, or if pte.r = 0 and pte.w = 1, stop and raise an access
    //    exception.
    // 4. Otherwise, the PTE is valid. If pte.r = 1 or pte.x = 1, go to step 5.
    //    Otherwise, this PTE is a pointer to the next level of the page table.
    //    Let i=i-1. If i < 0, stop and raise an access exception. Otherwise, let
    //    a = pte.ppn × PAGESIZE and go to step 2.
    // 5. A leaf PTE has been found. Determine if the requested memory access
    //    is allowed by the pte.r, pte.w, and pte.x bits. If not, stop and
    //    raise an access exception. Otherwise, the translation is successful.
    //    Set pte.a to 1, and, if the memory access is a store, set pte.d to 1.
    //    The translated physical address is given as follows:
    //      - pa.pgoff = va.pgoff.
    //      - If i > 0, then this is a superpage translation and
    //        pa.ppn[i-1:0] = va.vpn[i-1:0].
    //      - pa.ppn[LEVELS-1:i] = pte.ppn[LEVELS-1:i].
    always_comb begin : ptw
        // default assignments
        // PTW memory interface
        tag_valid_n       = 1'b0;
        data_req_o        = 1'b0;
        data_be_o         = 8'hFF;
        data_we_o         = 1'b0;
        ptw_error_o       = 1'b0;
        itlb_update_o     = 1'b0;
        dtlb_update_o     = 1'b0;
        is_instr_ptw_n    = is_instr_ptw_q;
        ptw_lvl_n         = ptw_lvl_q;
        ptw_pptr_n        = ptw_pptr_q;
        ptw_state_n       = ptw_state_q;
        global_mapping_n  = global_mapping_q;
        // input registers
        tlb_update_asid_n = tlb_update_asid_q;
        tlb_update_vpn_n  = tlb_update_vpn_q;

        unique case (ptw_state_q)

            PTW_READY: begin
                global_mapping_n = 1'b0;
                // if we got an ITLB miss
                if (enable_translation_i & itlb_access_i & itlb_miss_i & ~dtlb_access_i) begin
                    ptw_pptr_n          = {satp_ppn_i, itlb_vaddr_i[38:30], 3'b0};
                    is_instr_ptw_n      = 1'b1;
                    tlb_update_asid_n   = asid_i;
                    tlb_update_vpn_n    = itlb_vaddr_i[38:12];
                    ptw_state_n         = PTW_WAIT_GRANT;
                // we got an DTLB miss
                end else if (enable_translation_i & dtlb_access_i & dtlb_miss_i) begin
                    ptw_pptr_n          = {satp_ppn_i, dtlb_vaddr_i[38:30], 3'b0};
                    is_instr_ptw_n      = 1'b0;
                    tlb_update_asid_n   = asid_i;
                    tlb_update_vpn_n    = dtlb_vaddr_i[38:12];
                    ptw_state_n         = PTW_WAIT_GRANT;
                end
            end

            PTW_WAIT_GRANT: begin
                // send a request out
                data_req_o = 1'b1;
                // wait for the grant
                if (data_gnt_i) begin
                    // send the tag valid signal one cycle later
                    tag_valid_n = 1'b1;
                    ptw_state_n = PTW_PTE_LOOKUP;
                end
                // we could potentially error out here
            end

            PTW_PTE_LOOKUP: begin
                // we wait for the valid signal
                if (data_rvalid_i) begin
                    // check if the global mapping bit is set
                    if (pte.g)
                        global_mapping_n = 1'b1;
                    // depending on the current level send the right address
                    if (ptw_lvl_q == LVL2)
                        ptw_pptr_n = {pte.ppn, tlb_update_vpn_q[17:9], 3'b0};
                    if (ptw_lvl_q == LVL3)
                        ptw_pptr_n = {pte.ppn, tlb_update_vpn_q[8:0], 3'b0};

                    // -------------
                    // Invalid PTE
                    // -------------
                    // If pte.v = 0, or if pte.r = 0 and pte.w = 1, stop and raise a page-fault exception.
                    if (!pte.v || (!pte.r && pte.w))
                        ptw_state_n = PTW_PROPAGATE_ERROR;
                    // -----------
                    // Valid PTE
                    // -----------
                    else begin
                        ptw_state_n = PTW_READY;
                        // it is a valid PTE
                        // if pte.r = 1 or pte.x = 1 it is a valid PTE
                        if (pte.r || pte.x) begin
                            // Valid translation found (either 1G, 2M or 4K entry)
                            if (is_instr_ptw_q) begin
                                // ------------
                                // Update ITLB
                                // ------------
                                // If page is not executable, we can directly raise an error. This
                                // saves the 'x' bits in the ITLB otherwise needed for access
                                // right checks and doesn't put a useless entry into the TLB.
                                if (~pte.x)
                                  ptw_state_n = PTW_PROPAGATE_ERROR;
                                else
                                  itlb_update_o = 1'b1;

                            end else begin
                                // ------------
                                // Update DTLB
                                // ------------
                                // If page is not readable (there are no write-only pages), or the
                                // access that triggered the PTW is a write, but the page is not
                                // write-able, we can directly raise an error. This saves the 'r'
                                // bits in the TLB otherwise needed for access right checks and
                                // doesn't put a useless entry into the TLB.
                                if ((~pte.r && ~(pte.x && mxr_i)) || (~pte.w)) begin
                                  ptw_state_n   = PTW_PROPAGATE_ERROR;
                                end else begin
                                  dtlb_update_o = 1'b1;
                                end
                            end
                        // this is a pointer to the next TLB level
                        end else begin
                            // pointer to next level of page table
                            if (ptw_lvl_q == LVL1)
                                ptw_lvl_n = LVL2;

                            if (ptw_lvl_q == LVL2)
                                ptw_lvl_n = LVL3;

                            ptw_state_n = PTW_WAIT_GRANT;

                            if (ptw_lvl_q == LVL3) begin
                              // Should already be the last level page table => Error
                              ptw_lvl_n   = LVL3;
                              ptw_state_n = PTW_PROPAGATE_ERROR;
                            end
                        end
                    end
                end
                // we've got a data grant so tell the cache that the tag is valid
            end
            // TODO: propagate error
            PTW_PROPAGATE_ERROR: begin
                ptw_state_n = PTW_READY;
                ptw_error_o = 1'b1;
            end


        endcase // ptw_state_q
    end

    // sequential process
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if(~rst_ni) begin
            ptw_state_q        <= PTW_READY;
            is_instr_ptw_q     <= 1'b0;
            ptw_lvl_q          <= LVL1;
            tag_valid_q        <= 1'b0;
            tlb_update_asid_q  <= '{default: 0};
            tlb_update_vpn_q   <= '{default: 0};
            ptw_pptr_q         <= '{default: 0};
            global_mapping_q   <= 1'b0;
        end else begin
            ptw_state_q        <= ptw_state_n;
            ptw_pptr_q         <= ptw_pptr_n;
            is_instr_ptw_q     <= is_instr_ptw_n;
            ptw_lvl_q          <= ptw_lvl_n;
            tag_valid_q        <= tag_valid_n;
            tlb_update_asid_q  <= tlb_update_asid_n;
            tlb_update_vpn_q   <= tlb_update_vpn_n;
            global_mapping_q   <= global_mapping_n;
        end
    end

endmodule
/* verilator lint_on WIDTH */