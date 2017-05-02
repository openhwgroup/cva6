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
    output logic [63:0]             address_o,
    output logic [63:0]             data_wdata_o,
    output logic                    data_req_o,
    output logic                    data_we_o,
    output logic [7:0]              data_be_o,
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
    input  logic [37:0]             pd_ppn_i, // ppn from sptbr
    input  logic                    flag_mxr_i

);

    pte_t ptw_pte_i;
    assign ptw_pte_i = pte_t'(data_rdata_i);

    enum logic[3:0] {
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
    logic is_instr_ptw_q, is_instr_ptw_n;

    assign ptw_active_o    = (ptw_state_q != PTW_READY);
    assign walking_instr_o = is_instr_ptw_q;

    // register the ASID
    logic [ASID_WIDTH-1:0] tlb_update_asid_q, tlb_update_asid_n;
    // register the VPN we need to walk
    logic [26:0] tlb_update_vpn_q, tlb_update_vpn_n;
    // 4 byte aligned physical pointer
    logic[45:0] ptw_pptr_q, ptw_pptr_n;
    // directly output the correct physical address
    assign address_o = {ptw_pptr_q, 4'b0};
    // update the correct page table level
    assign update_is_2M_o = (ptw_lvl_q == LVL2);
    assign update_is_1G_o = (ptw_lvl_q == LVL1);
    // output the correct VPN and ASID
    assign update_vpn_o  = tlb_update_vpn_q;
    assign update_asid_o = tlb_update_asid_q;

    assign update_content_o = ptw_pte_i;

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
        data_req_o        = 1'b0;
        ptw_error_o       = 1'b0;
        itlb_update_o     = 1'b0;
        dtlb_update_o     = 1'b0;
        is_instr_ptw_n    = is_instr_ptw_q;
        ptw_lvl_n         = ptw_lvl_q;
        ptw_pptr_n        = ptw_pptr_q;
        // input registers
        tlb_update_asid_n = tlb_update_asid_q;
        tlb_update_vpn_n  = tlb_update_vpn_q;

        unique case (ptw_state_q)

            PTW_READY: begin
                // if we got an ITLB miss
                if (enable_translation_i & itlb_access_i & itlb_miss_i & ~dtlb_access_i) begin
                    ptw_pptr_n          = {pd_ppn_i, itlb_vaddr_i[38:30]};
                    is_instr_ptw_n      = 1'b0;
                    tlb_update_asid_n   = asid_i;
                    tlb_update_vpn_n    = itlb_vaddr_i[38:12];
                    ptw_state_n         = PTW_WAIT_GRANT;
                // we got a DTLB miss
                end else if (enable_translation_i & dtlb_access_i & dtlb_miss_i) begin
                    ptw_pptr_n          = {pd_ppn_i, dtlb_vaddr_i[38:30]};
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
                    ptw_state_n = PTW_PTE_LOOKUP;
                end
                // we could potentially error out here
            end

            PTW_PTE_LOOKUP: begin
                // we wait for the valid signal
                if (data_rvalid_i) begin
                    if (ptw_lvl_q == LVL2)
                        ptw_pptr_n = {ptw_pte_i.ppn[17:9], tlb_update_vpn_q[17:9]};
                    if (ptw_lvl_q == LVL3)
                        ptw_pptr_n = {ptw_pte_i.ppn[8:0], tlb_update_vpn_q[8:0]};

                    // it is an invalid PTE
                    if (~ptw_pte_i.v | (~ptw_pte_i.r & ptw_pte_i.w)) begin
                        ptw_state_n = PTW_PROPAGATE_ERROR;
                    end else begin
                        ptw_state_n = PTW_READY;
                        // it is a valid PTE
                        if (ptw_pte_i.r | ptw_pte_i.x) begin
                            // Valid translation found (either 4M or 4K entry)
                            if (is_instr_ptw_q) begin
                                // Update instruction-TLB
                                // If page is not executable, we can directly raise an error. This
                                // saves the 'x' bits in the ITLB otherwise needed for access
                                // right checks and doesn't put a useless entry into the TLB.
                                if (~ptw_pte_i.x) begin
                                  ptw_state_n = PTW_PROPAGATE_ERROR;
                                end else begin
                                  itlb_update_o = 1'b1;
                                end
                            end else begin
                                // Update data-TLB
                                // If page is not readable (there are no write-only pages), or the
                                // access that triggered the PTW is a write, but the page is not
                                // writeable, we can directly raise an error. This saves the 'r'
                                // bits in the TLB otherwise needed for access right checks and
                                // doesn't put a useless entry into the TLB.
                                if (  (~ptw_pte_i.r & ~(ptw_pte_i.x & flag_mxr_i))
                                    | (~ptw_pte_i.w)) begin
                                  ptw_state_n   = PTW_PROPAGATE_ERROR;
                                end else begin
                                  dtlb_update_o = 1'b1;
                                end
                            end
                        end
                    end
                    // ~data_rvalid_i
                end else begin
                    // Pointer to next level of page table
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
            // TODO: propagate error
            PTW_PROPAGATE_ERROR: begin
                ptw_state_n = PTW_READY;
                ptw_error_o = 1'b1;
            end

            default:
                ptw_state_n = PTW_READY;

        endcase // ptw_state_q
    end

    // sequential process
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if(~rst_ni) begin
            ptw_state_q        <= PTW_READY;
            is_instr_ptw_q     <= 1'b0;
            ptw_lvl_q          <= LVL1;
            tlb_update_asid_q  <= '{default: 0};
            tlb_update_vpn_q   <= '{default: 0};
            ptw_pptr_q         <= '{default: 0};
        end else begin
            ptw_state_q        <= ptw_state_n;
            ptw_pptr_q         <= ptw_pptr_n;
            is_instr_ptw_q     <= is_instr_ptw_n;
            ptw_lvl_q          <= ptw_lvl_n;
            tlb_update_asid_q  <= tlb_update_asid_n;
            tlb_update_vpn_q   <= tlb_update_vpn_n;
        end
    end

endmodule