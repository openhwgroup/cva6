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
      parameter int DATA_TLB_ENTRIES  = 4,
      parameter int ASID_WIDTH        = 1
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
        output logic [31:0]                     fetch_rdata_o,  // pass-through because of interfaces
        output exception                        fetch_ex_o,     // write-back fetch exceptions (e.g.: bus faults, page faults, etc.)
        // LSU interface
        // this is a more minimalistic interface because the actual addressing logic is handled
        // in the LSU as we distinguish load and stores, what we do here is simple address translation
        input  exception                        misaligned_ex_i,
        input  logic                            lsu_req_i,
        input  logic [63:0]                     lsu_vaddr_i,
        // if we need to walk the page table we can't grant in the same cycle
        output logic                            lsu_valid_o, // translation is valid
        output logic [63:0]                     lsu_paddr_o, // translated address
        output exception                        lsu_exception_o,
        // General control signals
        input priv_lvl_t                        priv_lvl_i,
        input logic                             flag_pum_i,
        input logic                             flag_mxr_i,
        // input logic flag_mprv_i,
        input logic [37:0]                      pd_ppn_i,
        input logic [ASID_WIDTH-1:0]            asid_i,
        input logic                             flush_tlb_i,
        // Memory interfaces
        // Instruction memory/cache
        output logic [63:0]                     instr_if_address_o,
        output logic                            instr_if_data_req_o,
        output logic [3:0]                      instr_if_data_be_o,
        input  logic                            instr_if_data_gnt_i,
        input  logic                            instr_if_data_rvalid_i,
        input  logic [31:0]                     instr_if_data_rdata_i,
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
    // assignments necessary to use interfaces here
    // only done for the few signals of the instruction interface
    logic [63:0] fetch_paddr;

    logic  fetch_req;
    assign instr_if_data_req_o       = fetch_req;
    assign instr_if_address_o        = fetch_paddr;
    assign fetch_rdata_o             = instr_if_data_rdata_i;
    // instruction error
    logic ierr_valid_q, ierr_valid_n;
    logic iaccess_err;
    logic ptw_active;
    logic walking_instr;
    logic ptw_error;

    logic update_is_2M;
    logic update_is_1G;
    logic [26:0] update_vpn;
    logic [0:0] update_asid;
    pte_t update_content;

    logic itlb_update;
    logic itlb_lu_access;
    pte_t itlb_content;

    logic itlb_is_2M;
    logic itlb_is_1G;
    logic itlb_lu_hit;

    logic dtlb_update;
    logic dtlb_lu_access;
    pte_t dtlb_content;

    logic dtlb_is_2M;
    logic dtlb_is_1G;
    logic dtlb_lu_hit;

    tlb #(
        .TLB_ENTRIES      ( INSTR_TLB_ENTRIES          ),
        .ASID_WIDTH       ( ASID_WIDTH                 )
    ) itlb_i (
        .clk_i            ( clk_i                      ),
        .rst_ni           ( rst_ni                     ),
        .flush_i          ( flush_tlb_i                ),
        .update_is_2M_i   ( update_is_2M               ),
        .update_is_1G_i   ( update_is_1G               ),
        .update_vpn_i     ( update_vpn                 ),
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
        .update_vpn_i     ( update_vpn                  ),
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
        .flush_i                ( flush_tlb_i           ),
        .ptw_active_o           ( ptw_active            ),
        .walking_instr_o        ( walking_instr         ),
        .ptw_error_o            ( ptw_error             ),
        .enable_translation_i   ( enable_translation_i  ),

        .itlb_update_o          ( itlb_update           ),
        .dtlb_update_o          ( dtlb_update           ),
        .update_content_o       ( update_content        ),
        .update_is_2M_o         ( update_is_2M          ),
        .update_is_1G_o         ( update_is_1G          ),
        .update_vpn_o           ( update_vpn            ),
        .update_asid_o          ( update_asid           ),

        .itlb_access_i          ( itlb_lu_access        ),
        .itlb_miss_i            ( ~itlb_lu_hit          ),
        .itlb_vaddr_i           ( fetch_vaddr_i         ),

        .dtlb_access_i          ( dtlb_lu_access        ),
        .dtlb_miss_i            ( ~dtlb_lu_hit          ),
        .dtlb_vaddr_i           ( lsu_vaddr_i           ),

        .*
     );

    assign itlb_lu_access = fetch_req_i;
    assign dtlb_lu_access = lsu_req_i;
    assign iaccess_err = fetch_req_i & (
                     ((priv_lvl_i == PRIV_LVL_U) & ~itlb_content.u)
                   | (flag_pum_i & (priv_lvl_i == PRIV_LVL_S) & itlb_content.u)
                   );

    //-----------------------
    // Instruction interface
    //-----------------------
    always_comb begin : instr_interface
        // MMU disabled: just pass through
        automatic logic fetch_valid   = instr_if_data_rvalid_i;
        fetch_req                     = fetch_req_i;
        fetch_paddr                   = fetch_vaddr_i;
        fetch_gnt_o                   = instr_if_data_gnt_i;
        fetch_err_o                   = 1'b0;
        ierr_valid_n                  = 1'b0;
        fetch_ex_o                    = '{default: 0};

        // MMU enabled: address from TLB, request delayed until hit. Error when TLB
        // hit and no access right or TLB hit and translated address not valid (e.g.
        // AXI decode error), or when PTW performs walk due to itlb miss and raises
        // an error.
        if (enable_translation_i) begin
            fetch_req = 1'b0;
            /* verilator lint_off WIDTH */
            fetch_paddr = {itlb_content.ppn, fetch_vaddr_i[11:0]};
            /* verilator lint_on WIDTH */
            if (itlb_is_2M) begin
              fetch_paddr[20:12] = fetch_vaddr_i[20:12];
            end

            if (itlb_is_1G) begin
                fetch_paddr[29:12] = fetch_vaddr_i[29:12];
            end

            fetch_gnt_o = instr_if_data_gnt_i;

            // TODO the following two ifs should be mutually exclusive
            if (itlb_lu_hit) begin
              fetch_req = fetch_req_i;
              if (iaccess_err) begin
                // Play through an instruction fetch with error signaled with rvalid
                fetch_req    = 1'b0;
                fetch_gnt_o  = 1'b1;  // immediate grant
                //fetch_valid = 1'b0; NOTE: valid from previous fetch: pass through
                // NOTE: back-to-back transfers: We only get a request if previous
                //       transfer is completed, or completes in this cycle)
                ierr_valid_n = 1'b1; // valid signaled in next cycle
              end
            end
            if (ptw_active & walking_instr) begin
              // On error pass through fetch with error signaled with valid
              fetch_gnt_o  = ptw_error;
              ierr_valid_n = ptw_error; // signal valid/error on next cycle
            end
        end
        fetch_err_o = ierr_valid_q;
        fetch_valid_o = fetch_valid || ierr_valid_q;
    end

    // registers
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if(~rst_ni) begin
            ierr_valid_q <= 1'b0;
        end else begin
            ierr_valid_q <= ierr_valid_n;
        end
    end

    //-----------------------
    // Data interface
    //-----------------------
    always_comb begin : data_interface
        // stub
        // lsu_req_i
        // lsu_vaddr_i
        // lsu_valid_o
        // lsu_paddr_o
        lsu_paddr_o = (enable_translation_i) ? {16'b0, dtlb_content} : lsu_vaddr_i;
        lsu_valid_o = lsu_req_i;
        // TODO: Assign access exception
        lsu_exception_o = misaligned_ex_i;
    end

endmodule