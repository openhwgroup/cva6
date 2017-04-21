// Author: Florian Zaruba, ETH Zurich - David Schaffenrath, TU Graz
// Date: 21.4.2017
// Description: Transaction Lookaside Buffer, SV39
//              fully set-associative
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

module tlb #(
      parameter int TLB_ENTRIES = 4,
      parameter int ASID_WIDTH = 1,
      parameter int CONTENT_SIZE = 24 // data: ppn + u + g + w + x_only , instr: ppn + u + g
  )
  (
    input logic                     clk_i,    // Clock
    input logic                     rst_ni,   // Asynchronous reset active low
    input  logic                    flush_i,  // Flush signal

    // Update signals
    input  logic                    update_is_2M_i,
    input  logic                    update_is_1G_i,
    input  logic [26:0]             update_vpn_i,
    input  logic [ASID_WIDTH-1:0]   update_asid_i,
    input  logic [CONTENT_SIZE-1:0] update_content_i,
    input  logic                    update_tlb_i,

    // Lookup signals
    input  logic                    lu_access_i,
    input  logic [ASID_WIDTH-1:0]   lu_asid_i,
    input  logic [63:0]             lu_vaddr_i,
    output logic [CONTENT_SIZE-1:0] lu_content_o,
    output logic                    lu_is_2M_o,
    output logic                    lu_is_1G_o,
    output logic                    lu_hit_o
);

    // SV39 defines three levels of page table
    struct packed {
      logic [ASID_WIDTH-1:0] asid;
      logic [8:0]            vpn2;
      logic [8:0]            vpn1;
      logic [8:0]            vpn0;
      logic                  is_2M;
      logic                  is_1G;
      logic                  valid;
    } [TLB_ENTRIES-1:0] tags_q, tags_n;

    logic [TLB_ENTRIES-1:0][CONTENT_SIZE-1:0] content_q, content_n;
    logic [8:0] vpn0, vpn1, vpn2;
    logic [TLB_ENTRIES-1:0] lu_hit; // to replacement logic
    logic [TLB_ENTRIES-1:0] replace_en; // replace the following entry, set by replacement strategy
    //-------------
    // Translation
    //-------------
    always_comb begin : translation
        vpn0 = lu_vaddr_i[20:12];
        vpn1 = lu_vaddr_i[29:21];
        vpn2 = lu_vaddr_i[38:30];

        // default assignment
        lu_hit       = '{default: 0};
        lu_hit_o     = 1'b0;
        lu_content_o = '{default: 0};

        for (int i = 0; i < TLB_ENTRIES; i++) begin
            // first level match, this may be a giga page, check the ASID flags as well
            if (tags_q[i].valid && (lu_asid_i == tags_q[i].asid)
            && vpn2 == tags_q[i].vpn2) begin
                // second level
                if (tags_q[i].is_1G) begin
                    lu_is_1G_o = 1'b1;;
                    lu_content_o = content_q[i];
                    lu_hit_o   = 1'b1;
                    lu_hit[i]  = 1'b1;
                // not a giga page hit so check further
                end else if (vpn1 == tags_q[i].vpn1) begin
                    // this could be a 2 mega page hit or a 4 kB hit
                    // output accordingly
                    if (tags_q[i].is_2M || vpn0 == tags_q[i].vpn0) begin
                        lu_is_2M_o   = tags_q[i].is_1G;
                        lu_content_o = content_q[i];
                        lu_hit_o     = 1'b1;
                        lu_hit[i]    = 1'b1;
                    end
                end
            end
        end
    end

    // ------------------
    // Update and Flush
    // ------------------
    always_comb begin : update_flush
        tags_n    = tags_q;
        content_n = content_q;

        for (int i = 0; i < TLB_ENTRIES; i++) begin
            if (flush_i) begin
                // invalidate logic
                if (lu_asid_i == 1'b0) // flush everything if ASID is 0
                    tags_n[i].valid = 1'b0;
                else if (lu_asid_i == tags_q[i].asid) // just flush entries from this ASID
                    tags_n[i].valid = 1'b0;

            // normal replacement
            end else if (update_tlb_i & replace_en[i]) begin
                // update tag array
                tags_n[i] = '{
                    asid: update_asid_i,
                    vpn2: update_vpn_i [26:18],
                    vpn1: update_vpn_i [17:9],
                    vpn0: update_vpn_i [8:0],
                    is_1G: update_is_1G_i,
                    is_2M: update_is_2M_i,
                    valid: 1'b1
                };
                // and content as well
                content_n[i] = content_q[i];
            end
        end
    end
    // -------
    // PLRU
    // -------

    // TODO: Implement
    // -----------------------------------------------
    // PLRU - Pseudo Least Recently Used Replacement
    // -----------------------------------------------

    always_ff @(posedge clk_i or negedge rst_ni) begin
        if(~rst_ni) begin
            tags_q    <= '{default: 0};
            content_q <= '{default: 0};
        end else begin
            tags_q    <= tags_n;
            content_q <= content_n;
        end
    end

endmodule