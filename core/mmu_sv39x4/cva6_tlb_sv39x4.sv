// Copyright (c) 2022  Bruno Sá and Zero-Day Labs.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Author: Bruno Sá
// Date: 14/08/2022
//
// Description: Translation Lookaside Buffer, Sv39x4 , fully set-associative
//              This module is an adaptation of the Sv39 TLB developed
//              by Florian Zaruba and David Schaffenrath to the Sv39x4 standard.


module cva6_tlb_sv39x4 import ariane_pkg::*; #(
      parameter int unsigned TLB_ENTRIES = 4,
      parameter int unsigned ASID_WIDTH  = 1,
      parameter int unsigned VMID_WIDTH  = 1
  )(
    input  logic                    clk_i,    // Clock
    input  logic                    rst_ni,   // Asynchronous reset active low
    input  logic                    flush_i,  // Flush normal translations signal
    input  logic                    flush_vvma_i,  // Flush vs stage signal
    input  logic                    flush_gvma_i,  // Flush g stage signal
    input  logic                    s_st_enbl_i,  // s-stage enabled
    input  logic                    g_st_enbl_i,  // g-stage enabled
    input  logic                    v_i,  // virtualization mode
    // Update TLB
    input  tlb_update_sv39x4_t      update_i,
    // Lookup signals
    input  logic                    lu_access_i,
    input  logic [ASID_WIDTH-1:0]   lu_asid_i,
    input  logic [VMID_WIDTH-1:0]   lu_vmid_i,
    input  logic [riscv::VLEN-1:0]  lu_vaddr_i,
    output logic [riscv::GPLEN-1:0] lu_gpaddr_o,
    output riscv::pte_t             lu_content_o,
    output riscv::pte_t             lu_g_content_o,
    input  logic [ASID_WIDTH-1:0]   asid_to_be_flushed_i,
    input  logic [VMID_WIDTH-1:0]   vmid_to_be_flushed_i,
    input  logic [riscv::VLEN-1:0]  vaddr_to_be_flushed_i,
    input  logic [riscv::GPLEN-1:0] gpaddr_to_be_flushed_i,
    output logic                    lu_is_2M_o,
    output logic                    lu_is_1G_o,
    output logic                    lu_hit_o
);

    // SV39 defines three levels of page tables
    struct packed {
      logic [ASID_WIDTH-1:0] asid;
      logic [VMID_WIDTH-1:0] vmid;
      logic [riscv::VPN2:0]  vpn2;
      logic [8:0]            vpn1;
      logic [8:0]            vpn0;
      logic [riscv::GPPN2:0] gppn2;
      logic [8:0]            gppn1;
      logic [8:0]            gppn0;
      logic                  is_2M;
      logic                  is_1G;
      logic                  is_s_2M;
      logic                  is_s_1G;
      logic                  is_g_2M;
      logic                  is_g_1G;
      logic                  s_st_enbl;   // s-stage translation
      logic                  g_st_enbl;   // g-stage translation
      logic                  v;           // virtualization mode
      logic                  valid;
    } [TLB_ENTRIES-1:0] tags_q, tags_n;

    struct packed {
      riscv::pte_t pte;
      riscv::pte_t gpte;
    } [TLB_ENTRIES-1:0] content_q, content_n;

    logic [8:0] vpn0, vpn1;
    logic [riscv::VPN2:0] vpn2;
    logic [riscv::GPPN2:0] gppn2;
    logic [TLB_ENTRIES-1:0] lu_hit;     // to replacement logic
    logic [TLB_ENTRIES-1:0] replace_en; // replace the following entry, set by replacement strategy
    logic [TLB_ENTRIES-1:0] match_vmid;
    logic [TLB_ENTRIES-1:0] match_asid;
    logic [TLB_ENTRIES-1:0] match_stage;
    logic [TLB_ENTRIES-1:0] match_pn;
    riscv::pte_t   g_content;
    //-------------
    // Translation
    //-------------
    always_comb begin : translation
        vpn0 = lu_vaddr_i[20:12];
        vpn1 = lu_vaddr_i[29:21];
        vpn2 = lu_vaddr_i[30+riscv::VPN2:30];
        gppn2 = lu_vaddr_i[30+riscv::GPPN2:30];

        // default assignment
        lu_hit       = '{default: 0};
        lu_hit_o     = 1'b0;
        lu_content_o = '{default: 0};
        lu_g_content_o = '{default: 0};
        lu_gpaddr_o  = '{default: 0};
        lu_is_1G_o   = 1'b0;
        lu_is_2M_o   = 1'b0;
        match_asid   = '{default: 0};
        match_vmid   = '{default: 0};
        match_stage  = '{default: 0};
        match_pn     = '{default: 0};

        for (int unsigned i = 0; i < TLB_ENTRIES; i++) begin
            // first level match, this may be a giga page, check the ASID and VMID flags as well if needed
            // if the entry is associated to a global address, don't match the ASID (ASID is don't care)
            match_asid[i] = (((lu_asid_i == tags_q[i].asid) || content_q[i].pte.g) && s_st_enbl_i) || !s_st_enbl_i;
            match_vmid[i] = (lu_vmid_i == tags_q[i].vmid && g_st_enbl_i) || !g_st_enbl_i;
            // check if translation is a: S-Stage and G-Stage, S-Stage only or G-Stage only translation and virtualization mode is on/off
            match_stage[i] = tags_q[i].g_st_enbl == g_st_enbl_i && tags_q[i].s_st_enbl == s_st_enbl_i && tags_q[i].v == v_i;
            match_pn[i] = (vpn2 == tags_q[i].vpn2 && s_st_enbl_i) || (gppn2 == tags_q[i].gppn2 && !s_st_enbl_i);
            if (tags_q[i].valid && match_asid[i] && match_vmid[i] && match_stage[i] && match_pn[i]) begin
                if (tags_q[i].is_1G) begin
                      lu_is_1G_o      = tags_q[i].is_1G;
                      lu_content_o    = content_q[i].pte;
                      lu_g_content_o  = content_q[i].gpte;
                      lu_gpaddr_o     = {tags_q[i].gppn2,lu_vaddr_i[29:0]};
                      lu_hit_o        = 1'b1;
                      lu_hit[i]       = 1'b1;
                // not a giga page hit so check further
                end else if (vpn1 == tags_q[i].vpn1) begin
                    // this could be a 2 mega page hit or a 4 kB hit
                    // output accordingly
                    if (tags_q[i].is_2M || vpn0 == tags_q[i].vpn0) begin
                            lu_is_2M_o     = tags_q[i].is_2M;
                            lu_gpaddr_o    = {content_q[i].pte.ppn, lu_vaddr_i[11:0]};
                            // Mega page
                            if (tags_q[i].is_s_2M) begin
                                lu_gpaddr_o[20:12] = lu_vaddr_i[20:12];
                            end
                            // Giga page
                            if (tags_q[i].is_s_1G) begin
                                lu_gpaddr_o[29:12] = lu_vaddr_i[29:12];
                            end
                            g_content      = content_q[i].gpte;
                            if(tags_q[i].is_g_2M)
                              g_content.ppn[8:0] = lu_gpaddr_o[20:12];
                            if(tags_q[i].is_g_1G)
                              g_content.ppn[17:0] = lu_gpaddr_o[29:12];
                            lu_content_o   = content_q[i].pte;
                            lu_g_content_o = g_content;
                            lu_hit_o       = 1'b1;
                            lu_hit[i]      = 1'b1;
                    end
                end
            end
        end
    end



    logic asid_to_be_flushed_is0;  // indicates that the ASID provided by SFENCE.VMA (rs2)is 0, active high
    logic vmid_to_be_flushed_is0;  // indicates that the VMID provided by HFENCE.GVMA (rs2)is 0, active high
    logic vaddr_to_be_flushed_is0;  // indicates that the VADDR provided by SFENCE.VMA (rs1)is 0, active high
    logic gpaddr_to_be_flushed_is0;  // indicates that the VADDR provided by SFENCE.VMA (rs1)is 0, active high
    logic  [TLB_ENTRIES-1:0] vaddr_vpn0_match;
    logic  [TLB_ENTRIES-1:0] vaddr_vpn1_match;
    logic  [TLB_ENTRIES-1:0] vaddr_vpn2_match;
    logic  [TLB_ENTRIES-1:0] gpaddr_gppn0_match;
    logic  [TLB_ENTRIES-1:0] gpaddr_gppn1_match;
    logic  [TLB_ENTRIES-1:0] gpaddr_gppn2_match;

    assign asid_to_be_flushed_is0 =  ~(|asid_to_be_flushed_i);
    assign vmid_to_be_flushed_is0 =  ~(|vmid_to_be_flushed_i);
    assign vaddr_to_be_flushed_is0 = ~(|vaddr_to_be_flushed_i);
    assign gpaddr_to_be_flushed_is0 = ~(|gpaddr_to_be_flushed_i);

	  // ------------------
    // Update and Flush
    // ------------------
    always_comb begin : update_flush
        tags_n    = tags_q;
        content_n = content_q;

        for (int unsigned i = 0; i < TLB_ENTRIES; i++) begin

            vaddr_vpn0_match[i] = (vaddr_to_be_flushed_i[20:12] == tags_q[i].vpn0);
            vaddr_vpn1_match[i] = (vaddr_to_be_flushed_i[29:21] == tags_q[i].vpn1);
            vaddr_vpn2_match[i] = (vaddr_to_be_flushed_i[30+riscv::VPN2:30] == tags_q[i].vpn2);

            gpaddr_gppn0_match[i] = (gpaddr_to_be_flushed_i[20:12] == tags_q[i].gppn0);
            gpaddr_gppn1_match[i] = (gpaddr_to_be_flushed_i[29:21] == tags_q[i].gppn1);
            gpaddr_gppn2_match[i] = (gpaddr_to_be_flushed_i[30+riscv::GPPN2:30] == tags_q[i].gppn2);

            if (flush_i) begin
                if(!tags_q[i].v && tags_q[i].s_st_enbl) begin
                    // invalidate logic
                    // flush everything if ASID is 0 and vaddr is 0 ("SFENCE.VMA x0 x0" case)
        				    if (asid_to_be_flushed_is0 && vaddr_to_be_flushed_is0 )
                        tags_n[i].valid = 1'b0;
                    // flush vaddr in all addressing space ("SFENCE.VMA vaddr x0" case), it should happen only for leaf pages
                    else if (asid_to_be_flushed_is0 && ((vaddr_vpn0_match[i] && vaddr_vpn1_match[i] && vaddr_vpn2_match[i]) || (vaddr_vpn2_match[i] && tags_q[i].is_1G) || (vaddr_vpn1_match[i] && vaddr_vpn2_match[i] && tags_q[i].is_2M) ) && (~vaddr_to_be_flushed_is0))
                        tags_n[i].valid = 1'b0;
                    // the entry is flushed if it's not global and asid and vaddr both matches with the entry to be flushed ("SFENCE.VMA vaddr asid" case)
				            else if ((!content_q[i].pte.g) && ((vaddr_vpn0_match[i] && vaddr_vpn1_match[i] && vaddr_vpn2_match[i]) || (vaddr_vpn2_match[i] && tags_q[i].is_1G) || (vaddr_vpn1_match[i] && vaddr_vpn2_match[i] && tags_q[i].is_2M)) && (asid_to_be_flushed_i == tags_q[i].asid) && (!vaddr_to_be_flushed_is0) && (!asid_to_be_flushed_is0))
				              	tags_n[i].valid = 1'b0;
                    // the entry is flushed if it's not global, and the asid matches and vaddr is 0. ("SFENCE.VMA 0 asid" case)
				            else if ((!content_q[i].pte.g) && (vaddr_to_be_flushed_is0) && (asid_to_be_flushed_i == tags_q[i].asid) && (!asid_to_be_flushed_is0))
				            	  tags_n[i].valid = 1'b0;
                end
            end else if (flush_vvma_i) begin
                if(tags_q[i].v && tags_q[i].s_st_enbl) begin
                    // invalidate logic
                    // flush everything if ASID is 0 and vaddr is 0 ("SFENCE.VMA x0 x0" case)
        				    if (asid_to_be_flushed_is0 && vaddr_to_be_flushed_is0 && ((tags_q[i].g_st_enbl && lu_vmid_i == tags_q[i].vmid) || !tags_q[i].g_st_enbl))
                        tags_n[i].valid = 1'b0;
                    // flush vaddr in all addressing space ("SFENCE.VMA vaddr x0" case), it should happen only for leaf pages
                    else if (asid_to_be_flushed_is0 && ((vaddr_vpn0_match[i] && vaddr_vpn1_match[i] && vaddr_vpn2_match[i]) || (vaddr_vpn2_match[i] && tags_q[i].is_s_1G) || (vaddr_vpn1_match[i] && vaddr_vpn2_match[i] && tags_q[i].is_s_2M) ) && (~vaddr_to_be_flushed_is0) && ((tags_q[i].g_st_enbl && lu_vmid_i == tags_q[i].vmid) || !tags_q[i].g_st_enbl))
                        tags_n[i].valid = 1'b0;
                    // the entry is flushed if it's not global and asid and vaddr both matches with the entry to be flushed ("SFENCE.VMA vaddr asid" case)
				            else if ((!content_q[i].pte.g) && ((vaddr_vpn0_match[i] && vaddr_vpn1_match[i] && vaddr_vpn2_match[i]) || (vaddr_vpn2_match[i] && tags_q[i].is_s_1G) || (vaddr_vpn1_match[i] && vaddr_vpn2_match[i] && tags_q[i].is_s_2M)) && (asid_to_be_flushed_i == tags_q[i].asid && ((tags_q[i].g_st_enbl && lu_vmid_i == tags_q[i].vmid) || !tags_q[i].g_st_enbl)) && (!vaddr_to_be_flushed_is0) && (!asid_to_be_flushed_is0))
				              	tags_n[i].valid = 1'b0;
                    // the entry is flushed if it's not global, and the asid matches and vaddr is 0. ("SFENCE.VMA 0 asid" case)
				            else if ((!content_q[i].pte.g) && (vaddr_to_be_flushed_is0) && (asid_to_be_flushed_i == tags_q[i].asid && ((tags_q[i].g_st_enbl && lu_vmid_i == tags_q[i].vmid) || !tags_q[i].g_st_enbl)) && (!asid_to_be_flushed_is0))
				            	  tags_n[i].valid = 1'b0;
                end
            end else if (flush_gvma_i) begin
                if(tags_q[i].g_st_enbl) begin
                    // invalidate logic
                    // flush everything if VMID is 0 and addr is 0 ("HFENCE.GVMA x0 x0" case)
        				    if (vmid_to_be_flushed_is0 && gpaddr_to_be_flushed_is0 )
                        tags_n[i].valid = 1'b0;
                    // flush gpaddr in all addressing space ("HFENCE.GVMA gpaddr x0" case), it should happen only for leaf pages
                    else if (vmid_to_be_flushed_is0 && ((gpaddr_gppn0_match[i] && gpaddr_gppn1_match[i] && gpaddr_gppn2_match[i]) || (gpaddr_gppn2_match[i] && tags_q[i].is_g_1G) || (gpaddr_gppn1_match[i] && gpaddr_gppn2_match[i] && tags_q[i].is_g_2M) ) && (~gpaddr_to_be_flushed_is0))
                        tags_n[i].valid = 1'b0;
                    // the entry asid and gpaddr both matches with the entry to be flushed ("HFENCE.GVMA gpaddr vmid" case)
				            else if (((gpaddr_gppn0_match[i] && gpaddr_gppn1_match[i] && gpaddr_gppn2_match[i]) || (gpaddr_gppn2_match[i] && tags_q[i].is_g_1G) || (gpaddr_gppn1_match[i] && gpaddr_gppn2_match[i] && tags_q[i].is_g_2M)) && (vmid_to_be_flushed_i == tags_q[i].vmid) && (~gpaddr_to_be_flushed_is0) && (~vmid_to_be_flushed_is0))
				              	tags_n[i].valid = 1'b0;
                    // the entry is flushed if it's not global, and the vmid matches and gpaddr is 0. ("HFENCE.GVMA 0 vmid" case)
				            else if ((gpaddr_to_be_flushed_is0) && (vmid_to_be_flushed_i == tags_q[i].vmid) && (!vmid_to_be_flushed_is0))
				            	  tags_n[i].valid = 1'b0;
                end
            // normal replacement
            end else if (update_i.valid & replace_en[i]) begin
                // update tag array
                tags_n[i] = '{
                    asid:  s_st_enbl_i ? update_i.asid : 'b0,
                    vmid:  g_st_enbl_i ? update_i.vmid : 'b0,
                    vpn2:  update_i.vpn [18+riscv::VPN2:18],
                    vpn1:  update_i.vpn [17:9],
                    vpn0:  update_i.vpn [8:0],
                    gppn2:  update_i.gppn [20+riscv::VPN2:18],
                    gppn1:  update_i.gppn [17:9],
                    gppn0:  update_i.gppn [8:0],
                    s_st_enbl:  s_st_enbl_i,
                    g_st_enbl:  g_st_enbl_i,
                    v:     v_i,
                    is_1G: update_i.is_1G,
                    is_2M: update_i.is_2M,
                    is_s_1G: update_i.is_s_1G,
                    is_s_2M: update_i.is_s_2M,
                    is_g_1G: update_i.is_g_1G,
                    is_g_2M: update_i.is_g_2M,
                    valid: 1'b1
                };
                // and content as well
                content_n[i].pte  = update_i.content;
                content_n[i].gpte = update_i.g_content;
            end
        end
    end

    // -----------------------------------------------
    // PLRU - Pseudo Least Recently Used Replacement
    // -----------------------------------------------
    logic[2*(TLB_ENTRIES-1)-1:0] plru_tree_q, plru_tree_n;
    always_comb begin : plru_replacement
        plru_tree_n = plru_tree_q;
        // The PLRU-tree indexing:
        // lvl0        0
        //            / \
        //           /   \
        // lvl1     1     2
        //         / \   / \
        // lvl2   3   4 5   6
        //       / \ /\/\  /\
        //      ... ... ... ...
        // Just predefine which nodes will be set/cleared
        // E.g. for a TLB with 8 entries, the for-loop is semantically
        // equivalent to the following pseudo-code:
        // unique case (1'b1)
        // lu_hit[7]: plru_tree_n[0, 2, 6] = {1, 1, 1};
        // lu_hit[6]: plru_tree_n[0, 2, 6] = {1, 1, 0};
        // lu_hit[5]: plru_tree_n[0, 2, 5] = {1, 0, 1};
        // lu_hit[4]: plru_tree_n[0, 2, 5] = {1, 0, 0};
        // lu_hit[3]: plru_tree_n[0, 1, 4] = {0, 1, 1};
        // lu_hit[2]: plru_tree_n[0, 1, 4] = {0, 1, 0};
        // lu_hit[1]: plru_tree_n[0, 1, 3] = {0, 0, 1};
        // lu_hit[0]: plru_tree_n[0, 1, 3] = {0, 0, 0};
        // default: begin /* No hit */ end
        // endcase
        for (int unsigned i = 0; i < TLB_ENTRIES; i++) begin
            automatic int unsigned idx_base, shift, new_index;
            // we got a hit so update the pointer as it was least recently used
            if (lu_hit[i] & lu_access_i) begin
                // Set the nodes to the values we would expect
                for (int unsigned lvl = 0; lvl < $clog2(TLB_ENTRIES); lvl++) begin
                  idx_base = $unsigned((2**lvl)-1);
                  // lvl0 <=> MSB, lvl1 <=> MSB-1, ...
                  shift = $clog2(TLB_ENTRIES) - lvl;
                  // to circumvent the 32 bit integer arithmetic assignment
                  new_index =  ~((i >> (shift-1)) & 32'b1);
                  plru_tree_n[idx_base + (i >> shift)] = new_index[0];
                end
            end
        end
        // Decode tree to write enable signals
        // Next for-loop basically creates the following logic for e.g. an 8 entry
        // TLB (note: pseudo-code obviously):
        // replace_en[7] = &plru_tree_q[ 6, 2, 0]; //plru_tree_q[0,2,6]=={1,1,1}
        // replace_en[6] = &plru_tree_q[~6, 2, 0]; //plru_tree_q[0,2,6]=={1,1,0}
        // replace_en[5] = &plru_tree_q[ 5,~2, 0]; //plru_tree_q[0,2,5]=={1,0,1}
        // replace_en[4] = &plru_tree_q[~5,~2, 0]; //plru_tree_q[0,2,5]=={1,0,0}
        // replace_en[3] = &plru_tree_q[ 4, 1,~0]; //plru_tree_q[0,1,4]=={0,1,1}
        // replace_en[2] = &plru_tree_q[~4, 1,~0]; //plru_tree_q[0,1,4]=={0,1,0}
        // replace_en[1] = &plru_tree_q[ 3,~1,~0]; //plru_tree_q[0,1,3]=={0,0,1}
        // replace_en[0] = &plru_tree_q[~3,~1,~0]; //plru_tree_q[0,1,3]=={0,0,0}
        // For each entry traverse the tree. If every tree-node matches,
        // the corresponding bit of the entry's index, this is
        // the next entry to replace.
        for (int unsigned i = 0; i < TLB_ENTRIES; i += 1) begin
            automatic logic en;
            automatic int unsigned idx_base, shift, new_index;
            en = 1'b1;
            for (int unsigned lvl = 0; lvl < $clog2(TLB_ENTRIES); lvl++) begin
                idx_base = $unsigned((2**lvl)-1);
                // lvl0 <=> MSB, lvl1 <=> MSB-1, ...
                shift = $clog2(TLB_ENTRIES) - lvl;

                // en &= plru_tree_q[idx_base + (i>>shift)] == ((i >> (shift-1)) & 1'b1);
                new_index =  (i >> (shift-1)) & 32'b1;
                if (new_index[0]) begin
                  en &= plru_tree_q[idx_base + (i>>shift)];
                end else begin
                  en &= ~plru_tree_q[idx_base + (i>>shift)];
                end
            end
            replace_en[i] = en;
        end
    end

    // sequential process
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if(~rst_ni) begin
            tags_q      <= '{default: 0};
            content_q   <= '{default: 0};
            plru_tree_q <= '{default: 0};
        end else begin
            tags_q      <= tags_n;
            content_q   <= content_n;
            plru_tree_q <= plru_tree_n;
        end
    end
    //--------------
    // Sanity checks
    //--------------

    //pragma translate_off
    `ifndef VERILATOR

    initial begin : p_assertions
      assert ((TLB_ENTRIES % 2 == 0) && (TLB_ENTRIES > 1))
        else begin $error("TLB size must be a multiple of 2 and greater than 1"); $stop(); end
      assert (ASID_WIDTH >= 1)
        else begin $error("ASID width must be at least 1"); $stop(); end
    end

    // Just for checking
    function int countSetBits(logic[TLB_ENTRIES-1:0] vector);
      automatic int count = 0;
      foreach (vector[idx]) begin
        count += vector[idx];
      end
      return count;
    endfunction

    assert property (@(posedge clk_i)(countSetBits(lu_hit) <= 1))
      else begin $error("More then one hit in TLB!"); $stop(); end
    assert property (@(posedge clk_i)(countSetBits(replace_en) <= 1))
      else begin $error("More then one TLB entry selected for next replace!"); $stop(); end

    `endif
    //pragma translate_on

endmodule
