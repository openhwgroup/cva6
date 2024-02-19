// Copyright (c) 2021 Thales.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Author: Angela Gonzalez PlanV Technology
// Date: 20/11/2023
//
// Description: Translation Lookaside Buffer, parameterizable to Sv32 or Sv39 , 
//              or sv39x4 fully set-associative
//              This module is an merge of the Sv32 TLB developed by Sebastien
//              Jacq (Thales Research & Technology), the Sv39 TLB developed
//              by Florian Zaruba and David Schaffenrath and the Sv39x4 by Bruno Sá.
//
// =========================================================================== //
// Revisions  :
// Date        Version  Author       Description
// 2024-01-25  0.2      A.Gonzalez   Generic TLB for CVA6 with Hypervisor support
// =========================================================================== //
module cva6_tlb import ariane_pkg::*; #(
  parameter type pte_cva6_t = logic,
  parameter type tlb_update_cva6_t = logic,
  parameter int unsigned TLB_ENTRIES = 4,
  parameter int unsigned HYP_EXT = 0,
  parameter int unsigned ASID_WIDTH [HYP_EXT:0] = {1}, //[vmid_width,asid_width]
  parameter int unsigned VPN_LEN = 1,
  parameter int unsigned PT_LEVELS = 1
)(
input  logic                    clk_i,    // Clock
input  logic                    rst_ni,   // Asynchronous reset active low
input  logic      [HYP_EXT*2:0] flush_i,  // Flush signal [g_stage,vs stage, normal translation signal]
input  logic      [HYP_EXT*2:0] v_st_enbl_i,  // v_i,g-stage enabled, s-stage enabled
// Update TLB
input  tlb_update_cva6_t        update_i,
// Lookup signals
input  logic                    lu_access_i,
input  logic [ASID_WIDTH[0]-1:0] lu_asid_i [HYP_EXT:0], //[lu_vmid,lu_asid]
input  logic [riscv::VLEN-1:0]  lu_vaddr_i,
output logic [riscv::GPLEN-1:0] lu_gpaddr_o,
output pte_cva6_t [HYP_EXT:0]   lu_content_o,
input  logic [ASID_WIDTH[0]-1:0] asid_to_be_flushed_i [HYP_EXT:0], //[vmid,asid]
input logic [riscv::VLEN-1:0]   vaddr_to_be_flushed_i [HYP_EXT:0], // [gpaddr,vaddr]
output logic [PT_LEVELS-2:0]    lu_is_page_o,
output logic                    lu_hit_o
);

  // computes the paddr based on the page size, ppn and offset
function automatic logic [(riscv::GPLEN-1):0] make_gpaddr(
    input logic s_st_enbl, input logic is_1G, input logic is_2M, 
    input logic [(riscv::VLEN-1):0] vaddr, input riscv::pte_t pte);
  logic [(riscv::GPLEN-1):0] gpaddr;
  if (s_st_enbl) begin
      gpaddr = {pte.ppn[(riscv::GPPNW-1):0], vaddr[11:0]};
      // Giga page
      if (is_1G) gpaddr[29:12] = vaddr[29:12];
      // Mega page
      if (is_2M) gpaddr[20:12] = vaddr[20:12];
  end else begin
      gpaddr = vaddr[(riscv::GPLEN-1):0];
  end
return gpaddr;
endfunction : make_gpaddr

// computes the final gppn based on the guest physical address
function automatic logic [(riscv::GPPNW-1):0] make_gppn(
    input logic s_st_enbl, input logic is_1G, input logic is_2M, 
    input logic [28:0] vpn, input riscv::pte_t pte);
  logic [(riscv::GPPNW-1):0] gppn;
  if (s_st_enbl) begin
      gppn = pte.ppn[(riscv::GPPNW-1):0];
      if(is_2M)
          gppn[8:0] = vpn[8:0];
      if(is_1G)
          gppn[17:0] = vpn[17:0];
  end else begin
      gppn = vpn;
  end
return gppn;
endfunction : make_gppn

// SV39 defines three levels of page tables
struct packed {
logic [HYP_EXT:0][ASID_WIDTH[0]-1:0]                        asid;   
logic [PT_LEVELS+HYP_EXT-1:0][(VPN_LEN/PT_LEVELS)-1:0] vpn;   
logic [PT_LEVELS-2:0][HYP_EXT:0]                       is_page;
logic [HYP_EXT*2:0]                                    v_st_enbl; // v_i,g-stage enabled, s-stage enabled
logic                                                  valid;
} [TLB_ENTRIES-1:0] tags_q, tags_n;

pte_cva6_t [TLB_ENTRIES-1:0][HYP_EXT:0] content_q , content_n;

logic [TLB_ENTRIES-1:0][PT_LEVELS-1:0] vpn_match;
logic [TLB_ENTRIES-1:0][PT_LEVELS-1:0] level_match;
logic [TLB_ENTRIES-1:0][HYP_EXT:0][PT_LEVELS-1:0] vaddr_vpn_match;
logic [TLB_ENTRIES-1:0][HYP_EXT:0][PT_LEVELS-1:0] vaddr_level_match;
logic [TLB_ENTRIES-1:0] lu_hit;     // to replacement logic
logic [TLB_ENTRIES-1:0] replace_en; // replace the following entry, set by replacement strategy
logic [TLB_ENTRIES-1:0][HYP_EXT:0] match_asid;
logic [TLB_ENTRIES-1:0][PT_LEVELS-1:0] page_match;
logic [TLB_ENTRIES-1:0][HYP_EXT:0][PT_LEVELS-1:0] vpage_match;
logic [TLB_ENTRIES-1:0][PT_LEVELS-2:0] is_page_o;
logic [TLB_ENTRIES-1:0] match_stage,tag_valid;
pte_cva6_t  g_content;
logic  [TLB_ENTRIES-1:0] [(riscv::GPPNW-1):0] gppn;
logic      [HYP_EXT*2:0] v_st_enbl;

assign v_st_enbl = (HYP_EXT==1) ? v_st_enbl_i : '1;
//-------------
// Translation
//-------------

genvar i,x,z,w;
generate
for (i=0; i < TLB_ENTRIES; i++) begin
  for (x=0; x < PT_LEVELS; x++) begin 
    //identify page_match for all TLB Entries  
    assign page_match[i][x] = x==0 ? 1 :((HYP_EXT==0 || x==(PT_LEVELS-1)) ? // PAGE_MATCH CONTAINS THE MATCH INFORMATION FOR EACH TAG OF is_1G and is_2M in sv39x4. HIGHER LEVEL (Giga page), THEN THERE IS THE Mega page AND AT THE LOWER LEVEL IS ALWAYS 1
                                            &(tags_q[i].is_page[PT_LEVELS-1-x] | (~v_st_enbl[HYP_EXT:0])):
                                            ((&v_st_enbl[HYP_EXT:0]) ? 
                                            ((tags_q[i].is_page[PT_LEVELS-1-x][0] && (tags_q[i].is_page[PT_LEVELS-2-x][HYP_EXT] || tags_q[i].is_page[PT_LEVELS-1-x][HYP_EXT])) 
                                          || (tags_q[i].is_page[PT_LEVELS-1-x][HYP_EXT] && (tags_q[i].is_page[PT_LEVELS-2-x][0] || tags_q[i].is_page[PT_LEVELS-1-x][0]))):
                                              tags_q[i].is_page[PT_LEVELS-1-x][0] && v_st_enbl[0] || tags_q[i].is_page[PT_LEVELS-1-x][HYP_EXT] && v_st_enbl[HYP_EXT]));

    //identify if vpn matches at all PT levels for all TLB entries  
    assign vpn_match[i][x]        = (HYP_EXT==1 && x==(PT_LEVELS-1) && ~v_st_enbl[0]) ? //
                                    lu_vaddr_i[12+((VPN_LEN/PT_LEVELS)*(x+1))-1:12+((VPN_LEN/PT_LEVELS)*x)] == tags_q[i].vpn[x] && lu_vaddr_i[12+VPN_LEN-1: 12+VPN_LEN-(VPN_LEN%PT_LEVELS)] == tags_q[i].vpn[x+1][(VPN_LEN%PT_LEVELS)-1:0]: //
                                    lu_vaddr_i[12+((VPN_LEN/PT_LEVELS)*(x+1))-1:12+((VPN_LEN/PT_LEVELS)*x)] == tags_q[i].vpn[x];
    
    //identify if there is a hit at each PT level for all TLB entries  
    assign level_match[i][x]      = &vpn_match[i][PT_LEVELS-1:x] && page_match[i][x];

    //identify vpage_match for all TLB Entries and vaddr_level match (if there is a hit at each PT level for all TLB entries on the vaddr)
    for(z=0;z<HYP_EXT+1;z++) begin
      assign vpage_match[i][z][x] = x==0 ? 1 :tags_q[i].is_page[PT_LEVELS-1-x][z];
      assign vaddr_level_match[i][z][x]= &vaddr_vpn_match[i][z][PT_LEVELS-1:x] && vpage_match[i][z][x];
          
    end
    //identify if virtual address vpn matches at all PT levels for all TLB entries 
    assign vaddr_vpn_match[i][0][x]  = vaddr_to_be_flushed_i[0][12+((VPN_LEN/PT_LEVELS)*(x+1))-1:12+((VPN_LEN/PT_LEVELS)*x)] == tags_q[i].vpn[x];

    //update vpn field in tags_n for each TLB when the update is valid and the tag needs to be replaced          
    assign tags_n[i].vpn[x]       = ((~(|flush_i)) && update_i.valid && replace_en[i] && !lu_hit_o) ? update_i.vpn[(1+x)*(VPN_LEN/PT_LEVELS)-1:x*(VPN_LEN/PT_LEVELS)] : tags_q[i].vpn[x];
    
  end

  assign tags_n[i].asid       = ((~(|flush_i)) && update_i.valid && replace_en[i] && !lu_hit_o) ? update_i.asid    : tags_q[i].asid;
  assign tags_n[i].is_page    = ((~(|flush_i)) && update_i.valid && replace_en[i] && !lu_hit_o) ? update_i.is_page : tags_q[i].is_page;

  assign tags_n[i].v_st_enbl  = ((~(|flush_i)) && update_i.valid && replace_en[i] && !lu_hit_o) ? update_i.v_st_enbl: tags_q[i].v_st_enbl;
  assign tags_n[i].valid      = ((~(|flush_i)) && update_i.valid && replace_en[i] && !lu_hit_o) ? 1'b1           : tag_valid[i];
  

  if(HYP_EXT==1) begin 
    //THIS UPDATES THE EXTRA BITS OF VPN IN SV39x4
    assign tags_n[i].vpn[PT_LEVELS][(VPN_LEN%PT_LEVELS)-1:0] =((~(|flush_i)) && update_i.valid && replace_en[i] && !lu_hit_o) ? update_i.vpn[VPN_LEN-1: VPN_LEN-(VPN_LEN%PT_LEVELS)] : tags_q[i].vpn[PT_LEVELS][(VPN_LEN%PT_LEVELS)-1:0];         
    //identify if GPADDR matches the GPPN
    assign vaddr_vpn_match[i][HYP_EXT][0] = (vaddr_to_be_flushed_i[HYP_EXT][20:12] == gppn[i][8:0]);
    assign vaddr_vpn_match[i][HYP_EXT][HYP_EXT] = (vaddr_to_be_flushed_i[HYP_EXT][29:21] == gppn[i][17:9]);
    assign vaddr_vpn_match[i][HYP_EXT][HYP_EXT*2] = (vaddr_to_be_flushed_i[HYP_EXT][30+riscv::GPPN2:30] == gppn[i][18+riscv::GPPN2:18]);
  
  end

  for (w=0; w < PT_LEVELS - 1; w++) begin  
    assign is_page_o[i][w] = page_match[i][PT_LEVELS - 1 - w]; //THIS REORGANIZES THE PAGES TO MATCH THE OUTPUT STRUCTURE (2M,1G)
  end
end
endgenerate

always_comb begin : translation

  // default assignment
  lu_hit         = '{default: 0};
  lu_hit_o       = 1'b0;
  lu_content_o   = '{default: 0};
  lu_is_page_o   = '{default: 0};
  match_asid     = '{default: 0};
  match_stage    = '{default: 0};
  g_content      = '{default: 0};
  lu_gpaddr_o    = '{default: 0};


  for (int unsigned i = 0; i < TLB_ENTRIES; i++) begin
      // first level match, this may be a giga page, check the ASID flags as well
      // if the entry is associated to a global address, don't match the ASID (ASID is don't care)
      match_asid[i][0] = (((lu_asid_i[0][ASID_WIDTH[0]-1:0] == tags_q[i].asid[0][ASID_WIDTH[0]-1:0]) || content_q[i][0].g) && v_st_enbl[0]) || !v_st_enbl[0];

      if(HYP_EXT==1) begin
        match_asid[i][HYP_EXT] = (lu_asid_i[HYP_EXT][ASID_WIDTH[HYP_EXT]-1:0] == tags_q[i].asid[HYP_EXT][ASID_WIDTH[HYP_EXT]-1:0] && v_st_enbl[HYP_EXT]) || !v_st_enbl[HYP_EXT];
      end
      
      // check if translation is a: S-Stage and G-Stage, S-Stage only or G-Stage only translation and virtualization mode is on/off
      match_stage[i] = tags_q[i].v_st_enbl == v_st_enbl;

      if (tags_q[i].valid && &match_asid[i] && match_stage[i]) begin

        if(HYP_EXT==1 && vpn_match[i][HYP_EXT*2])
          lu_gpaddr_o = make_gpaddr(v_st_enbl[0], tags_q[i].is_page[0][0], tags_q[i].is_page[1][0], lu_vaddr_i, content_q[i][0]);

        if (|level_match[i]) begin
              lu_is_page_o      = is_page_o[i];
              lu_content_o    = content_q[i];
              lu_hit_o        = 1'b1;
              lu_hit[i]       = 1'b1;

          if(HYP_EXT==1) begin
            // Compute G-Stage PPN based on the gpaddr
            g_content = content_q[i][HYP_EXT];
            if(tags_q[i].is_page[HYP_EXT][HYP_EXT])
                g_content.ppn[8:0] = lu_gpaddr_o[20:12];
            if(tags_q[i].is_page[0][HYP_EXT])
                g_content.ppn[17:0] = lu_gpaddr_o[29:12];
            // Output G-stage and S-stage content
            lu_content_o[HYP_EXT] = level_match[i][PT_LEVELS-1] ? content_q[i][HYP_EXT]:g_content;
          end
        end
      end
  end
end



logic [HYP_EXT:0]asid_to_be_flushed_is0;  // indicates that the ASID provided by SFENCE.VMA (rs2)is 0, active high
logic [HYP_EXT:0] vaddr_to_be_flushed_is0;  // indicates that the VADDR provided by SFENCE.VMA (rs1)is 0, active high

localparam int unsigned VADDR_WIDTH [1:0] = {riscv::GPLEN,riscv::VLEN};

genvar a;
  generate
      for(a=0;a<HYP_EXT+1;a++) begin
          assign asid_to_be_flushed_is0[a]  = ~(|asid_to_be_flushed_i[a][ASID_WIDTH[a]-1:0]);
          assign vaddr_to_be_flushed_is0[a] = ~(|vaddr_to_be_flushed_i[a][VADDR_WIDTH[a]-1:0]);
      end
  endgenerate 

// ------------------
// Update and Flush
// ------------------
always_comb begin : update_flush
  content_n = content_q;

  for (int unsigned i = 0; i < TLB_ENTRIES; i++) begin

    tag_valid[i] = tags_q[i].valid;
      
      if(HYP_EXT==1) begin
        gppn[i] = make_gppn(tags_q[i].v_st_enbl[0], tags_q[i].is_page[0][0], tags_q[i].is_page[1][0], {tags_q[i].vpn[3][(VPN_LEN%PT_LEVELS)-1:0],tags_q[i].vpn[2],tags_q[i].vpn[1],tags_q[i].vpn[0]}, content_q[i][0]);
      end
      

      if (flush_i[0]) begin
          if(!tags_q[i].v_st_enbl[HYP_EXT*2] || HYP_EXT==0) begin
              // invalidate logic
              // flush everything if ASID is 0 and vaddr is 0 ("SFENCE.VMA x0 x0" case)
              if (asid_to_be_flushed_is0[0] && vaddr_to_be_flushed_is0[0] )
              tag_valid[i] = 1'b0;
              // flush vaddr in all addressing space ("SFENCE.VMA vaddr x0" case), it should happen only for leaf pages
              else if (asid_to_be_flushed_is0[0] && (|vaddr_level_match[i][0] ) && (~vaddr_to_be_flushed_is0[0]))
                tag_valid[i] = 1'b0;
              // the entry is flushed if it's not global and asid and vaddr both matches with the entry to be flushed ("SFENCE.VMA vaddr asid" case)
              else if ((!content_q[i][0].g) && (|vaddr_level_match[i][0]) && (asid_to_be_flushed_i[0][ASID_WIDTH[0]-1:0] == tags_q[i].asid[0][ASID_WIDTH[0]-1:0] ) && (!vaddr_to_be_flushed_is0[0]) && (!asid_to_be_flushed_is0[0]))
                tag_valid[i] = 1'b0;
              // the entry is flushed if it's not global, and the asid matches and vaddr is 0. ("SFENCE.VMA 0 asid" case)
              else if ((!content_q[i][0].g) && (vaddr_to_be_flushed_is0[0]) && (asid_to_be_flushed_i[0][ASID_WIDTH[0]-1:0]  == tags_q[i].asid[0][ASID_WIDTH[0]-1:0] ) && (!asid_to_be_flushed_is0[0]))
                tag_valid[i] = 1'b0;
          end
      end else if (flush_i[HYP_EXT] &&  HYP_EXT==1) begin
          if(tags_q[i].v_st_enbl[HYP_EXT*2] && tags_q[i].v_st_enbl[0]) begin
              // invalidate logic
              // flush everything if current VMID matches and ASID is 0 and vaddr is 0 ("SFENCE.VMA/HFENCE.VVMA x0 x0" case)
              if (asid_to_be_flushed_is0[0] && vaddr_to_be_flushed_is0[0] && ((tags_q[i].v_st_enbl[HYP_EXT] && lu_asid_i[HYP_EXT][ASID_WIDTH[HYP_EXT]-1:0] == tags_q[i].asid[HYP_EXT][ASID_WIDTH[HYP_EXT]-1:0]) || !tags_q[i].v_st_enbl[HYP_EXT]))
              tag_valid[i] = 1'b0;
              // flush vaddr in all addressing space if current VMID matches ("SFENCE.VMA/HFENCE.VVMA vaddr x0" case), it should happen only for leaf pages
              else if (asid_to_be_flushed_is0[0] && (|vaddr_level_match[i][0]) && (~vaddr_to_be_flushed_is0[0]) && ((tags_q[i].v_st_enbl[HYP_EXT] && lu_asid_i[HYP_EXT][ASID_WIDTH[HYP_EXT]-1:0] == tags_q[i].asid[1][ASID_WIDTH[HYP_EXT]-1:0]) || !tags_q[i].v_st_enbl[HYP_EXT]))
                tag_valid[i] = 1'b0;
              // the entry is flushed if it's not global and asid and vaddr and current VMID matches with the entry to be flushed ("SFENCE.VMA/HFENCE.VVMA vaddr asid" case)
              else if ((!content_q[i][0].g) && (|vaddr_level_match[i][0]) && (asid_to_be_flushed_i[0][ASID_WIDTH[0]-1:0]  == tags_q[i].asid[0][ASID_WIDTH[0]-1:0]  && ((tags_q[i].v_st_enbl[HYP_EXT] && lu_asid_i[HYP_EXT][ASID_WIDTH[HYP_EXT]-1:0] == tags_q[i].asid[HYP_EXT][ASID_WIDTH[HYP_EXT]-1:0]) || !tags_q[i].v_st_enbl[HYP_EXT])) && (!vaddr_to_be_flushed_is0[0]) && (!asid_to_be_flushed_is0[0]))
                tag_valid[i] = 1'b0;
              // the entry is flushed if it's not global, and the asid and the current VMID matches and vaddr is 0. ("SFENCE.VMA/HFENCE.VVMA 0 asid" case)
              else if ((!content_q[i][0].g) && (vaddr_to_be_flushed_is0[0]) && (asid_to_be_flushed_i[0][ASID_WIDTH[0]-1:0]  == tags_q[i].asid[0][ASID_WIDTH[0]-1:0]  && ((tags_q[i].v_st_enbl[HYP_EXT] && lu_asid_i[HYP_EXT][ASID_WIDTH[HYP_EXT]-1:0] == tags_q[i].asid[HYP_EXT][ASID_WIDTH[HYP_EXT]-1:0]) || !tags_q[i].v_st_enbl[HYP_EXT])) && (!asid_to_be_flushed_is0[0]))
                tag_valid[i] = 1'b0;
          end
      end else if (flush_i[HYP_EXT*2] &&  HYP_EXT==1) begin
          if(tags_q[i].v_st_enbl[HYP_EXT]) begin
              // invalidate logic
              // flush everything if vmid is 0 and addr is 0 ("HFENCE.GVMA x0 x0" case)
              if (asid_to_be_flushed_is0[HYP_EXT] && vaddr_to_be_flushed_is0[HYP_EXT] )
              tag_valid[i] = 1'b0;
              // flush gpaddr in all addressing space ("HFENCE.GVMA gpaddr x0" case), it should happen only for leaf pages
              else if (asid_to_be_flushed_is0[HYP_EXT] && (|vaddr_level_match[i][HYP_EXT] ) && (~vaddr_to_be_flushed_is0[HYP_EXT]))
                tag_valid[i] = 1'b0;
              // the entry vmid and gpaddr both matches with the entry to be flushed ("HFENCE.GVMA gpaddr vmid" case)
              else if ((|vaddr_level_match[i][HYP_EXT]) && (asid_to_be_flushed_i[HYP_EXT][ASID_WIDTH[HYP_EXT]-1:0] == tags_q[i].asid[HYP_EXT][ASID_WIDTH[HYP_EXT]-1:0]) && (~vaddr_to_be_flushed_is0[HYP_EXT]) && (~asid_to_be_flushed_is0[HYP_EXT]))
                tag_valid[i] = 1'b0;
              // the entry is flushed if the vmid matches and gpaddr is 0. ("HFENCE.GVMA 0 vmid" case)
              else if ((vaddr_to_be_flushed_is0[HYP_EXT]) && (asid_to_be_flushed_i[HYP_EXT][ASID_WIDTH[HYP_EXT]-1:0] == tags_q[i].asid[HYP_EXT][ASID_WIDTH[HYP_EXT]-1:0]) && (!asid_to_be_flushed_is0[HYP_EXT]))
                tag_valid[i] = 1'b0;
          end
      // normal replacement
      end else if (update_i.valid & replace_en[i] && !lu_hit_o) begin
          // update content as well
          content_n[i] = update_i.content;
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
assert (ASID_WIDTH[0] >= 1)
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
