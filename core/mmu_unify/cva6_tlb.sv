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
// 2023-12-13  0.2      A.Gonzalez   Generic TLB for CVA6 with Hypervisor support
// =========================================================================== //

  module cva6_tlb
  import ariane_pkg::*;
#(
    parameter type pte_cva6_t = logic,
    parameter type tlb_update_cva6_t = logic,
    parameter config_pkg::cva6_cfg_t CVA6Cfg = config_pkg::cva6_cfg_empty,
    parameter logic HYP_EXT = 0,
    parameter int unsigned TLB_ENTRIES = 4,
    parameter int unsigned  ASID_WIDTH [HYP_EXT:0] = {1}, //[vmid_width,asid_width]
    parameter int unsigned  ASID_LEN[HYP_EXT:0] = 1, //[vmid_len,asid_len]
    parameter int unsigned VPN_LEN = 1,
    parameter int unsigned PT_LEVELS = 1
  ) (
    input logic clk_i,  // Clock
    input logic rst_ni,  // Asynchronous reset active low
    input logic [HYP_EXT*2:0] flush_i,  // Flush signal [g_stage,vs stage, normal translation signal]
    input  logic  [HYP_EXT*2:0] v_st_enbl_i,  // v_i,g-stage enabled, s-stage enabled
    // Update TLB
    input tlb_update_cva6_t update_i,
    // Lookup signals
    input logic lu_access_i,
    input logic [ASID_WIDTH[0]-1:0] lu_asid_i [HYP_EXT:0], //[lu_vmid,lu_asid]
    input logic [riscv::VLEN-1:0] lu_vaddr_i [HYP_EXT:0], //[gp_addr,vaddr]
    output  pte_cva6_t [HYP_EXT:0] lu_content_o ,
    input logic [ASID_WIDTH[0]-1:0] asid_to_be_flushed_i [HYP_EXT:0], //[vmid,asid]
    input logic [riscv::VLEN-1:0] vaddr_to_be_flushed_i [HYP_EXT:0], // [gpaddr,vaddr]
    output logic [PT_LEVELS-2:0] lu_is_page_o,
    output logic lu_hit_o
);

  // Sv32 defines two levels of page tables, Sv39 defines 3
  struct packed {
    logic [HYP_EXT:0][ASID_LEN-1:0] asid;   
    logic [PT_LEVELS+HYP_EXT-1:0][(VPN_LEN/PT_LEVELS)-1:0] vpn;   
    logic [HYP_EXT:0][PT_LEVELS-2:0] is_page;
    logic  [HYP_EXT*2:0] v_st_enbl_i; // v_i,g-stage enabled, s-stage enabled
    logic       valid;
  } [TLB_ENTRIES-1:0]
      tags_q, tags_n;

  pte_cva6_t [HYP_EXT:0][TLB_ENTRIES-1:0] content_q , content_n;
  logic [TLB_ENTRIES-1:0][PT_LEVELS-1:0] vpn_match;
  logic [TLB_ENTRIES-1:0][HYP_EXT:0]     asid_match;
  logic [TLB_ENTRIES-1:0][PT_LEVELS-1:0] page_match;
  logic [TLB_ENTRIES-1:0][PT_LEVELS-1:0] level_match;
  logic [TLB_ENTRIES-1:0][PT_LEVELS-1:0] vaddr_vpn_match;
  logic [TLB_ENTRIES-1:0][PT_LEVELS-1:0] vaddr_level_match;
  logic [TLB_ENTRIES-1:0] lu_hit;  // to replacement logic
  logic [TLB_ENTRIES-1:0] replace_en;  // replace the following entry, set by replacement strategy
  //-------------
  // Translation
  //-------------

    //at level 0 make page match always 1
    //build level match vector according to vpn_match and page_match
    //a level has a match if all vpn of higher levels and current have a match, 
    //AND the page_match is also set
    //At level 0 the page match is always set, so this level will have a match
    //if all vpn levels match
  genvar i,x,z;
      generate
        for (i=0; i < TLB_ENTRIES; i++) begin
          
          for(z=0;z<HYP_EXT+1;z++) begin
              assign asid_match[i][z]= (lu_asid_i[z] == tags_q[i].asid[z][ASID_WIDTH[z]-1:0]) ||!v_st_enbl_i[z];
          end

          for (x=0; x < PT_LEVELS; x++) begin  
              //identify page_match for all TLB Entries
              assign page_match[i][x] = x==0 ? 1 :tags_q[i].is_page[PT_LEVELS-1-x];
              //identify if vpn matches at all PT levels for all TLB entries  
              assign vpn_match[i][x]        = lu_vaddr_i[0][12+((VPN_LEN/PT_LEVELS)*(x+1))-1:12+((VPN_LEN/PT_LEVELS)*x)] == tags_q[i].vpn[x];
              //identify if there is a hit at each PT level for all TLB entries  
              assign level_match[i][x]      = &vpn_match[i][PT_LEVELS-1:x] & page_match[i][x];
              //identify if virtual address vpn matches at all PT levels for all TLB entries  
              assign vaddr_vpn_match[i][x]  = vaddr_to_be_flushed_i[0][12+((VPN_LEN/PT_LEVELS)*(x+1))-1:12+((VPN_LEN/PT_LEVELS)*x)] == tags_q[i].vpn[x];
              //identify if there is a hit at each PT level for all TLB entries  
              assign vaddr_level_match[i][x]= &vaddr_vpn_match[i][PT_LEVELS-1:x] & page_match[i][x];
              //update vpn field in tags_n for each TLB when the update is valid and the tag needs to be replaced
              assign tags_n[i].vpn[x]       = (!flush_i && update_i.valid && replace_en[i]) ? update_i.vpn[(1+x)*(VPN_LEN/PT_LEVELS)-1:x*(VPN_LEN/PT_LEVELS)] : tags_q[i].vpn[x];
          end
        end
      endgenerate

  always_comb begin : translation

    // default assignment
    lu_hit       = '{default: 0};
    lu_hit_o     = 1'b0;
    lu_content_o = '{default: 0};
    lu_is_page_o   = 0;

    for (int unsigned i = 0; i < TLB_ENTRIES; i++) begin
      // first level match, this may be a page, check the ASID flags as well
      // if the entry is associated to a global address, don't match the ASID (ASID is don't care)
      if (tags_q[i].valid && (&asid_match || (v_st_enbl_i[0]&&content_q[0][i].g))) begin
        // find if there is a match at any level
        if (|level_match[i]) begin
              lu_is_page_o   = tags_q[i].is_page; //the page size is indicated here
              lu_content_o = content_q[0][i];
              lu_hit_o     = 1'b1;
              lu_hit[i]    = 1'b1;
        end
      end
    end
  end

  logic asid_to_be_flushed_is0;  // indicates that the ASID provided by SFENCE.VMA (rs2)is 0, active high
  logic vaddr_to_be_flushed_is0;  // indicates that the VADDR provided by SFENCE.VMA (rs1)is 0, active high

  assign asid_to_be_flushed_is0  = ~(|asid_to_be_flushed_i[0]);
  assign vaddr_to_be_flushed_is0 = ~(|vaddr_to_be_flushed_i[0]);

  // ------------------
  // Update and Flush
  // ------------------
  always_comb begin : update_flush
    
    content_n = content_q;

    for (int unsigned i = 0; i < TLB_ENTRIES; i++) begin
      tags_n[i].asid    = tags_q[i].asid;
      tags_n[i].is_page    = tags_q[i].is_page;
      tags_n[i].valid    = tags_q[i].valid;
      if (flush_i) begin
        // invalidate logic
        // flush everything if ASID is 0 and vaddr is 0 ("SFENCE.VMA x0 x0" case)
        if (asid_to_be_flushed_is0 && vaddr_to_be_flushed_is0) tags_n[i].valid = 1'b0;
        // flush vaddr in all addressing space ("SFENCE.VMA vaddr x0" case), it should happen only for leaf pages
        else if (asid_to_be_flushed_is0 && (|vaddr_level_match[i]) && (~vaddr_to_be_flushed_is0))
          tags_n[i].valid = 1'b0;
        // the entry is flushed if it's not global and asid and vaddr both matches with the entry to be flushed ("SFENCE.VMA vaddr asid" case)
        else if ((!content_q[0][i].g) && (|vaddr_level_match[i]) && (asid_to_be_flushed_i[0] == tags_q[i].asid[0][ASID_WIDTH[0]-1:0]) && (!vaddr_to_be_flushed_is0) && (!asid_to_be_flushed_is0))
          tags_n[i].valid = 1'b0;
        // the entry is flushed if it's not global, and the asid matches and vaddr is 0. ("SFENCE.VMA 0 asid" case)
        else if ((!content_q[0][i].g) && (vaddr_to_be_flushed_is0) && (asid_to_be_flushed_i[0] == tags_q[i].asid[0][ASID_WIDTH[0]-1:0]) && (!asid_to_be_flushed_is0))
          tags_n[i].valid = 1'b0;
        // normal replacement
      end else if (update_i.valid & replace_en[i]) begin
        // update tag array
        tags_n[i].asid   = update_i.asid;
        tags_n[i].is_page= update_i.is_page;
        tags_n[i].valid  = 1'b1;

      // and content as well
      content_n[0][i] = update_i.content;
    end
  end
end

// -----------------------------------------------
// PLRU - Pseudo Least Recently Used Replacement
// -----------------------------------------------
logic [2*(TLB_ENTRIES-1)-1:0] plru_tree_q, plru_tree_n;
logic en;
int unsigned idx_base, shift, new_index;
always_comb begin : plru_replacement
  plru_tree_n = plru_tree_q;
  en = '0;
  idx_base = '0;
  shift = '0;
  new_index = '0;
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
      for (
      int unsigned i = 0; i < TLB_ENTRIES; i++
  ) begin
    // we got a hit so update the pointer as it was least recently used
    if (lu_hit[i] & lu_access_i) begin
      // Set the nodes to the values we would expect
      for (int unsigned lvl = 0; lvl < $clog2(TLB_ENTRIES); lvl++) begin
        idx_base = $unsigned((2 ** lvl) - 1);
        // lvl0 <=> MSB, lvl1 <=> MSB-1, ...
        shift = $clog2(TLB_ENTRIES) - lvl;
        // to circumvent the 32 bit integer arithmetic assignment
        new_index = ~((i >> (shift - 1)) & 32'b1);
        plru_tree_n[idx_base+(i>>shift)] = new_index[0];
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
    en = 1'b1;
    for (int unsigned lvl = 0; lvl < $clog2(TLB_ENTRIES); lvl++) begin
      idx_base = $unsigned((2 ** lvl) - 1);
      // lvl0 <=> MSB, lvl1 <=> MSB-1, ...
      shift = $clog2(TLB_ENTRIES) - lvl;

      // en &= plru_tree_q[idx_base + (i>>shift)] == ((i >> (shift-1)) & 1'b1);
      new_index = (i >> (shift - 1)) & 32'b1;
      if (new_index[0]) begin
        en &= plru_tree_q[idx_base+(i>>shift)];
      end else begin
        en &= ~plru_tree_q[idx_base+(i>>shift)];
      end
    end
    replace_en[i] = en;
  end
end

// sequential process
always_ff @(posedge clk_i or negedge rst_ni) begin
  if (~rst_ni) begin
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
  else begin
    $error("TLB size must be a multiple of 2 and greater than 1");
    $stop();
  end
  assert (ASID_WIDTH[0] >= 1)
  else begin
    $error("ASID width must be at least 1");
    $stop();
  end
end

// Just for checking
function int countSetBits(logic [TLB_ENTRIES-1:0] vector);
  automatic int count = 0;
  foreach (vector[idx]) begin
    count += vector[idx];
  end
  return count;
endfunction

assert property (@(posedge clk_i) (countSetBits(lu_hit) <= 1))
else begin
  $error("More then one hit in TLB!");
  $stop();
end
assert property (@(posedge clk_i) (countSetBits(replace_en) <= 1))
else begin
  $error("More then one TLB entry selected for next replace!");
  $stop();
end

`endif
//pragma translate_on

endmodule
