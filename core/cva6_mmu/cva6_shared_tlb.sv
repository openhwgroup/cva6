// Copyright (c) 2023 Thales.
// Copyright (c) 2024, PlanV Technology
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
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
// Date: 26/02/2024
//
// Description: N-way associative shared TLB, it allows to reduce the number
//              of ITLB and DTLB entries. This module is an update of the
//              shared TLB sv32 developed by Sebastien Jacq (Thales Research & Technology)
//              to be used with sv32, sv39 and sv39x4.

/* verilator lint_off WIDTH */

module cva6_shared_tlb #(
    parameter config_pkg::cva6_cfg_t CVA6Cfg = config_pkg::cva6_cfg_empty,
    parameter type pte_cva6_t = logic,
    parameter type tlb_update_cva6_t = logic,
    parameter int SHARED_TLB_WAYS = 2,
    parameter int unsigned HYP_EXT = 0

) (
    input logic clk_i,  // Clock
    input logic rst_ni,  // Asynchronous reset active low
    input logic flush_i,  // Flush normal translations signal
    input logic flush_vvma_i,  // Flush vs stage signal
    input logic flush_gvma_i,  // Flush g stage signal
    input logic s_st_enbl_i,  // s-stage enabled
    input logic g_st_enbl_i,  // g-stage enabled
    input logic v_i,  // virtualization mode
    input logic s_ld_st_enbl_i,  // s-stage enabled for load stores
    input logic g_ld_st_enbl_i,  // g-stage enabled for load stores
    input logic ld_st_v_i,  // virtualization mode for load stores

    input logic [CVA6Cfg.ASID_WIDTH-1:0] dtlb_asid_i,
    input logic [CVA6Cfg.ASID_WIDTH-1:0] itlb_asid_i,
    input logic [CVA6Cfg.VMID_WIDTH-1:0] lu_vmid_i,

    // from TLBs
    // did we miss?
    input logic                    itlb_access_i,
    input logic                    itlb_hit_i,
    input logic [CVA6Cfg.VLEN-1:0] itlb_vaddr_i,

    input logic                    dtlb_access_i,
    input logic                    dtlb_hit_i,
    input logic [CVA6Cfg.VLEN-1:0] dtlb_vaddr_i,

    input logic shared_tlb_miss_i,

    // to TLBs, update logic
    output tlb_update_cva6_t itlb_update_o,
    output tlb_update_cva6_t dtlb_update_o,

    // Performance counters
    output logic itlb_miss_o,
    output logic dtlb_miss_o,

    output logic                    shared_tlb_access_o,
    output logic                    shared_tlb_hit_o,
    output logic [CVA6Cfg.VLEN-1:0] shared_tlb_vaddr_o,

    output logic itlb_req_o,

    // Update shared TLB in case of miss
    input tlb_update_cva6_t shared_tlb_update_i

);

  function logic [SHARED_TLB_WAYS-1:0] shared_tlb_way_bin2oh(input logic [$clog2(SHARED_TLB_WAYS
)-1:0] in);
    logic [SHARED_TLB_WAYS-1:0] out;
    out     = '0;
    out[in] = 1'b1;
    return out;
  endfunction

  typedef struct packed {
    logic [CVA6Cfg.ASID_WIDTH-1:0] asid;
    logic [CVA6Cfg.VMID_WIDTH-1:0] vmid;
    logic [CVA6Cfg.PtLevels+HYP_EXT-1:0][(CVA6Cfg.VpnLen/CVA6Cfg.PtLevels)-1:0] vpn;
    logic [CVA6Cfg.PtLevels-2:0][HYP_EXT:0] is_page;
    logic [HYP_EXT*2:0] v_st_enbl;  // v_i,g-stage enabled, s-stage enabled
  } shared_tag_t;

  shared_tag_t shared_tag_wr;
  shared_tag_t [SHARED_TLB_WAYS-1:0] shared_tag_rd;

  logic [CVA6Cfg.SharedTlbDepth-1:0][SHARED_TLB_WAYS-1:0] shared_tag_valid_q, shared_tag_valid_d;

  logic [               SHARED_TLB_WAYS-1:0] shared_tag_valid;

  logic [               SHARED_TLB_WAYS-1:0] tag_wr_en;
  logic [$clog2(CVA6Cfg.SharedTlbDepth)-1:0] tag_wr_addr;
  logic [           $bits(shared_tag_t)-1:0] tag_wr_data;

  logic [               SHARED_TLB_WAYS-1:0] tag_rd_en;
  logic [$clog2(CVA6Cfg.SharedTlbDepth)-1:0] tag_rd_addr;
  logic [           $bits(shared_tag_t)-1:0] tag_rd_data      [SHARED_TLB_WAYS-1:0];

  logic [               SHARED_TLB_WAYS-1:0] tag_req;
  logic [               SHARED_TLB_WAYS-1:0] tag_we;
  logic [$clog2(CVA6Cfg.SharedTlbDepth)-1:0] tag_addr;

  logic [               SHARED_TLB_WAYS-1:0] pte_wr_en;
  logic [$clog2(CVA6Cfg.SharedTlbDepth)-1:0] pte_wr_addr;
  logic [                  CVA6Cfg.XLEN-1:0] pte_wr_data      [                1:0];

  logic [               SHARED_TLB_WAYS-1:0] pte_rd_en;
  logic [$clog2(CVA6Cfg.SharedTlbDepth)-1:0] pte_rd_addr;
  logic [                  CVA6Cfg.XLEN-1:0] pte_rd_data      [SHARED_TLB_WAYS-1:0] [HYP_EXT:0];

  logic [               SHARED_TLB_WAYS-1:0] pte_req;
  logic [               SHARED_TLB_WAYS-1:0] pte_we;
  logic [$clog2(CVA6Cfg.SharedTlbDepth)-1:0] pte_addr;

  logic [CVA6Cfg.PtLevels+HYP_EXT-1:0][(CVA6Cfg.VpnLen/CVA6Cfg.PtLevels)-1:0] vpn_d, vpn_q;
  logic [SHARED_TLB_WAYS-1:0][CVA6Cfg.PtLevels-1:0] vpn_match;
  logic [SHARED_TLB_WAYS-1:0][CVA6Cfg.PtLevels-1:0] page_match;
  logic [SHARED_TLB_WAYS-1:0][CVA6Cfg.PtLevels-1:0] level_match;

  logic [SHARED_TLB_WAYS-1:0] match_asid;
  logic [SHARED_TLB_WAYS-1:0] match_vmid;
  logic [SHARED_TLB_WAYS-1:0] match_stage;

  pte_cva6_t [SHARED_TLB_WAYS-1:0][HYP_EXT:0] pte;

  logic [CVA6Cfg.VLEN-1-12:0] itlb_vpn_q;
  logic [CVA6Cfg.VLEN-1-12:0] dtlb_vpn_q;

  logic [CVA6Cfg.ASID_WIDTH-1:0] tlb_update_asid_q, tlb_update_asid_d;
  logic [CVA6Cfg.VMID_WIDTH-1:0] tlb_update_vmid_q, tlb_update_vmid_d;

  logic shared_tlb_access_q, shared_tlb_access_d;
  logic shared_tlb_hit_d;
  logic [CVA6Cfg.VLEN-1:0] shared_tlb_vaddr_q, shared_tlb_vaddr_d;

  logic itlb_req_d, itlb_req_q;
  logic dtlb_req_d, dtlb_req_q;

  int i_req_d, i_req_q;

  logic [1:0][2:0] v_st_enbl;

  // replacement strategy
  logic [SHARED_TLB_WAYS-1:0] way_valid;
  logic update_lfsr;  // shift the LFSR
  logic [$clog2(SHARED_TLB_WAYS)-1:0] inv_way;  // first non-valid encountered
  logic [$clog2(SHARED_TLB_WAYS)-1:0] rnd_way;  // random index for replacement
  logic [$clog2(SHARED_TLB_WAYS)-1:0] repl_way;  // way to replace
  logic [SHARED_TLB_WAYS-1:0] repl_way_oh_d;  // way to replace (onehot)
  logic all_ways_valid;  // we need to switch repl strategy since all are valid

  assign shared_tlb_access_o = shared_tlb_access_q;
  assign shared_tlb_hit_o = shared_tlb_hit_d;
  assign shared_tlb_vaddr_o = shared_tlb_vaddr_q;
  assign itlb_req_o = itlb_req_q;
  assign v_st_enbl = {{v_i, g_st_enbl_i, s_st_enbl_i}, {ld_st_v_i, g_ld_st_enbl_i, s_ld_st_enbl_i}};

  genvar i, x;
  generate
    for (i = 0; i < SHARED_TLB_WAYS; i++) begin : gen_match_tlb_ways
      //identify page_match for all TLB Entries

      for (x = 0; x < CVA6Cfg.PtLevels; x++) begin : gen_match
        assign page_match[i][x] = x==0 ? 1 :((HYP_EXT==0 || x==(CVA6Cfg.PtLevels-1)) ? // PAGE_MATCH CONTAINS THE MATCH INFORMATION FOR EACH TAG OF is_1G and is_2M in sv39x4. HIGHER LEVEL (Giga page), THEN THERE IS THE Mega page AND AT THE LOWER LEVEL IS ALWAYS 1
            &(shared_tag_rd[i].is_page[CVA6Cfg.PtLevels-1-x] | (~v_st_enbl[i_req_q][HYP_EXT:0])):
                              ((&v_st_enbl[i_req_q][HYP_EXT:0]) ?
                              ((shared_tag_rd[i].is_page[CVA6Cfg.PtLevels-1-x][0] && (shared_tag_rd[i].is_page[CVA6Cfg.PtLevels-2-x][HYP_EXT] || shared_tag_rd[i].is_page[CVA6Cfg.PtLevels-1-x][HYP_EXT]))
                            || (shared_tag_rd[i].is_page[CVA6Cfg.PtLevels-1-x][HYP_EXT] && (shared_tag_rd[i].is_page[CVA6Cfg.PtLevels-2-x][0] || shared_tag_rd[i].is_page[CVA6Cfg.PtLevels-1-x][0]))):
                                shared_tag_rd[i].is_page[CVA6Cfg.PtLevels-1-x][0] && v_st_enbl[i_req_q][0] || shared_tag_rd[i].is_page[CVA6Cfg.PtLevels-1-x][HYP_EXT] && v_st_enbl[i_req_q][HYP_EXT]));

        //identify if vpn matches at all PT levels for all TLB entries
        assign vpn_match[i][x]        = (HYP_EXT==1 && x==(CVA6Cfg.PtLevels-1) && ~v_st_enbl[i_req_q][0]) ? //
            vpn_q[x] == shared_tag_rd[i].vpn[x] &&  vpn_q[x+HYP_EXT][(CVA6Cfg.VpnLen%CVA6Cfg.PtLevels)-HYP_EXT:0] == shared_tag_rd[i].vpn[x+HYP_EXT][(CVA6Cfg.VpnLen%CVA6Cfg.PtLevels)-HYP_EXT:0]: //
            vpn_q[x] == shared_tag_rd[i].vpn[x];

        //identify if there is a hit at each PT level for all TLB entries
        assign level_match[i][x] = &vpn_match[i][CVA6Cfg.PtLevels-1:x] && page_match[i][x];

      end
    end
  endgenerate

  genvar w;
  generate
    for (w = 0; w < CVA6Cfg.PtLevels; w++) begin
      assign vpn_d[w]               = ((|v_st_enbl[1][HYP_EXT:0]) && itlb_access_i && ~itlb_hit_i && ~dtlb_access_i) ? //
          itlb_vaddr_i[12+((CVA6Cfg.VpnLen/CVA6Cfg.PtLevels)*(w+1))-1:12+((CVA6Cfg.VpnLen/CVA6Cfg.PtLevels)*w)] :  //
          (((|v_st_enbl[0][HYP_EXT:0]) && dtlb_access_i && ~dtlb_hit_i) ?  //
          dtlb_vaddr_i[12+((CVA6Cfg.VpnLen/CVA6Cfg.PtLevels)*(w+1))-1:12+((CVA6Cfg.VpnLen/CVA6Cfg.PtLevels)*w)] : vpn_q[w]);
    end
  endgenerate

  if (CVA6Cfg.RVH)  //THIS UPDATES THE EXTRA BITS OF VPN IN SV39x4
    assign vpn_d[CVA6Cfg.PtLevels][(CVA6Cfg.VpnLen%CVA6Cfg.PtLevels)-1:0] = ((|v_st_enbl[1][HYP_EXT:0]) && itlb_access_i && ~itlb_hit_i && ~dtlb_access_i) ? //
        itlb_vaddr_i[CVA6Cfg.VpnLen-1:CVA6Cfg.VpnLen-(CVA6Cfg.VpnLen%CVA6Cfg.PtLevels)] :  //
        (((|v_st_enbl[0][HYP_EXT:0]) && dtlb_access_i && ~dtlb_hit_i) ?  //
        dtlb_vaddr_i[CVA6Cfg.VpnLen-1: CVA6Cfg.VpnLen-(CVA6Cfg.VpnLen%CVA6Cfg.PtLevels)] : vpn_q[CVA6Cfg.PtLevels][(CVA6Cfg.VpnLen%CVA6Cfg.PtLevels)-1:0]);

  ///////////////////////////////////////////////////////
  // tag comparison, hit generation
  ///////////////////////////////////////////////////////
  always_comb begin : itlb_dtlb_miss
    itlb_miss_o         = 1'b0;
    dtlb_miss_o         = 1'b0;

    tag_rd_en           = '0;
    pte_rd_en           = '0;

    itlb_req_d          = 1'b0;
    dtlb_req_d          = 1'b0;

    tlb_update_asid_d   = tlb_update_asid_q;
    tlb_update_vmid_d   = tlb_update_vmid_q;

    shared_tlb_access_d = '0;
    shared_tlb_vaddr_d  = shared_tlb_vaddr_q;

    tag_rd_addr         = '0;
    pte_rd_addr         = '0;
    i_req_d             = i_req_q;

    // if we got an ITLB miss
    if ((|v_st_enbl[1][HYP_EXT:0]) & itlb_access_i & ~itlb_hit_i & ~dtlb_access_i) begin
      tag_rd_en           = '1;
      tag_rd_addr         = itlb_vaddr_i[12+:$clog2(CVA6Cfg.SharedTlbDepth)];
      pte_rd_en           = '1;
      pte_rd_addr         = itlb_vaddr_i[12+:$clog2(CVA6Cfg.SharedTlbDepth)];

      itlb_miss_o         = shared_tlb_miss_i;
      itlb_req_d          = 1'b1;
      tlb_update_asid_d   = itlb_asid_i;
      tlb_update_vmid_d   = lu_vmid_i;

      shared_tlb_access_d = '1;
      shared_tlb_vaddr_d  = itlb_vaddr_i;
      i_req_d             = 1;

      // we got an DTLB miss
    end else if ((|v_st_enbl[0][HYP_EXT:0]) & dtlb_access_i & ~dtlb_hit_i) begin
      tag_rd_en           = '1;
      tag_rd_addr         = dtlb_vaddr_i[12+:$clog2(CVA6Cfg.SharedTlbDepth)];
      pte_rd_en           = '1;
      pte_rd_addr         = dtlb_vaddr_i[12+:$clog2(CVA6Cfg.SharedTlbDepth)];

      dtlb_miss_o         = shared_tlb_miss_i;
      dtlb_req_d          = 1'b1;
      tlb_update_asid_d   = dtlb_asid_i;
      tlb_update_vmid_d   = lu_vmid_i;

      shared_tlb_access_d = '1;
      shared_tlb_vaddr_d  = dtlb_vaddr_i;
      i_req_d             = 0;
    end
  end  //itlb_dtlb_miss

  always_comb begin : tag_comparison
    shared_tlb_hit_d = 1'b0;
    dtlb_update_o    = '0;
    itlb_update_o    = '0;
    match_asid       = '{default: 0};
    match_vmid       = CVA6Cfg.RVH ? '{default: 0} : '{default: 1};


    if (!CVA6Cfg.UseSharedTlb) begin
      if (shared_tlb_update_i.valid) begin
        shared_tlb_hit_d = 1'b1;
        if (itlb_req_q) begin
          itlb_update_o.valid = 1'b1;
          itlb_update_o.vpn = shared_tlb_update_i.vpn;
          itlb_update_o.is_page = shared_tlb_update_i.is_page;
          itlb_update_o.content = shared_tlb_update_i.content;
          itlb_update_o.g_content = shared_tlb_update_i.g_content;
          itlb_update_o.v_st_enbl = v_st_enbl[i_req_q][HYP_EXT*2:0];
          itlb_update_o.asid = shared_tlb_update_i.asid;
          itlb_update_o.vmid = shared_tlb_update_i.vmid;

        end else if (dtlb_req_q) begin
          dtlb_update_o.valid = 1'b1;
          dtlb_update_o.vpn = shared_tlb_update_i.vpn;
          dtlb_update_o.is_page = shared_tlb_update_i.is_page;
          dtlb_update_o.content = shared_tlb_update_i.content;
          dtlb_update_o.g_content = shared_tlb_update_i.g_content;
          dtlb_update_o.v_st_enbl = v_st_enbl[i_req_q][HYP_EXT*2:0];
          dtlb_update_o.asid = shared_tlb_update_i.asid;
          dtlb_update_o.vmid = shared_tlb_update_i.vmid;
        end
      end
    end else begin

      //number of ways
      for (int unsigned i = 0; i < SHARED_TLB_WAYS; i++) begin
        // first level match, this may be a giga page, check the ASID flags as well
        // if the entry is associated to a global address, don't match the ASID (ASID is don't care)
        match_asid[i] = (((tlb_update_asid_q == shared_tag_rd[i].asid) || pte[i][0].g) && v_st_enbl[i_req_q][0]) || !v_st_enbl[i_req_q][0];

        if (CVA6Cfg.RVH) begin
          match_vmid[i] = (tlb_update_vmid_q == shared_tag_rd[i].vmid && v_st_enbl[i_req_q][HYP_EXT]) || !v_st_enbl[i_req_q][HYP_EXT];
        end

        // check if translation is a: S-Stage and G-Stage, S-Stage only or G-Stage only translation and virtualization mode is on/off
        match_stage[i] = shared_tag_rd[i].v_st_enbl == v_st_enbl[i_req_q][HYP_EXT*2:0];

        if (shared_tag_valid[i] && match_asid[i] && match_vmid[i] && match_stage[i]) begin
          if (|level_match[i]) begin
            shared_tlb_hit_d = 1'b1;
            if (itlb_req_q) begin
              itlb_update_o.valid = 1'b1;
              itlb_update_o.vpn = itlb_vpn_q;
              itlb_update_o.is_page = shared_tag_rd[i].is_page;
              itlb_update_o.content = pte[i][0];
              itlb_update_o.g_content = pte[i][HYP_EXT];
              itlb_update_o.v_st_enbl = shared_tag_rd[i].v_st_enbl;
              itlb_update_o.asid = tlb_update_asid_q;
              itlb_update_o.vmid = tlb_update_vmid_q;
            end else if (dtlb_req_q) begin
              dtlb_update_o.valid = 1'b1;
              dtlb_update_o.vpn = dtlb_vpn_q;
              dtlb_update_o.is_page = shared_tag_rd[i].is_page;
              dtlb_update_o.content = pte[i][0];
              dtlb_update_o.g_content = pte[i][HYP_EXT];
              dtlb_update_o.v_st_enbl = shared_tag_rd[i].v_st_enbl;
              dtlb_update_o.asid = tlb_update_asid_q;
              dtlb_update_o.vmid = tlb_update_vmid_q;
            end
          end
        end
      end
    end
  end  //tag_comparison

  // sequential process
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (~rst_ni) begin
      itlb_vpn_q <= '0;
      dtlb_vpn_q <= '0;
      tlb_update_asid_q <= '{default: 0};
      tlb_update_vmid_q <= '{default: 0};
      shared_tlb_access_q <= '0;
      shared_tlb_vaddr_q <= '0;
      shared_tag_valid_q <= '0;
      vpn_q <= 0;
      itlb_req_q <= '0;
      dtlb_req_q <= '0;
      i_req_q <= 0;
      shared_tag_valid <= '0;
    end else begin
      itlb_vpn_q <= itlb_vaddr_i[CVA6Cfg.SV-1:12];
      dtlb_vpn_q <= dtlb_vaddr_i[CVA6Cfg.SV-1:12];
      tlb_update_asid_q <= tlb_update_asid_d;
      shared_tlb_access_q <= shared_tlb_access_d;
      shared_tlb_vaddr_q <= shared_tlb_vaddr_d;
      shared_tag_valid_q <= shared_tag_valid_d;
      vpn_q <= vpn_d;
      itlb_req_q <= itlb_req_d;
      dtlb_req_q <= dtlb_req_d;
      i_req_q <= i_req_d;
      shared_tag_valid <= shared_tag_valid_q[tag_rd_addr];

      if (CVA6Cfg.RVH) tlb_update_vmid_q <= tlb_update_vmid_d;
    end
  end

  // ------------------
  // Update and Flush
  // ------------------
  always_comb begin : update_flush
    shared_tag_valid_d = shared_tag_valid_q;
    tag_wr_en = '0;
    pte_wr_en = '0;

    if (flush_i || flush_vvma_i || flush_gvma_i) begin
      shared_tag_valid_d = '0;
    end else if (shared_tlb_update_i.valid) begin
      for (int unsigned i = 0; i < SHARED_TLB_WAYS; i++) begin
        if (repl_way_oh_d[i]) begin
          shared_tag_valid_d[shared_tlb_update_i.vpn[$clog2(CVA6Cfg.SharedTlbDepth)-1:0]][i] = 1'b1;
          tag_wr_en[i] = 1'b1;
          pte_wr_en[i] = 1'b1;
        end
      end
    end
  end  //update_flush

  assign shared_tag_wr.asid = shared_tlb_update_i.asid;
  assign shared_tag_wr.vmid = shared_tlb_update_i.vmid;
  assign shared_tag_wr.is_page = shared_tlb_update_i.is_page;
  assign shared_tag_wr.v_st_enbl = v_st_enbl[i_req_q][HYP_EXT*2:0];

  genvar z;
  generate
    for (z = 0; z < CVA6Cfg.PtLevels; z++) begin : gen_shared_tag
      assign shared_tag_wr.vpn[z] = shared_tlb_update_i.vpn[((CVA6Cfg.VpnLen/CVA6Cfg.PtLevels)*(z+1))-1:((CVA6Cfg.VpnLen/CVA6Cfg.PtLevels)*z)];
    end
    if (CVA6Cfg.RVH) begin : gen_shared_tag_hyp
      //THIS UPDATES THE EXTRA BITS OF VPN IN SV39x4
      assign shared_tag_wr.vpn[CVA6Cfg.PtLevels][(CVA6Cfg.VpnLen%CVA6Cfg.PtLevels)-1:0] = shared_tlb_update_i.vpn[CVA6Cfg.VpnLen-1: CVA6Cfg.VpnLen-(CVA6Cfg.VpnLen%CVA6Cfg.PtLevels)];
    end
  endgenerate


  assign tag_wr_addr = shared_tlb_update_i.vpn[$clog2(CVA6Cfg.SharedTlbDepth)-1:0];
  assign tag_wr_data = shared_tag_wr;

  assign pte_wr_addr = shared_tlb_update_i.vpn[$clog2(CVA6Cfg.SharedTlbDepth)-1:0];

  assign pte_wr_data[0] = shared_tlb_update_i.content[CVA6Cfg.XLEN-1:0];
  assign pte_wr_data[1] = shared_tlb_update_i.g_content[CVA6Cfg.XLEN-1:0];



  assign way_valid = shared_tag_valid_q[shared_tlb_update_i.vpn[$clog2(
      CVA6Cfg.SharedTlbDepth
  )-1:0]];
  assign repl_way = (all_ways_valid) ? rnd_way : inv_way;
  assign update_lfsr = shared_tlb_update_i.valid & all_ways_valid;
  assign repl_way_oh_d = (shared_tlb_update_i.valid) ? shared_tlb_way_bin2oh(repl_way) : '0;

  lzc #(
      .WIDTH(SHARED_TLB_WAYS)
  ) i_lzc (
      .in_i   (~way_valid),
      .cnt_o  (inv_way),
      .empty_o(all_ways_valid)
  );

  lfsr #(
      .LfsrWidth(8),
      .OutWidth ($clog2(SHARED_TLB_WAYS))
  ) i_lfsr (
      .clk_i (clk_i),
      .rst_ni(rst_ni),
      .en_i  (update_lfsr),
      .out_o (rnd_way)
  );

  ///////////////////////////////////////////////////////
  // memory arrays and regs
  ///////////////////////////////////////////////////////

  assign tag_req  = tag_wr_en | tag_rd_en;
  assign tag_we   = tag_wr_en;
  assign tag_addr = tag_wr_en ? tag_wr_addr : tag_rd_addr;

  assign pte_req  = pte_wr_en | pte_rd_en;
  assign pte_we   = pte_wr_en;
  assign pte_addr = pte_wr_en ? pte_wr_addr : pte_rd_addr;

  for (genvar i = 0; i < SHARED_TLB_WAYS; i++) begin : gen_sram
    if (CVA6Cfg.UseSharedTlb) begin
      // Tag RAM
      sram #(
          .DATA_WIDTH($bits(shared_tag_t)),
          .NUM_WORDS (CVA6Cfg.SharedTlbDepth)
      ) tag_sram (
          .clk_i  (clk_i),
          .rst_ni (rst_ni),
          .req_i  (tag_req[i]),
          .we_i   (tag_we[i]),
          .addr_i (tag_addr),
          .wuser_i('0),
          .wdata_i(tag_wr_data),
          .be_i   ('1),
          .ruser_o(),
          .rdata_o(tag_rd_data[i])
      );

      assign shared_tag_rd[i] = shared_tag_t'(tag_rd_data[i]);

      for (genvar a = 0; a < HYP_EXT + 1; a++) begin : g_content_sram
        // PTE RAM
        sram #(
            .DATA_WIDTH(CVA6Cfg.XLEN),
            .NUM_WORDS (CVA6Cfg.SharedTlbDepth)
        ) pte_sram (
            .clk_i  (clk_i),
            .rst_ni (rst_ni),
            .req_i  (pte_req[i]),
            .we_i   (pte_we[i]),
            .addr_i (pte_addr),
            .wuser_i('0),
            .wdata_i(pte_wr_data[a]),
            .be_i   ('1),
            .ruser_o(),
            .rdata_o(pte_rd_data[i][a])
        );
        assign pte[i][a] = pte_cva6_t'(pte_rd_data[i][a]);
      end
    end
  end
endmodule

/* verilator lint_on WIDTH */
