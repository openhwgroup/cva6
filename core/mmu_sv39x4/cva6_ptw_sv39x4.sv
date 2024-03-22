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
// Acknowledges: Technology Innovation Institute (TII)
//
// Description: Hardware-PTW (Page-Table-Walker) for MMU Sv39x4.
//              This module is an adaptation of the Sv39 PTW developed
//              by Florian Zaruba and David Schaffenrath to the Sv39x4 standard.
//

/* verilator lint_off WIDTH */

module cva6_ptw_sv39x4
  import ariane_pkg::*;
#(
    parameter config_pkg::cva6_cfg_t CVA6Cfg = config_pkg::cva6_cfg_empty,
    parameter type dcache_req_i_t = logic,
    parameter type dcache_req_o_t = logic,
    parameter type tlb_update_t = logic
) (
    input logic clk_i,  // Clock
    input logic rst_ni,  // Asynchronous reset active low
    input logic flush_i,  // flush everything, we need to do this because
                          // actually everything we do is speculative at this stage
                          // e.g.: there could be a CSR instruction that changes everything
    output logic ptw_active_o,
    output logic walking_instr_o,  // set when walking for TLB
    output logic ptw_error_o,  // set when an error occurred
    output logic ptw_error_at_g_st_o,  // set when an error occurred at the G-Stage
    output logic                    ptw_err_at_g_int_st_o,  // set when an error occurred at the G-Stage during S-Stage translation
    output logic ptw_access_exception_o,  // set when an PMP access exception occured
    input logic enable_translation_i,  // CSRs indicate to enable SV39 VS-Stage translation
    input logic enable_g_translation_i,  // CSRs indicate to enable SV39  G-Stage translation
    input logic en_ld_st_translation_i,  // enable virtual memory translation for load/stores
    input logic en_ld_st_g_translation_i,  // enable G-Stage translation for load/stores
    input logic v_i,  // current virtualization mode bit
    input logic ld_st_v_i,  // load/store virtualization mode bit
    input logic hlvx_inst_i,  // is a HLVX load/store instruction

    input  logic          lsu_is_store_i,  // this translation was triggered by a store
    // PTW memory interface
    input  dcache_req_o_t req_port_i,
    output dcache_req_i_t req_port_o,


    // to TLBs, update logic
    output tlb_update_t itlb_update_o,
    output tlb_update_t dtlb_update_o,

    output logic [CVA6Cfg.VLEN-1:0] update_vaddr_o,

    input logic [CVA6Cfg.ASID_WIDTH-1:0] asid_i,
    input logic [CVA6Cfg.ASID_WIDTH-1:0] vs_asid_i,
    input logic [CVA6Cfg.VMID_WIDTH-1:0] vmid_i,
    // from TLBs
    // did we miss?
    input logic                          itlb_access_i,
    input logic                          itlb_hit_i,
    input logic [      CVA6Cfg.VLEN-1:0] itlb_vaddr_i,

    input  logic                    dtlb_access_i,
    input  logic                    dtlb_hit_i,
    input  logic [CVA6Cfg.VLEN-1:0] dtlb_vaddr_i,
    // from CSR file
    input  logic [CVA6Cfg.PPNW-1:0] satp_ppn_i,     // ppn from satp
    input  logic [CVA6Cfg.PPNW-1:0] vsatp_ppn_i,    // ppn from satp
    input  logic [CVA6Cfg.PPNW-1:0] hgatp_ppn_i,    // ppn from hgatp
    input  logic                    mxr_i,
    input  logic                    vmxr_i,
    // Performance counters
    output logic                    itlb_miss_o,
    output logic                    dtlb_miss_o,
    // PMP

    input riscv::pmpcfg_t [15:0] pmpcfg_i,
    input logic [15:0][CVA6Cfg.PLEN-3:0] pmpaddr_i,
    output logic [CVA6Cfg.GPLEN-1:0] bad_gpaddr_o

);

  // input registers
  logic data_rvalid_q;
  logic [63:0] data_rdata_q;

  riscv::pte_t pte;
  // register to perform context switch between stages
  riscv::pte_t gpte_q, gpte_d;
  assign pte = riscv::pte_t'(data_rdata_q);

  enum logic [2:0] {
    IDLE,
    WAIT_GRANT,
    PTE_LOOKUP,
    WAIT_RVALID,
    PROPAGATE_ERROR,
    PROPAGATE_ACCESS_ERROR
  }
      state_q, state_d;

  // SV39 defines three levels of page tables
  enum logic [1:0] {
    LVL1,
    LVL2,
    LVL3
  }
      ptw_lvl_q, ptw_lvl_n, gptw_lvl_n, gptw_lvl_q;

  // define 3 PTW stages
  // S_STAGE -> S/VS-stage normal translation controlled by the satp/vsatp CSRs
  // G_INTERMED_STAGE -> Converts the S/VS-stage non-leaf GPA pointers to HPA (controlled by hgatp)
  // G_FINAL_STAGE -> Converts the S/VS-stage final GPA to HPA (controlled by hgatp)
  enum logic [1:0] {
    S_STAGE,
    G_INTERMED_STAGE,
    G_FINAL_STAGE
  }
      ptw_stage_q, ptw_stage_d;

  // is this an instruction page table walk?
  logic is_instr_ptw_q, is_instr_ptw_n;
  logic global_mapping_q, global_mapping_n;
  // latched tag signal
  logic tag_valid_n, tag_valid_q;
  // register the ASID
  logic [CVA6Cfg.ASID_WIDTH-1:0] tlb_update_asid_q, tlb_update_asid_n;
  // register the VMID
  logic [CVA6Cfg.VMID_WIDTH-1:0] tlb_update_vmid_q, tlb_update_vmid_n;
  // register the VPN we need to walk, SV39 defines a 39 bit virtual address
  logic [CVA6Cfg.VLEN-1:0] vaddr_q, vaddr_n;
  // register the VPN we need to walk, SV39x4 defines a 41 bit virtual address for the G-Stage
  logic [CVA6Cfg.GPLEN-1:0] gpaddr_q, gpaddr_n;
  // 4 byte aligned physical pointer
  logic [CVA6Cfg.PLEN-1:0] ptw_pptr_q, ptw_pptr_n;
  logic [CVA6Cfg.PLEN-1:0] gptw_pptr_q, gptw_pptr_n;

  // Assignments
  assign update_vaddr_o = vaddr_q;

  assign ptw_active_o = (state_q != IDLE);
  assign walking_instr_o = is_instr_ptw_q;
  // directly output the correct physical address
  assign req_port_o.address_index = ptw_pptr_q[CVA6Cfg.DCACHE_INDEX_WIDTH-1:0];
  assign req_port_o.address_tag   = ptw_pptr_q[CVA6Cfg.DCACHE_INDEX_WIDTH+CVA6Cfg.DCACHE_TAG_WIDTH-1:CVA6Cfg.DCACHE_INDEX_WIDTH];
  // we are never going to kill this request
  assign req_port_o.kill_req = '0;
  // we are never going to write with the HPTW
  assign req_port_o.data_wdata = 64'b0;

  // -----------
  // TLB Update
  // -----------
  always_comb begin : tlb_update

    itlb_update_o.vpn = {{41 - CVA6Cfg.SVX{1'b0}}, vaddr_q[CVA6Cfg.SVX-1:12]};
    dtlb_update_o.vpn = {{41 - CVA6Cfg.SVX{1'b0}}, vaddr_q[CVA6Cfg.SVX-1:12]};
    // update the correct page table level
    if (enable_g_translation_i && enable_translation_i) begin
      itlb_update_o.is_s_2M = (gptw_lvl_q == LVL2);
      itlb_update_o.is_s_1G = (gptw_lvl_q == LVL1);
      itlb_update_o.is_g_2M = (ptw_lvl_q == LVL2);
      itlb_update_o.is_g_1G = (ptw_lvl_q == LVL1);
    end else if (enable_translation_i) begin
      itlb_update_o.is_s_2M = (ptw_lvl_q == LVL2);
      itlb_update_o.is_s_1G = (ptw_lvl_q == LVL1);
      itlb_update_o.is_g_2M = 1'b0;
      itlb_update_o.is_g_1G = 1'b0;
    end else begin
      itlb_update_o.is_s_2M = 1'b0;
      itlb_update_o.is_s_1G = 1'b0;
      itlb_update_o.is_g_2M = (ptw_lvl_q == LVL2);
      itlb_update_o.is_g_1G = (ptw_lvl_q == LVL1);
    end

    if (en_ld_st_g_translation_i && en_ld_st_translation_i) begin
      dtlb_update_o.is_s_2M = (gptw_lvl_q == LVL2);
      dtlb_update_o.is_s_1G = (gptw_lvl_q == LVL1);
      dtlb_update_o.is_g_2M = (ptw_lvl_q == LVL2);
      dtlb_update_o.is_g_1G = (ptw_lvl_q == LVL1);
    end else if (en_ld_st_translation_i) begin
      dtlb_update_o.is_s_2M = (ptw_lvl_q == LVL2);
      dtlb_update_o.is_s_1G = (ptw_lvl_q == LVL1);
      dtlb_update_o.is_g_2M = 1'b0;
      dtlb_update_o.is_g_1G = 1'b0;
    end else begin
      dtlb_update_o.is_s_2M = 1'b0;
      dtlb_update_o.is_s_1G = 1'b0;
      dtlb_update_o.is_g_2M = (ptw_lvl_q == LVL2);
      dtlb_update_o.is_g_1G = (ptw_lvl_q == LVL1);
    end
    // output the correct ASID
    itlb_update_o.asid = tlb_update_asid_q;
    dtlb_update_o.asid = tlb_update_asid_q;
    // output the correct VMID
    itlb_update_o.vmid = tlb_update_vmid_q;
    dtlb_update_o.vmid = tlb_update_vmid_q;
    // set the global mapping bit
    if (enable_g_translation_i) begin
      itlb_update_o.content   = gpte_q | (global_mapping_q << 5);
      itlb_update_o.g_content = pte;
    end else begin
      itlb_update_o.content   = pte | (global_mapping_q << 5);
      itlb_update_o.g_content = '0;
    end
    if (en_ld_st_g_translation_i) begin
      dtlb_update_o.content   = gpte_q | (global_mapping_q << 5);
      dtlb_update_o.g_content = pte;
    end else begin
      dtlb_update_o.content   = pte | (global_mapping_q << 5);
      dtlb_update_o.g_content = '0;
    end
  end

  assign req_port_o.tag_valid = tag_valid_q;

  logic allow_access;

  assign bad_gpaddr_o = ptw_error_at_g_st_o ? ((ptw_stage_q == G_INTERMED_STAGE) ? gptw_pptr_q[CVA6Cfg.GPLEN:0] : gpaddr_q) : 'b0;

  pmp #(
      .CVA6Cfg   (CVA6Cfg),
      .PLEN      (CVA6Cfg.PLEN),
      .PMP_LEN   (CVA6Cfg.PLEN - 2),
      .NR_ENTRIES(CVA6Cfg.NrPMPEntries)
  ) i_pmp_ptw (
      .addr_i       (ptw_pptr_q),
      // PTW access are always checked as if in S-Mode...
      .priv_lvl_i   (riscv::PRIV_LVL_S),
      // ...and they are always loads
      .access_type_i(riscv::ACCESS_READ),
      // Configuration
      .conf_addr_i  (pmpaddr_i),
      .conf_i       (pmpcfg_i),
      .allow_o      (allow_access)
  );

  //-------------------
  // Page table walker
  //-------------------
  // A virtual address va is translated into a physical address pa as follows:
  // 1. Let a be sptbr.ppn × PAGESIZE, and let i = LEVELS-1. (For Sv39,
  //    PAGESIZE=2^12 and LEVELS=3.)
  // 2. Let pte be the value of the PTE at address a+va.vpn[i]×PTESIZE. (For
  //    Sv32, PTESIZE=4.)
  // 3. If pte.v = 0, or if pte.r = 0 and pte.w = 1, or if any bits or encodings 
  //    that are reserved for future standard use are set within pte, stop and raise 
  //    a page-fault exception corresponding to the original access type.
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
    automatic logic [ CVA6Cfg.PLEN-1:0] pptr;
    automatic logic [CVA6Cfg.GPLEN-1:0] gpaddr;
    // default assignments
    // PTW memory interface
    tag_valid_n            = 1'b0;
    req_port_o.data_req    = 1'b0;
    req_port_o.data_be     = 8'hFF;
    req_port_o.data_size   = 2'b11;
    req_port_o.data_we     = 1'b0;
    ptw_error_o            = 1'b0;
    ptw_error_at_g_st_o    = 1'b0;
    ptw_err_at_g_int_st_o  = 1'b0;
    ptw_access_exception_o = 1'b0;
    itlb_update_o.valid    = 1'b0;
    dtlb_update_o.valid    = 1'b0;
    is_instr_ptw_n         = is_instr_ptw_q;
    ptw_lvl_n              = ptw_lvl_q;
    gptw_lvl_n             = gptw_lvl_q;
    ptw_pptr_n             = ptw_pptr_q;
    gptw_pptr_n            = gptw_pptr_q;
    state_d                = state_q;
    ptw_stage_d            = ptw_stage_q;
    gpte_d                 = gpte_q;
    global_mapping_n       = global_mapping_q;
    // input registers
    tlb_update_asid_n      = tlb_update_asid_q;
    tlb_update_vmid_n      = tlb_update_vmid_q;
    vaddr_n                = vaddr_q;
    gpaddr_n               = gpaddr_q;
    pptr                   = ptw_pptr_q;
    gpaddr                 = gpaddr_q;

    itlb_miss_o            = 1'b0;
    dtlb_miss_o            = 1'b0;

    case (state_q)

      IDLE: begin
        // by default we start with the top-most page table
        ptw_lvl_n        = LVL1;
        gptw_lvl_n       = LVL1;
        global_mapping_n = 1'b0;
        is_instr_ptw_n   = 1'b0;
        gpaddr_n         = '0;
        gpte_d           = '0;
        // if we got an ITLB miss
        if ((enable_translation_i | enable_g_translation_i) & itlb_access_i & ~itlb_hit_i & ~dtlb_access_i) begin
          if (enable_translation_i && enable_g_translation_i) begin
            ptw_stage_d = G_INTERMED_STAGE;
            pptr = {vsatp_ppn_i, itlb_vaddr_i[CVA6Cfg.SV-1:30], 3'b0};
            gptw_pptr_n = pptr;
            ptw_pptr_n = {hgatp_ppn_i[CVA6Cfg.PPNW-1:2], pptr[CVA6Cfg.SVX-1:30], 3'b0};
          end else if (!enable_translation_i && enable_g_translation_i) begin
            ptw_stage_d = G_FINAL_STAGE;
            gpaddr_n = itlb_vaddr_i[CVA6Cfg.SVX-1:0];
            ptw_pptr_n = {hgatp_ppn_i[CVA6Cfg.PPNW-1:2], itlb_vaddr_i[CVA6Cfg.SVX-1:30], 3'b0};
          end else begin
            ptw_stage_d = S_STAGE;
            if (v_i) ptw_pptr_n = {vsatp_ppn_i, itlb_vaddr_i[CVA6Cfg.SV-1:30], 3'b0};
            else ptw_pptr_n = {satp_ppn_i, itlb_vaddr_i[CVA6Cfg.SV-1:30], 3'b0};
          end
          is_instr_ptw_n    = 1'b1;
          tlb_update_asid_n = v_i ? vs_asid_i : asid_i;
          tlb_update_vmid_n = vmid_i;
          vaddr_n           = itlb_vaddr_i;
          state_d           = WAIT_GRANT;
          itlb_miss_o       = 1'b1;
          // we got an DTLB miss
        end else if ((en_ld_st_translation_i || en_ld_st_g_translation_i) & dtlb_access_i & ~dtlb_hit_i) begin
          if (en_ld_st_translation_i && en_ld_st_g_translation_i) begin
            ptw_stage_d = G_INTERMED_STAGE;
            pptr = {vsatp_ppn_i, dtlb_vaddr_i[CVA6Cfg.SV-1:30], 3'b0};
            gptw_pptr_n = pptr;
            ptw_pptr_n = {hgatp_ppn_i[CVA6Cfg.PPNW-1:2], pptr[CVA6Cfg.SVX-1:30], 3'b0};
          end else if (!en_ld_st_translation_i && en_ld_st_g_translation_i) begin
            ptw_stage_d = G_FINAL_STAGE;
            gpaddr_n = dtlb_vaddr_i[CVA6Cfg.SVX-1:0];
            ptw_pptr_n = {hgatp_ppn_i[CVA6Cfg.PPNW-1:2], dtlb_vaddr_i[CVA6Cfg.SVX-1:30], 3'b0};
          end else begin
            ptw_stage_d = S_STAGE;
            if (ld_st_v_i) ptw_pptr_n = {vsatp_ppn_i, dtlb_vaddr_i[CVA6Cfg.SV-1:30], 3'b0};
            else ptw_pptr_n = {satp_ppn_i, dtlb_vaddr_i[CVA6Cfg.SV-1:30], 3'b0};
          end
          tlb_update_asid_n = ld_st_v_i ? vs_asid_i : asid_i;
          tlb_update_vmid_n = vmid_i;
          vaddr_n           = dtlb_vaddr_i;
          state_d           = WAIT_GRANT;
          dtlb_miss_o       = 1'b1;
        end
      end

      WAIT_GRANT: begin
        // send a request out
        req_port_o.data_req = 1'b1;
        // wait for the WAIT_GRANT
        if (req_port_i.data_gnt) begin
          // send the tag valid signal one cycle later
          tag_valid_n = 1'b1;
          state_d     = PTE_LOOKUP;
        end
      end

      PTE_LOOKUP: begin
        // we wait for the valid signal
        if (data_rvalid_q) begin

          // check if the global mapping bit is set
          if (pte.g && ptw_stage_q == S_STAGE) global_mapping_n = 1'b1;

          // -------------
          // Invalid PTE
          // -------------
          // If pte.v = 0, or if pte.r = 0 and pte.w = 1, stop and raise a page-fault exception.
          if (!pte.v || (!pte.r && pte.w) || (|pte.reserved)) state_d = PROPAGATE_ERROR;
          // -----------
          // Valid PTE
          // -----------
          else begin
            state_d = IDLE;
            // it is a valid PTE
            // if pte.r = 1 or pte.x = 1 it is a valid PTE
            if (pte.r || pte.x) begin
              case (ptw_stage_q)
                S_STAGE: begin
                  if ((is_instr_ptw_q && enable_g_translation_i) || (!is_instr_ptw_q && en_ld_st_g_translation_i)) begin
                    state_d = WAIT_GRANT;
                    ptw_stage_d = G_FINAL_STAGE;
                    gpte_d = pte;
                    gptw_lvl_n = ptw_lvl_q;
                    gpaddr = {pte.ppn[CVA6Cfg.GPPNW-1:0], vaddr_q[11:0]};
                    if (ptw_lvl_q == LVL2) gpaddr[20:0] = vaddr_q[20:0];
                    if (ptw_lvl_q == LVL1) gpaddr[29:0] = vaddr_q[29:0];
                    gpaddr_n   = gpaddr;
                    ptw_pptr_n = {hgatp_ppn_i[CVA6Cfg.PPNW-1:2], gpaddr[CVA6Cfg.SVX-1:30], 3'b0};
                    ptw_lvl_n  = LVL1;
                  end
                end
                G_INTERMED_STAGE: begin
                  state_d = WAIT_GRANT;
                  ptw_stage_d = S_STAGE;
                  ptw_lvl_n = gptw_lvl_q;
                  pptr = {pte.ppn[CVA6Cfg.GPPNW-1:0], gptw_pptr_q[11:0]};
                  if (ptw_lvl_q == LVL2) pptr[20:0] = gptw_pptr_q[20:0];
                  if (ptw_lvl_q == LVL1) pptr[29:0] = gptw_pptr_q[29:0];
                  ptw_pptr_n = pptr;
                end
                default: ;
              endcase
              // Valid translation found (either 1G, 2M or 4K entry)
              if (is_instr_ptw_q) begin
                // ------------
                // Update ITLB
                // ------------
                // If page is not executable, we can directly raise an error. This
                // doesn't put a useless entry into the TLB. The same idea applies
                // to the access flag since we let the access flag be managed by SW.
                if (!pte.x || !pte.a) begin
                  state_d = PROPAGATE_ERROR;
                  ptw_stage_d = ptw_stage_q;
                end else if ((ptw_stage_q == G_FINAL_STAGE) || !enable_g_translation_i)
                  itlb_update_o.valid = 1'b1;

              end else begin
                // ------------
                // Update DTLB
                // ------------
                // Check if the access flag has been set, otherwise throw a page-fault
                // and let the software handle those bits.
                // If page is not readable (there are no write-only pages)
                // we can directly raise an error. This doesn't put a useless
                // entry into the TLB.
                if (pte.a && ((pte.r && !hlvx_inst_i) || (pte.x && (mxr_i || hlvx_inst_i || (ptw_stage_q == S_STAGE && vmxr_i && ld_st_v_i))))) begin
                  if ((ptw_stage_q == G_FINAL_STAGE) || !en_ld_st_g_translation_i)
                    dtlb_update_o.valid = 1'b1;
                end else begin
                  state_d = PROPAGATE_ERROR;
                  ptw_stage_d = ptw_stage_q;
                end
                // Request is a store: perform some additional checks
                // If the request was a store and the page is not write-able, raise an error
                // the same applies if the dirty flag is not set
                if (lsu_is_store_i && (!pte.w || !pte.d)) begin
                  dtlb_update_o.valid = 1'b0;
                  state_d = PROPAGATE_ERROR;
                  ptw_stage_d = ptw_stage_q;
                end
              end
              // check if the ppn is correctly aligned:
              // 6. If i > 0 and pa.ppn[i − 1 : 0] != 0, this is a misaligned superpage; stop and raise a page-fault
              // exception.
              if (ptw_lvl_q == LVL1 && pte.ppn[17:0] != '0) begin
                state_d             = PROPAGATE_ERROR;
                ptw_stage_d         = ptw_stage_q;
                dtlb_update_o.valid = 1'b0;
                itlb_update_o.valid = 1'b0;
              end else if (ptw_lvl_q == LVL2 && pte.ppn[8:0] != '0) begin
                state_d             = PROPAGATE_ERROR;
                ptw_stage_d         = ptw_stage_q;
                dtlb_update_o.valid = 1'b0;
                itlb_update_o.valid = 1'b0;
              end
              // check if 63:41 are all zeros
              if (((v_i && is_instr_ptw_q) || (ld_st_v_i && !is_instr_ptw_q)) && ptw_stage_q == S_STAGE && !((|pte.ppn[CVA6Cfg.PPNW-1:CVA6Cfg.GPPNW]) == 1'b0)) begin
                state_d = PROPAGATE_ERROR;
                ptw_stage_d = G_FINAL_STAGE;
              end
              // this is a pointer to the next TLB level
            end else begin
              // pointer to next level of page table
              if (ptw_lvl_q == LVL1) begin
                // we are in the second level now
                ptw_lvl_n = LVL2;
                case (ptw_stage_q)
                  S_STAGE: begin
                    if ((is_instr_ptw_q && enable_g_translation_i) || (!is_instr_ptw_q && en_ld_st_g_translation_i)) begin
                      ptw_stage_d = G_INTERMED_STAGE;
                      gpte_d = pte;
                      gptw_lvl_n = LVL2;
                      pptr = {pte.ppn, vaddr_q[29:21], 3'b0};
                      gptw_pptr_n = pptr;
                      ptw_pptr_n = {hgatp_ppn_i[CVA6Cfg.PPNW-1:2], pptr[CVA6Cfg.SVX-1:30], 3'b0};
                      ptw_lvl_n = LVL1;
                    end else begin
                      ptw_pptr_n = {pte.ppn, vaddr_q[29:21], 3'b0};
                    end
                  end
                  G_INTERMED_STAGE: begin
                    ptw_pptr_n = {pte.ppn, gptw_pptr_q[29:21], 3'b0};
                  end
                  G_FINAL_STAGE: begin
                    ptw_pptr_n = {pte.ppn, gpaddr_q[29:21], 3'b0};
                  end
                  default: ;
                endcase
              end

              if (ptw_lvl_q == LVL2) begin
                // here we received a pointer to the third level
                ptw_lvl_n = LVL3;
                unique case (ptw_stage_q)
                  S_STAGE: begin
                    if ((is_instr_ptw_q && enable_g_translation_i) || (!is_instr_ptw_q && en_ld_st_g_translation_i)) begin
                      ptw_stage_d = G_INTERMED_STAGE;
                      gpte_d = pte;
                      gptw_lvl_n = LVL3;
                      pptr = {pte.ppn, vaddr_q[20:12], 3'b0};
                      gptw_pptr_n = pptr;
                      ptw_pptr_n = {hgatp_ppn_i[CVA6Cfg.PPNW-1:2], pptr[CVA6Cfg.SVX-1:30], 3'b0};
                      ptw_lvl_n = LVL1;
                    end else begin
                      ptw_pptr_n = {pte.ppn, vaddr_q[20:12], 3'b0};
                    end
                  end
                  G_INTERMED_STAGE: begin
                    ptw_pptr_n = {pte.ppn, gptw_pptr_q[20:12], 3'b0};
                  end
                  G_FINAL_STAGE: begin
                    ptw_pptr_n = {pte.ppn, gpaddr_q[20:12], 3'b0};
                  end
                  default: ;
                endcase
              end

              state_d = WAIT_GRANT;
              // check if reserved bits are cleared for non-leaf entries
              if (pte.a || pte.d || pte.u) begin
                state_d = PROPAGATE_ERROR;
                ptw_stage_d = ptw_stage_q;
              end
              if (ptw_lvl_q == LVL3) begin
                // Should already be the last level page table => Error
                ptw_lvl_n = LVL3;
                state_d = PROPAGATE_ERROR;
                ptw_stage_d = ptw_stage_q;
              end
              // check if 63:41 are all zeros
              if (((v_i && is_instr_ptw_q) || (ld_st_v_i && !is_instr_ptw_q)) && ptw_stage_q == S_STAGE && !((|pte.ppn[CVA6Cfg.PPNW-1:CVA6Cfg.GPPNW]) == 1'b0)) begin
                state_d = PROPAGATE_ERROR;
                ptw_stage_d = ptw_stage_q;
              end
            end
          end

          // Check if this access was actually allowed from a PMP perspective
          if (!allow_access) begin
            itlb_update_o.valid = 1'b0;
            dtlb_update_o.valid = 1'b0;
            // we have to return the failed address in bad_addr
            ptw_pptr_n = ptw_pptr_q;
            ptw_stage_d = ptw_stage_q;
            state_d = PROPAGATE_ACCESS_ERROR;
          end
        end
        // we've got a data WAIT_GRANT so tell the cache that the tag is valid
      end
      // Propagate error to MMU/LSU
      PROPAGATE_ERROR: begin
        state_d               = IDLE;
        ptw_error_o           = 1'b1;
        ptw_error_at_g_st_o   = (ptw_stage_q != S_STAGE) ? 1'b1 : 1'b0;
        ptw_err_at_g_int_st_o = (ptw_stage_q == G_INTERMED_STAGE) ? 1'b1 : 1'b0;
      end
      PROPAGATE_ACCESS_ERROR: begin
        state_d                = IDLE;
        ptw_access_exception_o = 1'b1;
      end
      // wait for the rvalid before going back to IDLE
      WAIT_RVALID: begin
        if (data_rvalid_q) state_d = IDLE;
      end
      default: begin
        state_d = IDLE;
      end
    endcase

    // -------
    // Flush
    // -------
    // should we have flushed before we got an rvalid, wait for it until going back to IDLE
    if (flush_i) begin
      // on a flush check whether we are
      // 1. in the PTE Lookup check whether we still need to wait for an rvalid
      // 2. waiting for a grant, if so: wait for it
      // if not, go back to idle
      if (((state_q inside {PTE_LOOKUP, WAIT_RVALID}) && !data_rvalid_q) ||
                ((state_q == WAIT_GRANT) && req_port_i.data_gnt))
        state_d = WAIT_RVALID;
      else state_d = IDLE;
    end
  end

  // sequential process
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (~rst_ni) begin
      state_q           <= IDLE;
      ptw_stage_q       <= S_STAGE;
      is_instr_ptw_q    <= 1'b0;
      ptw_lvl_q         <= LVL1;
      gptw_lvl_q        <= LVL1;
      tag_valid_q       <= 1'b0;
      tlb_update_asid_q <= '0;
      tlb_update_vmid_q <= '0;
      vaddr_q           <= '0;
      gpaddr_q          <= '0;
      ptw_pptr_q        <= '0;
      gptw_pptr_q       <= '0;
      global_mapping_q  <= 1'b0;
      data_rdata_q      <= '0;
      gpte_q            <= '0;
      data_rvalid_q     <= 1'b0;
    end else begin
      state_q           <= state_d;
      ptw_stage_q       <= ptw_stage_d;
      ptw_pptr_q        <= ptw_pptr_n;
      gptw_pptr_q       <= gptw_pptr_n;
      is_instr_ptw_q    <= is_instr_ptw_n;
      ptw_lvl_q         <= ptw_lvl_n;
      gptw_lvl_q        <= gptw_lvl_n;
      tag_valid_q       <= tag_valid_n;
      tlb_update_asid_q <= tlb_update_asid_n;
      tlb_update_vmid_q <= tlb_update_vmid_n;
      vaddr_q           <= vaddr_n;
      gpaddr_q          <= gpaddr_n;
      global_mapping_q  <= global_mapping_n;
      data_rdata_q      <= req_port_i.data_rdata;
      gpte_q            <= gpte_d;
      data_rvalid_q     <= req_port_i.data_rvalid;
    end
  end

endmodule
/* verilator lint_on WIDTH */
