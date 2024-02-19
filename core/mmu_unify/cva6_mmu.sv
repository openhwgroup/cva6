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
// Author: Angela Gonzalez, PlanV Technology
// Date: 14/02/2024
//
// Description: Memory Management Unit for CVA6, contains TLB and
//              address translation unit. SV32 SV39 and SV39x4 as defined in RISC-V
//              privilege specification 1.11-WIP.
//              This module is an merge of the MMU Sv39 developed
//              by Florian Zaruba, the MMU Sv32 developed by Sebastien Jacq and the MMU Sv39x4 developed by Bruno Sá.


module cva6_mmu
  import ariane_pkg::*;
#(
    parameter config_pkg::cva6_cfg_t CVA6Cfg                      = config_pkg::cva6_cfg_empty,
    // parameter ariane_pkg::ariane_cfg_t ArianeCfg = ariane_pkg::ArianeDefaultConfig, //This is the required config param in the hypervisor version for now
    parameter int unsigned           INSTR_TLB_ENTRIES            = 4,
    parameter int unsigned           DATA_TLB_ENTRIES             = 4,
    parameter logic                  HYP_EXT                      = 0,
    parameter int unsigned           ASID_WIDTH       [HYP_EXT:0],
    parameter int unsigned           VPN_LEN                      = 1,
    parameter int unsigned           PT_LEVELS                    = 1

) (
    input logic clk_i,
    input logic rst_ni,
    input logic flush_i,
    input logic [HYP_EXT*2:0] enable_translation_i,  //[v_i,enable_g_translation,enable_translation]
    input  logic   [HYP_EXT*2:0]              en_ld_st_translation_i,   // enable virtual memory translation for load/stores
    // IF interface
    input icache_arsp_t icache_areq_i,
    output icache_areq_t icache_areq_o,
    // input  icache_areq_o_t                  icache_areq_i, this is the data type in the hypervisor version for now
    // output icache_areq_i_t                  icache_areq_o,

    // LSU interface
    // this is a more minimalistic interface because the actual addressing logic is handled
    // in the LSU as we distinguish load and stores, what we do here is simple address translation
    input exception_t misaligned_ex_i,
    input logic lsu_req_i,  // request address translation
    input logic [riscv::VLEN-1:0] lsu_vaddr_i,  // virtual address in
    input riscv::xlen_t lsu_tinst_i,  // transformed instruction in
    input logic lsu_is_store_i,  // the translation is requested by a store
    output logic csr_hs_ld_st_inst_o,  // hyp load store instruction
    // if we need to walk the page table we can't grant in the same cycle
    // Cycle 0
    output logic                            lsu_dtlb_hit_o,   // sent in the same cycle as the request if translation hits in the DTLB
    output logic [riscv::PPNW-1:0] lsu_dtlb_ppn_o,  // ppn (send same cycle as hit)
    // Cycle 1
    output logic lsu_valid_o,  // translation is valid
    output logic [riscv::PLEN-1:0] lsu_paddr_o,  // translated address
    output exception_t lsu_exception_o,  // address translation threw an exception
    // General control signals
    input riscv::priv_lvl_t priv_lvl_i,
    input riscv::priv_lvl_t ld_st_priv_lvl_i,
    input logic [HYP_EXT:0] sum_i,
    input logic [HYP_EXT:0] mxr_i,
    input logic hlvx_inst_i,
    input logic hs_ld_st_inst_i,
    // input logic flag_mprv_i,
    input logic [riscv::PPNW-1:0] satp_ppn_i[HYP_EXT*2:0],  //[hgatp,vsatp,satp]

    input logic [ASID_WIDTH[0]-1:0] asid_i               [HYP_EXT*2:0],  //[vmid,vs_asid,asid]
    input logic [ASID_WIDTH[0]-1:0] asid_to_be_flushed_i [  HYP_EXT:0],
    input logic [  riscv::VLEN-1:0] vaddr_to_be_flushed_i[  HYP_EXT:0],

    input logic [HYP_EXT*2:0] flush_tlb_i,

    // Performance counters
    output logic                                   itlb_miss_o,
    output logic                                   dtlb_miss_o,
    // PTW memory interface
    input  dcache_req_o_t                          req_port_i,
    output dcache_req_i_t                          req_port_o,
    // PMP
    input  riscv::pmpcfg_t [15:0]                  pmpcfg_i,
    input  logic           [15:0][riscv::PLEN-3:0] pmpaddr_i
);
  logic [ASID_WIDTH[0]-1:0] dtlb_mmu_asid_i[HYP_EXT:0];
  logic [ASID_WIDTH[0]-1:0] itlb_mmu_asid_i[HYP_EXT:0];

  genvar b;
  generate
    for (b = 0; b < HYP_EXT + 1; b++) begin
      assign dtlb_mmu_asid_i[b] = b==0 ? 
                                    ((en_ld_st_translation_i[2*HYP_EXT] || flush_tlb_i[HYP_EXT]) ? asid_i[HYP_EXT] : asid_i[0]): 
                                    asid_i[HYP_EXT*2];
      assign itlb_mmu_asid_i[b] = b==0 ?
                                    (enable_translation_i[2*HYP_EXT] ? asid_i[HYP_EXT] : asid_i[0]):
                                    asid_i[HYP_EXT*2];
    end
    endgenerate

  // memory management, pte for cva6
  localparam type pte_cva6_t = struct packed {
        // typedef struct packed {
        logic [riscv::PPNW-1:0] ppn;  // PPN length for
        logic [1:0] rsw;
        logic d;
        logic a;
        logic g;
        logic u;
        logic x;
        logic w;
        logic r;
        logic v;
    } ;

    localparam type tlb_update_cva6_t = struct packed {
    // typedef struct packed {
        logic                  valid;      // valid flag
        logic [PT_LEVELS-2:0][HYP_EXT:0] is_page;      //
        logic [VPN_LEN-1:0]    vpn;        //
        logic [HYP_EXT:0][ASID_WIDTH[0]-1:0]   asid;       //
        logic [HYP_EXT*2:0]               v_st_enbl; // v_i,g-stage enabled, s-stage enabled
        pte_cva6_t  [HYP_EXT:0]          content;
    } ;

    logic [HYP_EXT:0]      iaccess_err;   // insufficient privilege to access this instruction page
    logic [HYP_EXT:0]      daccess_err;   // insufficient privilege to access this data page
    logic                   ptw_active;    // PTW is currently walking a page table
    logic                   walking_instr; // PTW is walking because of an ITLB miss
    logic  [HYP_EXT*2:0]    ptw_error;     // PTW threw an exception
    logic                   ptw_access_exception; // PTW threw an access exception (PMPs)
    logic [HYP_EXT:0][riscv::PLEN-1:0] ptw_bad_paddr; // PTW guest page fault bad guest physical addr

    logic [riscv::VLEN-1:0] update_vaddr, shared_tlb_vaddr;

    tlb_update_cva6_t update_itlb, update_dtlb, update_shared_tlb;

    logic        itlb_lu_access;
    pte_cva6_t  [HYP_EXT:0]  itlb_content ;
    logic [PT_LEVELS-2:0]               itlb_is_page;
    logic        itlb_lu_hit;
    logic [riscv::GPLEN-1:0]  itlb_gpaddr;
    logic [ASID_WIDTH[0]-1:0]    itlb_lu_asid;

    logic        dtlb_lu_access;
    pte_cva6_t  [HYP_EXT:0]  dtlb_content ;
    logic [PT_LEVELS-2:0]               dtlb_is_page;
    logic [ASID_WIDTH[0]-1:0]    dtlb_lu_asid;
    logic        dtlb_lu_hit;
    logic [riscv::GPLEN-1:0] dtlb_gpaddr;

    logic  shared_tlb_access;
    logic        shared_tlb_hit, itlb_req;

    // Assignments

    assign itlb_lu_access = icache_areq_i.fetch_req;
    assign dtlb_lu_access = lsu_req_i;  


    cva6_tlb #(
        .pte_cva6_t(pte_cva6_t),
        .tlb_update_cva6_t(tlb_update_cva6_t),
        .TLB_ENTRIES      ( INSTR_TLB_ENTRIES),
        .HYP_EXT(HYP_EXT),
        .ASID_WIDTH (ASID_WIDTH),
        .VPN_LEN(VPN_LEN),
        .PT_LEVELS(PT_LEVELS)
    ) i_itlb (
        .clk_i            ( clk_i                      ),
        .rst_ni           ( rst_ni                     ),
        .flush_i          ( flush_tlb_i                ),
        .v_st_enbl_i      ( enable_translation_i            ),
        .update_i         ( update_itlb                ),
        .lu_access_i      ( itlb_lu_access             ),
        .lu_asid_i        ( itlb_mmu_asid_i            ),
        .asid_to_be_flushed_i (asid_to_be_flushed_i),
        .vaddr_to_be_flushed_i(vaddr_to_be_flushed_i),
        .lu_vaddr_i       ( icache_areq_i.fetch_vaddr  ),
        .lu_content_o     ( itlb_content               ),
        .lu_gpaddr_o      ( itlb_gpaddr                ),
        .lu_is_page_o     ( itlb_is_page               ),
        .lu_hit_o         ( itlb_lu_hit                )
    );

    cva6_tlb #(
        .pte_cva6_t(pte_cva6_t),
        .tlb_update_cva6_t(tlb_update_cva6_t),
        .TLB_ENTRIES    (DATA_TLB_ENTRIES),
        .HYP_EXT(HYP_EXT),
        .ASID_WIDTH (ASID_WIDTH),
        .VPN_LEN(VPN_LEN),
        .PT_LEVELS(PT_LEVELS)
    ) i_dtlb (
        .clk_i            ( clk_i                       ),
        .rst_ni           ( rst_ni                      ),
        .flush_i          ( flush_tlb_i                 ),
        .v_st_enbl_i      ( en_ld_st_translation_i             ),
        .update_i         ( update_dtlb                 ),
        .lu_access_i      ( dtlb_lu_access              ),
        .lu_asid_i        ( dtlb_mmu_asid_i             ),
        .asid_to_be_flushed_i ( asid_to_be_flushed_i),
        .vaddr_to_be_flushed_i(vaddr_to_be_flushed_i),
        .lu_vaddr_i       ( lsu_vaddr_i                 ),
        .lu_content_o     ( dtlb_content                ),
        .lu_gpaddr_o      ( dtlb_gpaddr                 ),
        .lu_is_page_o     ( dtlb_is_page                ),
        .lu_hit_o         ( dtlb_lu_hit                 )
    );


    cva6_shared_tlb #(
        .SHARED_TLB_DEPTH (64),
        .SHARED_TLB_WAYS  (2),
        .HYP_EXT(HYP_EXT),
        .ASID_WIDTH       (ASID_WIDTH),
        .VPN_LEN          (VPN_LEN),
        .PT_LEVELS        (PT_LEVELS),
        .pte_cva6_t       (pte_cva6_t),
        .tlb_update_cva6_t(tlb_update_cva6_t)
    ) i_shared_tlb (
        .clk_i  (clk_i),
        .rst_ni (rst_ni),
        .flush_i(flush_tlb_i),
        .v_st_enbl_i({enable_translation_i,en_ld_st_translation_i}),

        .dtlb_asid_i       (dtlb_mmu_asid_i),
        .itlb_asid_i       (itlb_mmu_asid_i),
        // from TLBs
        // did we miss?
        .itlb_access_i(itlb_lu_access),
        .itlb_hit_i   (itlb_lu_hit),
        .itlb_vaddr_i (icache_areq_i.fetch_vaddr),

        .dtlb_access_i(dtlb_lu_access),
        .dtlb_hit_i   (dtlb_lu_hit),
        .dtlb_vaddr_i (lsu_vaddr_i),

        // to TLBs, update logic
        .itlb_update_o(update_itlb),
        .dtlb_update_o(update_dtlb),

        // Performance counters
        .itlb_miss_o(itlb_miss_o),
        .dtlb_miss_o(dtlb_miss_o),

        .shared_tlb_access_o(shared_tlb_access),
        .shared_tlb_hit_o   (shared_tlb_hit),
        .shared_tlb_vaddr_o (shared_tlb_vaddr),

        .itlb_req_o         (itlb_req),
        // to update shared tlb
        .shared_tlb_update_i(update_shared_tlb)
    );

    cva6_ptw  #(
        .CVA6Cfg   (CVA6Cfg),
    //   .ArianeCfg              ( ArianeCfg             ), this is the configuration needed in the hypervisor extension for now
        .pte_cva6_t(pte_cva6_t),
        .tlb_update_cva6_t(tlb_update_cva6_t),
        .HYP_EXT(HYP_EXT),
        .ASID_WIDTH             ( ASID_WIDTH            ),
        .VPN_LEN(VPN_LEN),
        .PT_LEVELS(PT_LEVELS)
    ) i_ptw (
        .clk_i                  ( clk_i                 ),
        .rst_ni                 ( rst_ni                ),
        .flush_i(flush_i),

        .ptw_active_o           ( ptw_active            ),
        .walking_instr_o        ( walking_instr         ),
        .ptw_error_o            ( ptw_error             ),
        .ptw_access_exception_o ( ptw_access_exception  ),

        .enable_translation_i  (enable_translation_i),
        .en_ld_st_translation_i(en_ld_st_translation_i),

        .lsu_is_store_i(lsu_is_store_i),
        // PTW memory interface
        .req_port_i             ( req_port_i            ),
        .req_port_o             ( req_port_o            ),
        // .enable_translation_i   ( enable_translation_i  ),
        // .en_ld_st_translation_i ( en_ld_st_translation_i),
        .asid_i                 (asid_i),

        .update_vaddr_o         ( update_vaddr          ),

        // to Shared TLB, update logic
        .shared_tlb_update_o(update_shared_tlb),

        
    // from shared TLB
    // did we miss?
        .shared_tlb_access_i(shared_tlb_access),
        .shared_tlb_hit_i   (shared_tlb_hit),
        .shared_tlb_vaddr_i (shared_tlb_vaddr),

        .itlb_req_i(itlb_req),
        // .dtlb_access_i          ( dtlb_lu_access        ),
        // .dtlb_hit_i             ( dtlb_lu_hit           ),
        // .dtlb_vaddr_i           ( lsu_vaddr_i           ),
        .hlvx_inst_i            ( hlvx_inst_i           ),
        // from CSR file
        .satp_ppn_i             (satp_ppn_i             ),
        .mxr_i                  (mxr_i                  ),

        // Performance counters
        .shared_tlb_miss_o(),  //open for now

    // PMP
        .pmpcfg_i   (pmpcfg_i),
        .pmpaddr_i  (pmpaddr_i),
        .bad_paddr_o(ptw_bad_paddr)

    );

    // ila_1 i_ila_1 (
    //     .clk(clk_i), // input wire clk
    //     .probe0({req_port_o.address_tag, req_port_o.address_index}),
    //     .probe1(req_port_o.data_req), // input wire [63:0]  probe1
    //     .probe2(req_port_i.data_gnt), // input wire [0:0]  probe2
    //     .probe3(req_port_i.data_rdata), // input wire [0:0]  probe3
    //     .probe4(req_port_i.data_rvalid), // input wire [0:0]  probe4
    //     .probe5(ptw_error), // input wire [1:0]  probe5
    //     .probe6(update_vaddr), // input wire [0:0]  probe6
    //     .probe7(update_ptw_itlb.valid), // input wire [0:0]  probe7
    //     .probe8(update_ptw_dtlb.valid), // input wire [0:0]  probe8
    //     .probe9(dtlb_lu_access), // input wire [0:0]  probe9
    //     .probe10(lsu_vaddr_i), // input wire [0:0]  probe10
    //     .probe11(dtlb_lu_hit), // input wire [0:0]  probe11
    //     .probe12(itlb_lu_access), // input wire [0:0]  probe12
    //     .probe13(icache_areq_i.fetch_vaddr), // input wire [0:0]  probe13
    //     .probe14(itlb_lu_hit) // input wire [0:0]  probe13
    // );

    //-----------------------
    // Instruction Interface
    //-----------------------
    logic match_any_execute_region;
    logic pmp_instr_allow;
    localparam PPNWMin = (riscv::PPNW - 1 > 29) ? 29 : riscv::PPNW - 1;

    assign icache_areq_o.fetch_paddr    [11:0] = icache_areq_i.fetch_vaddr[11:0];
    assign icache_areq_o.fetch_paddr [riscv::PLEN-1:PPNWMin+1]   = //
                              (|enable_translation_i[HYP_EXT:0]) ? //
                              (enable_translation_i[HYP_EXT] ? itlb_content[HYP_EXT].ppn[riscv::PPNW-1:(riscv::PPNW - (riscv::PLEN - PPNWMin-1))] :
                              itlb_content[0].ppn[riscv::PPNW-1:(riscv::PPNW - (riscv::PLEN - PPNWMin-1))] ): //
      (riscv::PLEN-PPNWMin-1)'(icache_areq_i.fetch_vaddr[((riscv::PLEN > riscv::VLEN) ? riscv::VLEN : riscv::PLEN )-1:PPNWMin+1]);
  genvar a;
  generate

    for (a = 0; a < PT_LEVELS - 1; a++) begin
      assign icache_areq_o.fetch_paddr [PPNWMin-((VPN_LEN/PT_LEVELS)*(a)):PPNWMin-((VPN_LEN/PT_LEVELS)*(a+1))+1] = //
          (|enable_translation_i[HYP_EXT:0] && (|itlb_is_page[a:0] == 0)) ?  //
          (enable_translation_i[HYP_EXT] ? itlb_content[HYP_EXT].ppn  [(riscv::PPNW - (riscv::PLEN - PPNWMin-1)-((VPN_LEN/PT_LEVELS)*(a))-1):(riscv::PPNW - (riscv::PLEN - PPNWMin-1)-((VPN_LEN/PT_LEVELS)*(a+1)))]:
                            itlb_content[0].ppn  [(riscv::PPNW - (riscv::PLEN - PPNWMin-1)-((VPN_LEN/PT_LEVELS)*(a))-1):(riscv::PPNW - (riscv::PLEN - PPNWMin-1)-((VPN_LEN/PT_LEVELS)*(a+1)))]) : //
          icache_areq_i.fetch_vaddr[PPNWMin-((VPN_LEN/PT_LEVELS)*(a)):PPNWMin-((VPN_LEN/PT_LEVELS)*(a+1))+1];
    end

  endgenerate

  // The instruction interface is a simple request response interface
  always_comb begin : instr_interface
    // MMU disabled: just pass through
    icache_areq_o.fetch_valid = icache_areq_i.fetch_req;
    // icache_areq_o.fetch_paddr  = icache_areq_i.fetch_vaddr[riscv::PLEN-1:0]; // play through in case we disabled address translation
    // // two potential exception sources:
    // 1. HPTW threw an exception -> signal with a page fault exception
    // 2. We got an access error because of insufficient permissions -> throw an access exception
    icache_areq_o.fetch_exception = '0;
    // Check whether we are allowed to access this memory region from a fetch perspective
    iaccess_err[0]   = icache_areq_i.fetch_req && (enable_translation_i[0] || HYP_EXT==0) && (((priv_lvl_i == riscv::PRIV_LVL_U) && ~itlb_content[0].u)
                                                    || ((priv_lvl_i == riscv::PRIV_LVL_S) && itlb_content[0].u));

    if (HYP_EXT == 1)
      iaccess_err[HYP_EXT] = icache_areq_i.fetch_req && enable_translation_i[HYP_EXT] && !itlb_content[HYP_EXT].u;
    // MMU enabled: address from TLB, request delayed until hit. Error when TLB
    // hit and no access right or TLB hit and translated address not valid (e.g.
    // AXI decode error), or when PTW performs walk due to ITLB miss and raises
    // an error.
    if ((|enable_translation_i[HYP_EXT:0])) begin
      // we work with SV39 or SV32, so if VM is enabled, check that all bits [riscv::VLEN-1:riscv::SV-1] are equal
      if (icache_areq_i.fetch_req && !((&icache_areq_i.fetch_vaddr[riscv::VLEN-1:riscv::SV-1]) == 1'b1 || (|icache_areq_i.fetch_vaddr[riscv::VLEN-1:riscv::SV-1]) == 1'b0)) begin
        if (HYP_EXT == 1) begin
          icache_areq_o.fetch_exception = {
            riscv::INSTR_ACCESS_FAULT,
            {{riscv::XLEN - riscv::VLEN{1'b0}}, icache_areq_i.fetch_vaddr},
            {riscv::GPLEN{1'b0}},
            {{riscv::XLEN{1'b0}}},
            enable_translation_i[HYP_EXT*2],
            1'b1
          };
        end else begin
          icache_areq_o.fetch_exception = {
            riscv::INSTR_ACCESS_FAULT,
            {{riscv::XLEN - riscv::VLEN{1'b0}}, icache_areq_i.fetch_vaddr},
            1'b1
          };
        end


            icache_areq_o.fetch_valid = 1'b0;


            // ---------
            // ITLB Hit
            // --------
            // if we hit the ITLB output the request signal immediately
            if (itlb_lu_hit) begin
                icache_areq_o.fetch_valid = icache_areq_i.fetch_req;
                if (HYP_EXT==1 && iaccess_err[HYP_EXT]) begin
                    icache_areq_o.fetch_exception = {
                        riscv::INSTR_GUEST_PAGE_FAULT,
                        {{riscv::XLEN-riscv::VLEN{1'b0}}, icache_areq_i.fetch_vaddr},
                        itlb_gpaddr[riscv::GPLEN-1:0],
                        {riscv::XLEN{1'b0}},
                        enable_translation_i[HYP_EXT*2],
                        1'b1
                    };
                    // we got an access error
                end else if (iaccess_err[0]) begin
                    // throw a page fault
                    if(HYP_EXT==1) begin
                        icache_areq_o.fetch_exception = {
                            riscv::INSTR_PAGE_FAULT,
                            {{riscv::XLEN-riscv::VLEN{1'b0}}, icache_areq_i.fetch_vaddr},
                            {riscv::GPLEN{1'b0}},
                            {riscv::XLEN{1'b0}},
                            enable_translation_i[HYP_EXT*2],
                            1'b1
                        };
                    end
                    else begin
                        icache_areq_o.fetch_exception = {
                            riscv::INSTR_PAGE_FAULT,
                            {{riscv::XLEN - riscv::VLEN{1'b0}}, icache_areq_i.fetch_vaddr},
                            1'b1
                            };
                    end

                end else if (!pmp_instr_allow) begin
                    if(HYP_EXT==1) begin
                        icache_areq_o.fetch_exception = {
                            riscv::INSTR_ACCESS_FAULT,
                            {riscv::XLEN '(icache_areq_i.fetch_vaddr)},
                            {riscv::GPLEN{1'b0}},
                            {riscv::XLEN{1'b0}},
                            enable_translation_i[HYP_EXT*2],
                            1'b1
                        };
                    end
                    else begin
                        icache_areq_o.fetch_exception = {
                            riscv::INSTR_ACCESS_FAULT, riscv::XLEN '(icache_areq_i.fetch_vaddr), 1'b1
                        }; 
                    end
                end
            end else
            // ---------
            // ITLB Miss
            // ---------
            // watch out for exceptions happening during walking the page table
            if (ptw_active && walking_instr) begin
                icache_areq_o.fetch_valid = ptw_error[0] | ptw_access_exception;
                if (ptw_error[0]) begin
                    if (HYP_EXT==1  && ptw_error[HYP_EXT]) begin
                        icache_areq_o.fetch_exception = {
                            riscv::INSTR_GUEST_PAGE_FAULT,
                            {{riscv::XLEN-riscv::VLEN{1'b0}}, update_vaddr},
                            ptw_bad_paddr[HYP_EXT][riscv::GPLEN-1:0],
                            (ptw_error[HYP_EXT*2] ? (riscv::IS_XLEN64 ? riscv::READ_64_PSEUDOINSTRUCTION : riscv::READ_32_PSEUDOINSTRUCTION) : {riscv::XLEN{1'b0}}),
                            enable_translation_i[2*HYP_EXT],
                            1'b1
                        };
                    end else begin
                        if (HYP_EXT==1) begin
                            icache_areq_o.fetch_exception = {
                                riscv::INSTR_PAGE_FAULT,
                                {{riscv::XLEN-riscv::VLEN{1'b0}}, update_vaddr},
                                {riscv::GPLEN{1'b0}},
                                {riscv::XLEN{1'b0}},
                                enable_translation_i[2*HYP_EXT],
                                1'b1
                            };
                        end
                        else begin
                            icache_areq_o.fetch_exception = {
                                riscv::INSTR_PAGE_FAULT, {{riscv::XLEN - riscv::VLEN{1'b0}}, update_vaddr}, 1'b1
                            };
                        end
                    end
                end
                // TODO(moschn,zarubaf): What should the value of tval be in this case?
                else begin
                    if(HYP_EXT==1) begin
                        icache_areq_o.fetch_exception = {
                            riscv::INSTR_ACCESS_FAULT,
                            {{riscv::XLEN-riscv::VLEN{1'b0}}, update_vaddr},
                            {riscv::GPLEN{1'b0}},
                            {riscv::XLEN{1'b0}},
                            enable_translation_i[HYP_EXT*2],
                            1'b1
                        };
                    end
                    else begin
                        icache_areq_o.fetch_exception = {
                            riscv::INSTR_ACCESS_FAULT, ptw_bad_paddr[0][riscv::PLEN-1:(riscv::PLEN > riscv::VLEN) ? (riscv::PLEN - riscv::VLEN) : 0], 1'b1
                        };
                    end
                end
            end
        end
        // if it didn't match any execute region throw an `Instruction Access Fault`
        // or: if we are not translating, check PMPs immediately on the paddr
        if ((!match_any_execute_region && (!ptw_error[0]|| HYP_EXT==0) ) || (!(|enable_translation_i[HYP_EXT:0]) && !pmp_instr_allow)) begin
            if(HYP_EXT==1) begin
                icache_areq_o.fetch_exception = {
                    riscv::INSTR_ACCESS_FAULT,
                    {riscv::XLEN '(icache_areq_o.fetch_paddr)},
                    {riscv::GPLEN{1'b0}},
                    {riscv::XLEN{1'b0}},
                    enable_translation_i[HYP_EXT*2],
                    1'b1
                };
            end 
            else begin
                icache_areq_o.fetch_exception = {
                    riscv::INSTR_ACCESS_FAULT, riscv::VLEN'(icache_areq_o.fetch_paddr[riscv::PLEN-1:(riscv::PLEN > riscv::VLEN) ? (riscv::PLEN - riscv::VLEN) : 0]), 1'b1
                };
            end
        end
    end

    // check for execute flag on memory
    assign match_any_execute_region = config_pkg::is_inside_execute_regions(CVA6Cfg, {{64-riscv::PLEN{1'b0}}, icache_areq_o.fetch_paddr});
    // assign match_any_execute_region = ariane_pkg::is_inside_execute_regions(ArianeCfg, {{64-riscv::PLEN{1'b0}}, icache_areq_o.fetch_paddr}); this is the package used in the hypervisor extension for now

    // Instruction fetch
    pmp #(
        .CVA6Cfg   (CVA6Cfg), //comment for hypervisor extension
        .PLEN       ( riscv::PLEN            ),
        .PMP_LEN    ( riscv::PLEN - 2        ),
        .NR_ENTRIES ( CVA6Cfg.NrPMPEntries )
        // .NR_ENTRIES ( ArianeCfg.NrPMPEntries ) configuration used in hypervisor extension
    ) i_pmp_if (
        .addr_i        ( icache_areq_o.fetch_paddr ),
        .priv_lvl_i,
        // we will always execute on the instruction fetch port
        .access_type_i ( riscv::ACCESS_EXEC        ),
        // Configuration
        .conf_addr_i   ( pmpaddr_i                 ),
        .conf_i        ( pmpcfg_i                  ),
        .allow_o       ( pmp_instr_allow           )
    );

    //-----------------------
    // Data Interface
    //-----------------------
    logic [HYP_EXT:0][riscv::VLEN-1:0] lsu_vaddr_n,     lsu_vaddr_q;
    logic [riscv::XLEN-1:0] lsu_tinst_n,     lsu_tinst_q;
    logic                   hs_ld_st_inst_n, hs_ld_st_inst_q;
    pte_cva6_t   [HYP_EXT:0] dtlb_pte_n,      dtlb_pte_q;
    exception_t  misaligned_ex_n, misaligned_ex_q;
    logic        lsu_req_n,       lsu_req_q;
    logic        lsu_is_store_n,  lsu_is_store_q;
    logic        dtlb_hit_n,      dtlb_hit_q;
    logic [PT_LEVELS-2:0] dtlb_is_page_n, dtlb_is_page_q;

    // check if we need to do translation or if we are always ready (e.g.: we are not translating anything)
    assign lsu_dtlb_hit_o = (|en_ld_st_translation_i[HYP_EXT:0]) ? dtlb_lu_hit :  1'b1;

    // Wires to PMP checks
    riscv::pmp_access_t pmp_access_type;
    logic        pmp_data_allow;

    assign lsu_paddr_o    [11:0] = lsu_vaddr_q[0][11:0];
    assign lsu_paddr_o [riscv::PLEN-1:PPNWMin+1]   = 
                            (|en_ld_st_translation_i[HYP_EXT:0] && !misaligned_ex_q.valid) ? //
                            (en_ld_st_translation_i[HYP_EXT] ? dtlb_pte_q[HYP_EXT].ppn[riscv::PPNW-1:(riscv::PPNW - (riscv::PLEN - PPNWMin-1))]:
                            dtlb_pte_q[0].ppn[riscv::PPNW-1:(riscv::PPNW - (riscv::PLEN - PPNWMin-1))] ): // 
                            (riscv::PLEN-PPNWMin-1)'(lsu_vaddr_q[0][((riscv::PLEN > riscv::VLEN) ? riscv::VLEN : riscv::PLEN )-1:PPNWMin+1]);

    assign lsu_dtlb_ppn_o [11:0]   = 
                            (|en_ld_st_translation_i[HYP_EXT:0] && !misaligned_ex_q.valid) ? //
                            (en_ld_st_translation_i[HYP_EXT] ? dtlb_content[HYP_EXT].ppn[11:0]:
                            dtlb_content[0].ppn[11:0]) : // 
                            lsu_vaddr_n[0][23:12];

    genvar i;
    generate
        
        for (i=0; i < PT_LEVELS-1; i++) begin  
            assign lsu_paddr_o   [PPNWMin-((VPN_LEN/PT_LEVELS)*(i)):PPNWMin-((VPN_LEN/PT_LEVELS)*(i+1))+1] = //
                                (|en_ld_st_translation_i[HYP_EXT:0]  && !misaligned_ex_q.valid && (|dtlb_is_page_q[i:0]==0)) ? //
                                (en_ld_st_translation_i[HYP_EXT] ? dtlb_pte_q[HYP_EXT].ppn  [(riscv::PPNW - (riscv::PLEN - PPNWMin-1)-((VPN_LEN/PT_LEVELS)*(i))-1):(riscv::PPNW - (riscv::PLEN - PPNWMin-1)-((VPN_LEN/PT_LEVELS)*(i+1)))]:
                                dtlb_pte_q[0].ppn  [(riscv::PPNW - (riscv::PLEN - PPNWMin-1)-((VPN_LEN/PT_LEVELS)*(i))-1):(riscv::PPNW - (riscv::PLEN - PPNWMin-1)-((VPN_LEN/PT_LEVELS)*(i+1)))] ): //
                                lsu_vaddr_q[0][PPNWMin-((VPN_LEN/PT_LEVELS)*(i)):PPNWMin-((VPN_LEN/PT_LEVELS)*(i+1))+1];

            assign lsu_dtlb_ppn_o[PPNWMin-((VPN_LEN/PT_LEVELS)*(i)):PPNWMin-((VPN_LEN/PT_LEVELS)*(i+1))+1] = //
                                (|en_ld_st_translation_i[HYP_EXT:0]  && !misaligned_ex_q.valid && (|dtlb_is_page_q[i:0]==0)) ? //
                                (en_ld_st_translation_i[HYP_EXT] ? dtlb_content[HYP_EXT].ppn[PPNWMin-((VPN_LEN/PT_LEVELS)*(i)):PPNWMin-((VPN_LEN/PT_LEVELS)*(i+1))+1]:
                                dtlb_content[0].ppn[PPNWMin-((VPN_LEN/PT_LEVELS)*(i)):PPNWMin-((VPN_LEN/PT_LEVELS)*(i+1))+1] ): //
                                (|en_ld_st_translation_i[HYP_EXT:0]  && !misaligned_ex_q.valid && (|dtlb_is_page_q[i:0]!=0)?
                                lsu_vaddr_n[0][PPNWMin-((VPN_LEN/PT_LEVELS)*(i)):PPNWMin-((VPN_LEN/PT_LEVELS)*(i+1))+1]://
                                (VPN_LEN/PT_LEVELS)'(lsu_vaddr_n[0][((riscv::PLEN > riscv::VLEN) ? riscv::VLEN -1 : (24 + (VPN_LEN/PT_LEVELS)*(PT_LEVELS-i-1) ) -1): (riscv::PLEN > riscv::VLEN) ? 24 :24 + (VPN_LEN/PT_LEVELS)*(PT_LEVELS-i-2)]));
        end
        if(riscv::IS_XLEN64) begin
            assign lsu_dtlb_ppn_o[riscv::PPNW-1:PPNWMin+1] = (|en_ld_st_translation_i[HYP_EXT:0] && !misaligned_ex_q.valid) ? 
                                (en_ld_st_translation_i[HYP_EXT] ? dtlb_content[HYP_EXT].ppn[riscv::PPNW-1:PPNWMin+1]:
                                dtlb_content[0].ppn[riscv::PPNW-1:PPNWMin+1] ): 
                                lsu_vaddr_n[0][riscv::PLEN-1:PPNWMin+1] ;
        end

    endgenerate 
    
    // The data interface is simpler and only consists of a request/response interface
    always_comb begin : data_interface
        // save request and DTLB response
        lsu_vaddr_n[0]        = lsu_vaddr_i;
        lsu_tinst_n           = lsu_tinst_i;
        
        lsu_req_n             = lsu_req_i;
        hs_ld_st_inst_n       = hs_ld_st_inst_i;
        misaligned_ex_n       = misaligned_ex_i;
        dtlb_pte_n            = dtlb_content;
        dtlb_hit_n            = dtlb_lu_hit;
        lsu_is_store_n        = lsu_is_store_i;
        dtlb_is_page_n        = dtlb_is_page;

        if(HYP_EXT==1) begin
            lsu_vaddr_n[HYP_EXT]  = dtlb_gpaddr;
        end

        lsu_valid_o           = lsu_req_q;
        lsu_exception_o       = misaligned_ex_q;
        csr_hs_ld_st_inst_o   = hs_ld_st_inst_i || hs_ld_st_inst_q;
        pmp_access_type       = lsu_is_store_q ? riscv::ACCESS_WRITE : riscv::ACCESS_READ;

        // mute misaligned exceptions if there is no request otherwise they will throw accidental exceptions
        misaligned_ex_n.valid = misaligned_ex_i.valid & lsu_req_i;

        // Check if the User flag is set, then we may only access it in supervisor mode
        // if SUM is enabled
        daccess_err[0] = (en_ld_st_translation_i[0] || HYP_EXT==0)&&
                        ((ld_st_priv_lvl_i == riscv::PRIV_LVL_S && (en_ld_st_translation_i[HYP_EXT*2] ? !sum_i[HYP_EXT] : !sum_i[0] ) && dtlb_pte_q[0].u) || // SUM is not set and we are trying to access a user page in supervisor mode
                        (ld_st_priv_lvl_i == riscv::PRIV_LVL_U && !dtlb_pte_q[0].u));
        
        if(HYP_EXT==1)
            daccess_err[HYP_EXT] = en_ld_st_translation_i[HYP_EXT] && !dtlb_pte_q[1].u;
        // translation is enabled and no misaligned exception occurred
        if ((|en_ld_st_translation_i[HYP_EXT:0]) && !misaligned_ex_q.valid) begin
            lsu_valid_o = 1'b0;

            // ---------
            // DTLB Hit
            // --------
            if (dtlb_hit_q && lsu_req_q) begin
                lsu_valid_o = 1'b1;
                // exception priority:
                // PAGE_FAULTS have higher priority than ACCESS_FAULTS
                // virtual memory based exceptions are PAGE_FAULTS
                // physical memory based exceptions are ACCESS_FAULTS (PMA/PMP)

                // this is a store
                if (lsu_is_store_q) begin
                    // check if the page is write-able and we are not violating privileges
                    // also check if the dirty flag is set
                    if(HYP_EXT==1 && en_ld_st_translation_i[HYP_EXT] && (!dtlb_pte_q[HYP_EXT].w || daccess_err[HYP_EXT] || !dtlb_pte_q[HYP_EXT].d)) begin
                        lsu_exception_o = {
                            riscv::STORE_GUEST_PAGE_FAULT,
                            {{riscv::XLEN-riscv::VLEN{lsu_vaddr_q[0][riscv::VLEN-1]}},lsu_vaddr_q[0]},
                            lsu_vaddr_q[1][riscv::GPLEN-1:0],
                            {riscv::XLEN{1'b0}},
                            en_ld_st_translation_i[HYP_EXT*2],
                            1'b1
                        };
                    end else if ((en_ld_st_translation_i[0] || HYP_EXT==0) && (!dtlb_pte_q[0].w || daccess_err[0] || !dtlb_pte_q[0].d)) begin
                        if(HYP_EXT==1) begin
                            lsu_exception_o = {
                                riscv::STORE_PAGE_FAULT,
                                {{riscv::XLEN-riscv::VLEN{lsu_vaddr_q[0][riscv::VLEN-1]}},lsu_vaddr_q[0]},
                                {riscv::GPLEN{1'b0}},
                                lsu_tinst_q,
                                en_ld_st_translation_i[HYP_EXT*2],
                                1'b1
                            };
                        end
                        else begin
                            lsu_exception_o = {
                                riscv::STORE_PAGE_FAULT,
                                {{riscv::XLEN - riscv::VLEN{lsu_vaddr_q[0][riscv::VLEN-1]}}, lsu_vaddr_q[0]},
                                1'b1
                            };
                        end
                    // Check if any PMPs are violated
                    end else if (!pmp_data_allow) begin
                        if(HYP_EXT==1) begin
                            lsu_exception_o = {
                                riscv::ST_ACCESS_FAULT,
                                {riscv::XLEN '(lsu_paddr_o)},
                                {riscv::GPLEN{1'b0}},
                                lsu_tinst_q,
                                en_ld_st_translation_i[HYP_EXT*2],
                                1'b1
                            };
                        end
                        else begin
                            lsu_exception_o = {
                                riscv::ST_ACCESS_FAULT, riscv::XLEN'(lsu_paddr_o[riscv::PLEN-1:(riscv::PLEN > riscv::VLEN) ? (riscv::PLEN - riscv::VLEN) : 0]), 1'b1
                            };
                        end
                    end

                // this is a load
                end else begin
                    if (HYP_EXT==1 && daccess_err[HYP_EXT]) begin
                        lsu_exception_o = {
                            riscv::LOAD_GUEST_PAGE_FAULT,
                            {{riscv::XLEN-riscv::VLEN{lsu_vaddr_q[0][riscv::VLEN-1]}},lsu_vaddr_q[0]},
                            lsu_vaddr_q[1][riscv::GPLEN-1:0],
                            {riscv::XLEN{1'b0}},
                            en_ld_st_translation_i[HYP_EXT*2],
                            1'b1
                        };
                    // check for sufficient access privileges - throw a page fault if necessary
                    end else if (daccess_err[0]) begin
                        if(HYP_EXT==1) begin
                            lsu_exception_o = {
                                riscv::LOAD_PAGE_FAULT,
                                {{riscv::XLEN-riscv::VLEN{lsu_vaddr_q[0][riscv::VLEN-1]}},lsu_vaddr_q[0]},
                                {riscv::GPLEN{1'b0}},
                                lsu_tinst_q,
                                en_ld_st_translation_i[HYP_EXT*2],
                                1'b1
                            };
                        end
                        else begin
                            lsu_exception_o = {
                                riscv::LOAD_PAGE_FAULT,
                                {{riscv::XLEN - riscv::VLEN{lsu_vaddr_q[0][riscv::VLEN-1]}}, lsu_vaddr_q[0]},
                                1'b1
                            };
                        end
                    // Check if any PMPs are violated
                    end else if (!pmp_data_allow) begin
                        if(HYP_EXT==1) begin
                            lsu_exception_o = {
                                riscv::LD_ACCESS_FAULT,
                                {{riscv::XLEN-riscv::VLEN{lsu_vaddr_q[0][riscv::VLEN-1]}},lsu_vaddr_q[0]},
                                {riscv::GPLEN{1'b0}},
                                lsu_tinst_q,
                                en_ld_st_translation_i[HYP_EXT*2],
                                1'b1
                            };
                        end
                        else begin
                            lsu_exception_o = {
                                riscv::LD_ACCESS_FAULT, lsu_paddr_o[riscv::PLEN-1:(riscv::PLEN > riscv::VLEN) ? (riscv::PLEN - riscv::VLEN) : 0], 1'b1
                            };
                        end
                    end
                end
            end else

            // ---------
            // DTLB Miss
            // ---------
            // watch out for exceptions
            if (ptw_active && !walking_instr) begin
                // page table walker threw an exception
                if (ptw_error[0]) begin
                    // an error makes the translation valid
                    lsu_valid_o = 1'b1;
                    // the page table walker can only throw page faults
                    if (lsu_is_store_q) begin
                        if (HYP_EXT==1 && ptw_error[HYP_EXT]) begin
                            lsu_exception_o = {
                                riscv::STORE_GUEST_PAGE_FAULT,
                                {{riscv::XLEN-riscv::VLEN{lsu_vaddr_q[0][riscv::VLEN-1]}},update_vaddr},
                                ptw_bad_paddr[HYP_EXT][riscv::GPLEN-1:0],
                                (ptw_error[HYP_EXT*2] ? (riscv::IS_XLEN64 ? riscv::READ_64_PSEUDOINSTRUCTION : riscv::READ_32_PSEUDOINSTRUCTION) : {riscv::XLEN{1'b0}}),
                                en_ld_st_translation_i[HYP_EXT*2],
                                1'b1
                            };
                        end else begin
                            if(HYP_EXT==1) begin
                                lsu_exception_o = {
                                    riscv::STORE_PAGE_FAULT,
                                    {{riscv::XLEN-riscv::VLEN{lsu_vaddr_q[0][riscv::VLEN-1]}},update_vaddr},
                                    {riscv::GPLEN{1'b0}},
                                    lsu_tinst_q,
                                    en_ld_st_translation_i[HYP_EXT*2],
                                    1'b1
                                };
                            end
                            else begin
                                lsu_exception_o = {
                                    riscv::STORE_PAGE_FAULT,
                                    {{riscv::XLEN - riscv::VLEN{lsu_vaddr_q[0][riscv::VLEN-1]}}, update_vaddr},
                                    1'b1
                                };
                            end
                        end
                    end else begin
                        if (HYP_EXT==1 && ptw_error[HYP_EXT]) begin
                            lsu_exception_o = {
                                riscv::LOAD_GUEST_PAGE_FAULT,
                                {{riscv::XLEN-riscv::VLEN{lsu_vaddr_q[0][riscv::VLEN-1]}},update_vaddr},
                                ptw_bad_paddr[HYP_EXT][riscv::GPLEN-1:0],
                                (ptw_error[HYP_EXT*2] ? (riscv::IS_XLEN64 ? riscv::READ_64_PSEUDOINSTRUCTION : riscv::READ_32_PSEUDOINSTRUCTION) : {riscv::XLEN{1'b0}}),
                                en_ld_st_translation_i[HYP_EXT*2],
                                1'b1
                            };
                        end else begin
                            if(HYP_EXT==1) begin
                                lsu_exception_o = {
                                    riscv::LOAD_PAGE_FAULT,
                                    {{riscv::XLEN-riscv::VLEN{lsu_vaddr_q[0][riscv::VLEN-1]}},update_vaddr},
                                    {riscv::GPLEN{1'b0}},
                                    lsu_tinst_q,
                                    en_ld_st_translation_i[HYP_EXT*2],
                                    1'b1
                                };
                            end
                            else begin
                                lsu_exception_o = {
                                    riscv::LOAD_PAGE_FAULT,
                                    {{riscv::XLEN - riscv::VLEN{lsu_vaddr_q[0][riscv::VLEN-1]}}, update_vaddr},
                                    1'b1
                                };
                            end
                        end
                    end
                end

                if (ptw_access_exception) begin
                    // an error makes the translation valid
                    lsu_valid_o = 1'b1;
                    // the page table walker can only throw page faults
                    if(HYP_EXT==1) begin
                        lsu_exception_o = {
                            riscv::LD_ACCESS_FAULT,
                            {{riscv::XLEN-riscv::VLEN{lsu_vaddr_q[0][riscv::VLEN-1]}},update_vaddr},
                            {riscv::GPLEN{1'b0}},
                            lsu_tinst_q,
                            en_ld_st_translation_i[HYP_EXT*2],
                            1'b1
                        };
                    end
                    else begin
                        lsu_exception_o = {riscv::LD_ACCESS_FAULT, ptw_bad_paddr[0][riscv::PLEN-1:(riscv::PLEN > riscv::VLEN) ? (riscv::PLEN - riscv::VLEN) : 0], 1'b1};
                    end
                end
            end
        end
        // If translation is not enabled, check the paddr immediately against PMPs
        else if (lsu_req_q && !misaligned_ex_q.valid && !pmp_data_allow) begin
            if (lsu_is_store_q) begin
                if(HYP_EXT==1) begin
                    lsu_exception_o = {
                        riscv::ST_ACCESS_FAULT,
                        {{riscv::XLEN-riscv::VLEN{lsu_vaddr_q[0][riscv::VLEN-1]}},update_vaddr},
                        {riscv::GPLEN{1'b0}},
                        lsu_tinst_q,
                        en_ld_st_translation_i[HYP_EXT*2],
                        1'b1
                    };
                end
                else 
                    lsu_exception_o = {riscv::ST_ACCESS_FAULT, lsu_paddr_o[riscv::PLEN-1:(riscv::PLEN > riscv::VLEN) ? (riscv::PLEN - riscv::VLEN) : 0], 1'b1};
                end else begin
                    if(HYP_EXT==1) begin
                    lsu_exception_o = {
                        riscv::LD_ACCESS_FAULT,
                        {{riscv::XLEN-riscv::VLEN{lsu_vaddr_q[0][riscv::VLEN-1]}},update_vaddr},
                        {riscv::GPLEN{1'b0}},
                        lsu_tinst_q,
                        en_ld_st_translation_i[HYP_EXT*2],
                        1'b1
                    };
                end
                else begin
                    lsu_exception_o = {riscv::LD_ACCESS_FAULT, lsu_paddr_o[riscv::PLEN-1:(riscv::PLEN > riscv::VLEN) ? (riscv::PLEN - riscv::VLEN) : 0], 1'b1};
                end
            end
        end
    end

    // Load/store PMP check
    pmp #(
        .CVA6Cfg   (CVA6Cfg), // COMMENT IN HYPERVISOR EXTENSION
        .PLEN       ( riscv::PLEN            ),
        .PMP_LEN    ( riscv::PLEN - 2        ),
        .NR_ENTRIES ( CVA6Cfg.NrPMPEntries )
        // .NR_ENTRIES ( ArianeCfg.NrPMPEntries ) CONFIGURATION USED IN HYPERVISOR EXTENSION
    ) i_pmp_data (
        .addr_i        ( lsu_paddr_o         ),
        .priv_lvl_i    ( ld_st_priv_lvl_i    ),
        .access_type_i ( pmp_access_type     ),
        // Configuration
        .conf_addr_i   ( pmpaddr_i           ),
        .conf_i        ( pmpcfg_i            ),
        .allow_o       ( pmp_data_allow      )
    );

    // ----------
    // Registers
    // ----------
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (~rst_ni) begin
            lsu_vaddr_q      <= '0;
            lsu_tinst_q      <= '0;
            hs_ld_st_inst_q  <= '0;
            lsu_req_q        <= '0;
            misaligned_ex_q  <= '0;
            dtlb_pte_q       <= '0;
            dtlb_hit_q       <= '0;
            lsu_is_store_q   <= '0;
            dtlb_is_page_q   <= '0;
        end else begin
            lsu_vaddr_q      <=  lsu_vaddr_n;
            lsu_tinst_q      <=  lsu_tinst_n;
            hs_ld_st_inst_q  <= hs_ld_st_inst_n;
            lsu_req_q        <=  lsu_req_n;
            misaligned_ex_q  <=  misaligned_ex_n;
            dtlb_pte_q       <=  dtlb_pte_n;
            dtlb_hit_q       <=  dtlb_hit_n;
            lsu_is_store_q   <=  lsu_is_store_n;
            dtlb_is_page_q  <= dtlb_is_page_n;
        end
    end
endmodule
