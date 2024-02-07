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
// Date: 02/02/2024
// Description: Hardware-PTW (Page-Table-Walker) for CVA6 supporting sv32, sv39 and sv39x4.
//              This module is an merge of the PTW Sv39 developed by Florian Zaruba,
//              the PTW Sv32 developed by Sebastien Jacq and the PTW Sv39x4 by Bruno Sá.  

/* verilator lint_off WIDTH */

module cva6_ptw import ariane_pkg::*; #(
    parameter type pte_cva6_t = logic,
    parameter type tlb_update_cva6_t = logic,
    parameter int unsigned HYP_EXT = 0,
    parameter int unsigned ASID_WIDTH [HYP_EXT:0] = {1},
    parameter int unsigned VPN_LEN = 1,
    parameter config_pkg::cva6_cfg_t CVA6Cfg           = config_pkg::cva6_cfg_empty,
    parameter int unsigned PT_LEVELS = 1
) (
    input  logic                    clk_i,                  // Clock
    input  logic                    rst_ni,                 // Asynchronous reset active low
    input  logic                    flush_i,                // flush everything, we need to do this because
                                                            // actually everything we do is speculative at this stage
                                                            // e.g.: there could be a CSR instruction that changes everything
    output logic                    ptw_active_o,
    output logic                    walking_instr_o,        // set when walking for TLB
    output logic   [HYP_EXT*2:0]    ptw_error_o,            // set when an error occurred
    output logic                    ptw_access_exception_o, // set when an PMP access exception occured

    input  logic                    hlvx_inst_i,            // is a HLVX load/store instruction

    input  logic                    lsu_is_store_i,         // this translation was triggered by a store
    // PTW memory interface
    input  dcache_req_o_t           req_port_i,
    output dcache_req_i_t           req_port_o,


    // to TLBs, update logic
    output tlb_update_cva6_t      shared_tlb_update_o,

    output logic [riscv::VLEN-1:0]  update_vaddr_o,

    input logic [ASID_WIDTH[0]-1:0] asid_i[HYP_EXT*2:0],//[vmid,vs_asid,asid]

    // from TLBs
    // did we miss?
    input  logic [HYP_EXT*2:0]      shared_tlb_access_i,
    input  logic                    shared_tlb_hit_i,
    input  logic [riscv::VLEN-1:0]  shared_tlb_vaddr_i,

    input logic itlb_req_i,

    // from CSR file
    input logic [riscv::PPNW-1:0]   satp_ppn_i[HYP_EXT*2:0],//[hgatp,vsatp,satp]
    input logic    [HYP_EXT:0]      mxr_i,

    // Performance counters
    output logic                    shared_tlb_miss_o,

    // PMP

    input  riscv::pmpcfg_t [15:0]   pmpcfg_i,
    input  logic [15:0][riscv::PLEN-3:0] pmpaddr_i,
    output logic [HYP_EXT:0][riscv::PLEN-1:0] bad_paddr_o

);

    // input registers
    logic data_rvalid_q;
    riscv::xlen_t data_rdata_q;

    pte_cva6_t [HYP_EXT*2:0] pte; //[gpte_d,gpte_q,pte]
    // register to perform context switch between stages
    // pte_cva6_t gpte_q, gpte_d;
    assign pte[0] = pte_cva6_t'(data_rdata_q[riscv::PPNW+9:0]);

    enum logic[2:0] {
      IDLE,
      WAIT_GRANT,
      PTE_LOOKUP,
      WAIT_RVALID,
      PROPAGATE_ERROR,
      PROPAGATE_ACCESS_ERROR,
      LATENCY
    } state_q, state_d;

    logic [PT_LEVELS-1:0] misaligned_page;
    logic [HYP_EXT:0][PT_LEVELS-2:0] ptw_lvl_n,ptw_lvl_q;  

    // define 3 PTW stages to be used in sv39x4. sv32 and sv39 are always in S_STAGE
    // S_STAGE -> S/VS-stage normal translation controlled by the satp/vsatp CSRs
    // G_INTERMED_STAGE -> Converts the S/VS-stage non-leaf GPA pointers to HPA (controlled by hgatp)
    // G_FINAL_STAGE -> Converts the S/VS-stage final GPA to HPA (controlled by hgatp)
    enum logic [1:0] {
        S_STAGE,
        G_INTERMED_STAGE,
        G_FINAL_STAGE
    } ptw_stage_q, ptw_stage_d;

    // is this an instruction page table walk?
    logic is_instr_ptw_q,   is_instr_ptw_n;
    logic global_mapping_q, global_mapping_n;
    // latched tag signal
    logic tag_valid_n,      tag_valid_q;
    // register the ASIDs
    logic [HYP_EXT:0][ASID_WIDTH[0]-1:0]  tlb_update_asid_q, tlb_update_asid_n;
    // register the VPN we need to walk, SV39 defines a 39 bit virtual address
    logic [riscv::VLEN-1:0] vaddr_q,   vaddr_n;
    logic [HYP_EXT*2:0][PT_LEVELS-2:0][(VPN_LEN/PT_LEVELS)-1:0] vaddr_lvl;   
    // register the VPN we need to walk, SV39x4 defines a 41 bit virtual address for the G-Stage
    logic [riscv::GPLEN-1:0] gpaddr_q, gpaddr_n,gpaddr_base;
    logic [PT_LEVELS-2:0][riscv::GPLEN-1:0] gpaddr;
    // 4 byte aligned physical pointer
    logic [riscv::PLEN-1:0] ptw_pptr_q, ptw_pptr_n;
    logic [riscv::PLEN-1:0] gptw_pptr_q, gptw_pptr_n;

    // Assignments
    assign update_vaddr_o  = vaddr_q;

    assign ptw_active_o    = (state_q != IDLE);
    assign walking_instr_o = is_instr_ptw_q;
    // directly output the correct physical address
    assign req_port_o.address_index = ptw_pptr_q[DCACHE_INDEX_WIDTH-1:0];
    assign req_port_o.address_tag   = ptw_pptr_q[DCACHE_INDEX_WIDTH+DCACHE_TAG_WIDTH-1:DCACHE_INDEX_WIDTH];
    // we are never going to kill this request
    assign req_port_o.kill_req      = '0;
    // we are never going to write with the HPTW
    assign req_port_o.data_wdata    = '0;
    // we only issue one single request at a time
    assign req_port_o.data_id = '0;

    // -----------
    // TLB Update
    // -----------

    assign gpaddr_base = {pte[0].ppn[riscv::GPPNW-1:0], vaddr_q[11:0]};

    genvar z,w;
    generate
        for (z=0; z < PT_LEVELS-1; z++) begin  

            // check if the ppn is correctly aligned:
            // 6. If i > 0 and pa.ppn[i − 1 : 0] != 0, this is a misaligned superpage; stop and raise a page-fault
            // exception.
            assign misaligned_page[z] = (ptw_lvl_q[0] == (z)) && (pte[0].ppn[(VPN_LEN/PT_LEVELS)*(PT_LEVELS-1-z)-1:0] != '0);

            //record the vaddr corresponding to each level
            for (w=0; w < HYP_EXT*2+1; w++) begin 
                assign vaddr_lvl[w][z] = w==0 ?  vaddr_q[12+((VPN_LEN/PT_LEVELS)*(PT_LEVELS-z-1))-1:12+((VPN_LEN/PT_LEVELS)*(PT_LEVELS-z-2))] :
                                  w==1 ?  gptw_pptr_q[12+((VPN_LEN/PT_LEVELS)*(PT_LEVELS-z-1))-1:12+((VPN_LEN/PT_LEVELS)*(PT_LEVELS-z-2))]:
                                  gpaddr_q[12+((VPN_LEN/PT_LEVELS)*(PT_LEVELS-z-1))-1:12+((VPN_LEN/PT_LEVELS)*(PT_LEVELS-z-2))];
            end

            assign gpaddr[z][VPN_LEN-(VPN_LEN/PT_LEVELS):0]= (ptw_lvl_q[0] == z) ? vaddr_q[VPN_LEN-(VPN_LEN/PT_LEVELS):0] : gpaddr_base[VPN_LEN-(VPN_LEN/PT_LEVELS):0];
            assign gpaddr[z][VPN_LEN:VPN_LEN-(VPN_LEN/PT_LEVELS)+1]= (ptw_lvl_q[0] == 0) ? vaddr_q[VPN_LEN:VPN_LEN-(VPN_LEN/PT_LEVELS)+1] : gpaddr_base[VPN_LEN:VPN_LEN-(VPN_LEN/PT_LEVELS)+1];
            assign gpaddr[z][riscv::GPLEN-1:VPN_LEN+1]= gpaddr_base[riscv::GPLEN-1:VPN_LEN+1];


        end
    endgenerate

    always_comb begin : tlb_update
        
        shared_tlb_update_o.vpn = VPN_LEN'(vaddr_q[riscv::SV+HYP_EXT*2-1:12]);

        // update the correct page table level
        for (int unsigned y=0; y < HYP_EXT+1; y++) begin
            for (int unsigned x=0; x < PT_LEVELS-1; x++) begin
                if(&shared_tlb_access_i[HYP_EXT:0] && HYP_EXT==1) 
                    shared_tlb_update_o.is_page[x][y] = (ptw_lvl_q[y==HYP_EXT? 0 : 1] == x);
                else if(shared_tlb_access_i[0] || HYP_EXT==0) 
                    shared_tlb_update_o.is_page[x][y] = y==0 ? (ptw_lvl_q[0]== x) : 1'b0;
                else 
                    shared_tlb_update_o.is_page[x][y] = y!=0 ? (ptw_lvl_q[0]== x) : 1'b0;
            end

            // set the global mapping bit
            if(shared_tlb_access_i[HYP_EXT] && HYP_EXT==1) begin
                shared_tlb_update_o.content[y] = y==0 ? pte[HYP_EXT] | (global_mapping_q << 5) : pte[0];
            end else begin
                shared_tlb_update_o.content[y] = y==0 ? (pte[0] | (global_mapping_q << 5)) : '0;
            end
        end
        // output the correct ASIDs
        shared_tlb_update_o.asid = tlb_update_asid_q;
        
        bad_paddr_o[0] = ptw_access_exception_o ? ptw_pptr_q : 'b0;
        if(HYP_EXT==1)
            bad_paddr_o[HYP_EXT][riscv::GPLEN:0] = ptw_error_o[HYP_EXT] ? ((ptw_stage_q == G_INTERMED_STAGE) ? gptw_pptr_q[riscv::GPLEN:0] : gpaddr_q) : 'b0;
    end

    assign req_port_o.tag_valid      = tag_valid_q;

    logic allow_access;



    pmp #(
        .PLEN       ( riscv::PLEN            ),
        .PMP_LEN    ( riscv::PLEN - 2        ),
        .NR_ENTRIES ( CVA6Cfg.NrPMPEntries )
    ) i_pmp_ptw (
        .addr_i        ( ptw_pptr_q         ),
        // PTW access are always checked as if in S-Mode...
        .priv_lvl_i    ( riscv::PRIV_LVL_S  ),
        // ...and they are always loads
        .access_type_i ( riscv::ACCESS_READ ),
        // Configuration
        .conf_addr_i   ( pmpaddr_i          ),
        .conf_i        ( pmpcfg_i           ),
        .allow_o       ( allow_access       )
    );


    assign req_port_o.data_be = riscv::XLEN ==32?
                             be_gen_32(req_port_o.address_index[1:0], req_port_o.data_size):
                             be_gen(req_port_o.address_index[2:0], req_port_o.data_size);

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
        automatic logic [riscv::PLEN-1:0] pptr;
        // automatic logic [riscv::GPLEN-1:0] gpaddr;
        // default assignments
        // PTW memory interface
        tag_valid_n            = 1'b0;
        req_port_o.data_req    = 1'b0;
        req_port_o.data_size   = 2'(PT_LEVELS);
        req_port_o.data_we     = 1'b0;
        ptw_error_o            = '0;
        ptw_access_exception_o = 1'b0;
        shared_tlb_update_o.valid    = 1'b0;
        is_instr_ptw_n         = is_instr_ptw_q;
        ptw_lvl_n              = ptw_lvl_q;
        ptw_pptr_n             = ptw_pptr_q;
        gptw_pptr_n            = gptw_pptr_q;
        state_d                = state_q;
        ptw_stage_d            = ptw_stage_q;
        global_mapping_n       = global_mapping_q;
        // input registers
        tlb_update_asid_n     = tlb_update_asid_q;
        vaddr_n               = vaddr_q;
        gpaddr_n              = gpaddr_q;
        pptr                  = ptw_pptr_q;
        // gpaddr                = gpaddr_q;

        shared_tlb_miss_o           = 1'b0;

        if(HYP_EXT==1)
            pte[HYP_EXT*2] = pte[HYP_EXT];

        case (state_q)

            IDLE: begin
                // by default we start with the top-most page table
                ptw_lvl_n        = '0;
                global_mapping_n = 1'b0;
                is_instr_ptw_n   = 1'b0;
                gpaddr_n         = '0;

                if(HYP_EXT==1)
                    pte[HYP_EXT*2] = '0;
                // if we got an ITLB miss
                if (|shared_tlb_access_i & ~shared_tlb_hit_i) begin
                    if (&shared_tlb_access_i[HYP_EXT:0] && HYP_EXT==1) begin
                        ptw_stage_d = G_INTERMED_STAGE;
                        pptr = {satp_ppn_i[HYP_EXT], shared_tlb_vaddr_i[riscv::SV-1:riscv::SV-(VPN_LEN/PT_LEVELS)], (PT_LEVELS)'(0)};
                        gptw_pptr_n = pptr;
                        ptw_pptr_n = {satp_ppn_i[HYP_EXT*2][riscv::PPNW-1:2], pptr[riscv::SV+HYP_EXT*2-1:riscv::SV-(VPN_LEN/PT_LEVELS)], (PT_LEVELS)'(0)};
                    end else if (!shared_tlb_access_i[0] && HYP_EXT==1) begin
                        ptw_stage_d = G_FINAL_STAGE;
                        gpaddr_n = shared_tlb_vaddr_i[riscv::SV+HYP_EXT*2-1:0];
                        ptw_pptr_n = {satp_ppn_i[HYP_EXT*2][riscv::PPNW-1:2], shared_tlb_vaddr_i[riscv::SV+HYP_EXT*2-1:riscv::SV-(VPN_LEN/PT_LEVELS)], (PT_LEVELS)'(0)};
                    end else begin
                        ptw_stage_d = S_STAGE;
                        if(shared_tlb_access_i[HYP_EXT*2] && HYP_EXT==1)
                            ptw_pptr_n  = {satp_ppn_i[HYP_EXT], shared_tlb_vaddr_i[riscv::SV-1:riscv::SV-(VPN_LEN/PT_LEVELS)], (PT_LEVELS)'(0)};
                        else
                            ptw_pptr_n  = {satp_ppn_i[0], shared_tlb_vaddr_i[riscv::SV-1:riscv::SV-(VPN_LEN/PT_LEVELS)], (PT_LEVELS)'(0)};
                    end

                    is_instr_ptw_n      = itlb_req_i;
                    vaddr_n             = shared_tlb_vaddr_i;
                    state_d             = WAIT_GRANT;
                    shared_tlb_miss_o         = 1'b1;

                    for (int unsigned b=0; b < HYP_EXT+1; b++) begin  
                        tlb_update_asid_n[b] = b==0 ? (shared_tlb_access_i[2*HYP_EXT] ? asid_i[HYP_EXT] : asid_i[0]) : asid_i[HYP_EXT*2];
                    end
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
                    if (pte[0].g && ptw_stage_q == S_STAGE)
                        global_mapping_n = 1'b1;

                    // -------------
                    // Invalid PTE
                    // -------------
                    // If pte.v = 0, or if pte.r = 0 and pte.w = 1, stop and raise a page-fault exception.
                    if (!pte[0].v || (!pte[0].r && pte[0].w))// || (|pte.reserved))
                        state_d = PROPAGATE_ERROR;
                    // -----------
                    // Valid PTE
                    // -----------
                    else begin
                        state_d = LATENCY;
                        // it is a valid PTE
                        // if pte.r = 1 or pte.x = 1 it is a valid PTE
                        if (pte[0].r || pte[0].x) begin
                            case (ptw_stage_q)
                                S_STAGE: begin
                                    if (HYP_EXT==1 && shared_tlb_access_i[HYP_EXT]) begin
                                        state_d = WAIT_GRANT;
                                        ptw_stage_d = G_FINAL_STAGE;
                                        if(HYP_EXT==1)
                                            pte[HYP_EXT*2] = pte[0];
                                        ptw_lvl_n[HYP_EXT] = ptw_lvl_q[0];
                                        gpaddr_n = gpaddr[ptw_lvl_q[0]];
                                        ptw_pptr_n = {satp_ppn_i[HYP_EXT*2][riscv::PPNW-1:2], gpaddr[ptw_lvl_q[0]][riscv::SV+HYP_EXT*2-1:riscv::SV-(VPN_LEN/PT_LEVELS)],(PT_LEVELS)'(0)};
                                        ptw_lvl_n[0] = 0;
                                    end
                                end
                                G_INTERMED_STAGE: begin
                                    state_d = WAIT_GRANT;
                                    ptw_stage_d = S_STAGE;
                                    ptw_lvl_n[0] = ptw_lvl_q[HYP_EXT];
                                    pptr = {pte[0].ppn[riscv::GPPNW-1:0], gptw_pptr_q[11:0]};
                                    if (ptw_lvl_q[0] == 1)
                                        pptr[20:0] = gptw_pptr_q[20:0];
                                    if(ptw_lvl_q[0] == 0)
                                        pptr[29:0] = gptw_pptr_q[29:0];
                                    ptw_pptr_n = pptr;
                                end
                                default:;
                            endcase
                            // Valid translation found (either 1G, 2M or 4K entry)
                            if (is_instr_ptw_q) begin
                                // ------------
                                // Update ITLB
                                // ------------
                                // If page is not executable, we can directly raise an error. This
                                // doesn't put a useless entry into the TLB. The same idea applies
                                // to the access flag since we let the access flag be managed by SW.
                                if (!pte[0].x || !pte[0].a) begin
                                    state_d = PROPAGATE_ERROR;
                                    ptw_stage_d = ptw_stage_q;
                                end else if((ptw_stage_q == G_FINAL_STAGE) || !shared_tlb_access_i[HYP_EXT] || HYP_EXT==0)
                                    shared_tlb_update_o.valid = 1'b1;

                            end else begin
                                // ------------
                                // Update DTLB
                                // ------------
                                // Check if the access flag has been set, otherwise throw a page-fault
                                // and let the software handle those bits.
                                // If page is not readable (there are no write-only pages)
                                // we can directly raise an error. This doesn't put a useless
                                // entry into the TLB.
                                if (pte[0].a && ((pte[0].r && !hlvx_inst_i) || (pte[0].x && (mxr_i[0] || hlvx_inst_i || (ptw_stage_q == S_STAGE && mxr_i[HYP_EXT] && shared_tlb_access_i[HYP_EXT*2] && HYP_EXT==1))))) begin
                                    if((ptw_stage_q == G_FINAL_STAGE) || !shared_tlb_access_i[HYP_EXT] || HYP_EXT==0)
                                        shared_tlb_update_o.valid = 1'b1;
                                end else begin
                                    state_d   = PROPAGATE_ERROR;
                                    ptw_stage_d = ptw_stage_q;
                                end
                                // Request is a store: perform some additional checks
                                // If the request was a store and the page is not write-able, raise an error
                                // the same applies if the dirty flag is not set
                                if (lsu_is_store_i && (!pte[0].w || !pte[0].d)) begin
                                    shared_tlb_update_o.valid = 1'b0;
                                    state_d   = PROPAGATE_ERROR;
                                    ptw_stage_d = ptw_stage_q;
                                end
                            end

                            //if there is a misaligned page, propagate error
                            if (|misaligned_page) begin
                                state_d             = PROPAGATE_ERROR;
                                ptw_stage_d         = ptw_stage_q;
                                shared_tlb_update_o.valid = 1'b0;
                            end 

                            // check if 63:41 are all zeros
                            if (HYP_EXT==1 && shared_tlb_access_i[HYP_EXT*2] && ptw_stage_q == S_STAGE && !((|pte[0].ppn[riscv::PPNW-HYP_EXT:riscv::GPPNW]) == 1'b0)) begin
                                state_d = PROPAGATE_ERROR;
                                ptw_stage_d = G_FINAL_STAGE;
                            end
                        // this is a pointer to the next TLB level
                        end else begin
                            // pointer to next level of page table

                            if (ptw_lvl_q[0] == PT_LEVELS-1) begin
                                // Should already be the last level page table => Error
                                    ptw_lvl_n[0]   = PT_LEVELS-1;
                                    state_d = PROPAGATE_ERROR;
                                    ptw_stage_d = ptw_stage_q;
                                    

                            end else begin
                                ptw_lvl_n[0] = ptw_lvl_q[0]+1;
                                state_d = WAIT_GRANT;

                                case (ptw_stage_q)
                                    S_STAGE: begin
                                        if (HYP_EXT==1 && shared_tlb_access_i[HYP_EXT]) begin
                                            ptw_stage_d = G_INTERMED_STAGE;
                                            if(HYP_EXT==1)
                                                pte[HYP_EXT*2] = pte[0];
                                            ptw_lvl_n[HYP_EXT] = ptw_lvl_q[0]+1;
                                            pptr = {pte[0].ppn, vaddr_lvl[0][ptw_lvl_q[0]], (PT_LEVELS)'(0)};
                                            gptw_pptr_n = pptr;
                                            ptw_pptr_n = {satp_ppn_i[HYP_EXT*2][riscv::PPNW-1:2], pptr[riscv::SV+HYP_EXT*2-1:riscv::SV-(VPN_LEN/PT_LEVELS)], (PT_LEVELS)'(0)};
                                            ptw_lvl_n[0] = 0;
                                        end else begin
                                            ptw_pptr_n = {pte[0].ppn, vaddr_lvl[0][ptw_lvl_q[0]], (PT_LEVELS)'(0)};
                                        end
                                    end
                                    G_INTERMED_STAGE: begin
                                            ptw_pptr_n = {pte[0].ppn, vaddr_lvl[HYP_EXT][ptw_lvl_q[0]], (PT_LEVELS)'(0)};
                                    end
                                    G_FINAL_STAGE: begin
                                            ptw_pptr_n = {pte[0].ppn, vaddr_lvl[HYP_EXT*2][ptw_lvl_q[0]], (PT_LEVELS)'(0)};
                                    end
                                endcase

                                if(HYP_EXT==1 && (pte[0].a || pte[0].d || pte[0].u)) begin
                                    state_d = PROPAGATE_ERROR;
                                    ptw_stage_d = ptw_stage_q;
                                end
                                
                            end

                            // check if 63:41 are all zeros
                            if (HYP_EXT==1 && (shared_tlb_access_i[HYP_EXT*2]  && ptw_stage_q == S_STAGE && !((|pte[0].ppn[riscv::PPNW-1:riscv::GPPNW]) == 1'b0))) begin
                                state_d = PROPAGATE_ERROR;
                                ptw_stage_d = ptw_stage_q;
                            end
                        end
                    end

                    // Check if this access was actually allowed from a PMP perspective
                    if (!allow_access) begin
                        shared_tlb_update_o.valid = 1'b0;
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
                state_d     = LATENCY;
                ptw_error_o[0] = 1'b1;
                if(HYP_EXT==1) begin
                    ptw_error_o[HYP_EXT]   = (ptw_stage_q != S_STAGE) ? 1'b1 : 1'b0;
                    ptw_error_o[HYP_EXT*2] = (ptw_stage_q == G_INTERMED_STAGE) ? 1'b1 : 1'b0;
                end
            end
            PROPAGATE_ACCESS_ERROR: begin
                state_d     = LATENCY;
                ptw_access_exception_o = 1'b1;
            end
            // wait for the rvalid before going back to IDLE
            WAIT_RVALID: begin
                if (data_rvalid_q)
                    state_d = IDLE;
            end
            LATENCY: begin
                state_d = IDLE;
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
            if (((state_q inside {PTE_LOOKUP, WAIT_RVALID}) && !data_rvalid_q) || ((state_q == WAIT_GRANT) && req_port_i.data_gnt))
                state_d = WAIT_RVALID;
            else
                state_d = LATENCY;
        end
    end

    // sequential process
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (~rst_ni) begin
            state_q            <= IDLE;
            ptw_stage_q        <= S_STAGE;
            is_instr_ptw_q     <= 1'b0;
            ptw_lvl_q          <= '0;
            tag_valid_q        <= 1'b0;
            tlb_update_asid_q  <= '0;
            vaddr_q            <= '0;
            gpaddr_q           <= '0;
            ptw_pptr_q         <= '0;
            gptw_pptr_q        <= '0;
            global_mapping_q   <= 1'b0;
            data_rdata_q       <= '0;
            data_rvalid_q      <= 1'b0;
            if(HYP_EXT==1)
                pte[HYP_EXT] = '0;
        end else begin
            state_q            <= state_d;
            ptw_stage_q        <= ptw_stage_d;
            ptw_pptr_q         <= ptw_pptr_n;
            gptw_pptr_q        <= gptw_pptr_n;
            is_instr_ptw_q     <= is_instr_ptw_n;
            ptw_lvl_q          <= ptw_lvl_n;
            tag_valid_q        <= tag_valid_n;
            tlb_update_asid_q  <= tlb_update_asid_n;
            vaddr_q            <= vaddr_n;
            gpaddr_q           <= gpaddr_n;
            global_mapping_q   <= global_mapping_n;
            data_rdata_q       <= req_port_i.data_rdata;
            data_rvalid_q      <= req_port_i.data_rvalid;

            if(HYP_EXT==1)
                pte[HYP_EXT] = pte[HYP_EXT*2];
        end
    end

endmodule
/* verilator lint_on WIDTH */
