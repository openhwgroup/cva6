
// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Author: Florian Zaruba, ETH Zurich
// Date: 19.04.2017
// Description: Instantiation of all functional units residing in the execute stage

import ariane_pkg::*;

module ex_stage (
    input  logic                                   clk_i,    // Clock
    input  logic                                   rst_ni,   // Asynchronous reset active low
    input  logic                                   flush_i,

    input  fu_data_t                               fu_data_i,
    input  logic [63:0]                            pc_i,                  // PC of current instruction
    input  logic                                   is_compressed_instr_i, // we need to know if this was a compressed instruction
                                                                          // in order to calculate the next PC on a mis-predict
    // Fixed latency unit(s)
    output logic [63:0]                            flu_result_o,
    output logic [TRANS_ID_BITS-1:0]               flu_trans_id_o,        // ID of scoreboard entry at which to write back
    output exception_t                             flu_exception_o,
    output logic                                   flu_ready_o,           // FLU is ready
    output logic                                   flu_valid_o,           // FLU result is valid
    // Branches and Jumps
    // ALU 1
    input  logic                                   alu_valid_i,           // Output is valid
    // Branch Unit
    input  logic                                   branch_valid_i,        // we are using the branch unit
    input  branchpredict_sbe_t                     branch_predict_i,
    output branchpredict_t                         resolved_branch_o,     // the branch engine uses the write back from the ALU
    output logic                                   resolve_branch_o,      // to ID signaling that we resolved the branch
    // CSR
    input  logic                                   csr_valid_i,
    output logic [11:0]                            csr_addr_o,
    input  logic                                   csr_commit_i,
    // MULT
    input  logic                                   mult_valid_i,      // Output is valid
    // LSU
    output logic                                   lsu_ready_o,        // FU is ready
    input  logic                                   lsu_valid_i,        // Input is valid

    output logic                                   load_valid_o,
    output logic [63:0]                            load_result_o,
    output logic [TRANS_ID_BITS-1:0]               load_trans_id_o,
    output exception_t                             load_exception_o,
    output logic                                   store_valid_o,
    output logic [63:0]                            store_result_o,
    output logic [TRANS_ID_BITS-1:0]               store_trans_id_o,
    output exception_t                             store_exception_o,

    input  logic                                   lsu_commit_i,
    output logic                                   lsu_commit_ready_o, // commit queue is ready to accept another commit request
    output logic                                   no_st_pending_o,
    input  logic                                   amo_valid_commit_i,
    // FPU
    output logic                                   fpu_ready_o,      // FU is ready
    input  logic                                   fpu_valid_i,      // Output is valid
    input  logic [1:0]                             fpu_fmt_i,        // FP format
    input  logic [2:0]                             fpu_rm_i,         // FP rm
    input  logic [2:0]                             fpu_frm_i,        // FP frm csr
    input  logic [6:0]                             fpu_prec_i,       // FP precision control
    output logic [TRANS_ID_BITS-1:0]               fpu_trans_id_o,
    output logic [63:0]                            fpu_result_o,
    output logic                                   fpu_valid_o,
    output exception_t                             fpu_exception_o,
    // Memory Management
    input  logic                                   enable_translation_i,
    input  logic                                   en_ld_st_translation_i,
    input  logic                                   flush_tlb_i,

    input  riscv::priv_lvl_t                       priv_lvl_i,
    input  riscv::priv_lvl_t                       ld_st_priv_lvl_i,
    input  logic                                   sum_i,
    input  logic                                   mxr_i,
    input  logic [43:0]                            satp_ppn_i,
    input  logic [ASID_WIDTH-1:0]                  asid_i,
    // icache translation requests
    input  icache_areq_o_t                         icache_areq_i,
    output icache_areq_i_t                         icache_areq_o,

    // interface to dcache
    input  dcache_req_o_t [2:0]                    dcache_req_ports_i,
    output dcache_req_i_t [2:0]                    dcache_req_ports_o,
    output amo_req_t                               amo_req_o,          // request to cache subsytem
    input  amo_resp_t                              amo_resp_i,         // response from cache subsystem
    // Performance counters
    output logic                                   itlb_miss_o,
    output logic                                   dtlb_miss_o
);

    // -------------------------
    // Fixed Latency Units
    // -------------------------
    // all fixed latency units share a single issue port and a sing write
    // port into the scoreboard. At the moment those are:
    // 1. ALU - all operations are single cycle
    // 2. Branch unit: operation is single cycle, the ALU is needed
    //    for comparison
    // 3. CSR: This is a small buffer which saves the address of the CSR.
    //    The value is then re-fetched once the instruction retires. The buffer
    //    is only a single entry deep, hence this operation will block all
    //    other operations once this buffer is full. This should not be a major
    //    concern though as CSRs are infrequent.
    // 4. Multiplier/Divider: The multiplier has a fixed latency of 1 cycle.
    //                        The issue logic will take care of not issuing
    //                        another instruction if it will collide on the
    //                        output port. Divisions are arbitrary in length
    //                        they will simply block the issue of all other
    //                        instructions.

    // from ALU to branch unit
    logic alu_branch_res; // branch comparison result
    logic [63:0] alu_result, branch_result, csr_result, mult_result;
    logic csr_ready, mult_ready;
    logic [TRANS_ID_BITS-1:0] mult_trans_id;
    logic mult_valid;

    // 1. ALU (combinatorial)
    // data silence operation
    fu_data_t alu_data;
    assign alu_data = (alu_valid_i | branch_valid_i) ? fu_data_i  : '0;

    alu alu_i (
        .clk_i,
        .rst_ni,
        .fu_data_i        ( alu_data       ),
        .result_o         ( alu_result     ),
        .alu_branch_res_o ( alu_branch_res )
    );

    // 2. Branch Unit (combinatorial)
    // we don't silence the branch unit as this is already critical and we do
    // not want to add another layer of logic
    branch_unit branch_unit_i (
        .fu_data_i,
        .pc_i,
        .is_compressed_instr_i,
        // any functional unit is valid, check that there is no accidental mis-predict
        .fu_valid_i ( alu_valid_i || lsu_valid_i || csr_valid_i || mult_valid_i || fpu_valid_i ) ,
        .branch_valid_i,
        .branch_comp_res_i ( alu_branch_res ),
        .branch_result_o   ( branch_result ),
        .branch_predict_i,
        .resolved_branch_o,
        .resolve_branch_o,
        .branch_exception_o ( flu_exception_o )
    );

    // 3. CSR (sequential)
    csr_buffer csr_buffer_i (
        .clk_i,
        .rst_ni,
        .flush_i,
        .fu_data_i,
        .csr_valid_i,
        .csr_ready_o    ( csr_ready    ),
        .csr_result_o   ( csr_result   ),
        .csr_commit_i,
        .csr_addr_o
    );

    assign flu_valid_o = alu_valid_i | branch_valid_i | csr_valid_i | mult_valid;

    // result MUX
    always_comb begin
        // Branch result as default case
        flu_result_o = branch_result;
        flu_trans_id_o = fu_data_i.trans_id;
        // ALU result
        if (alu_valid_i) begin
            flu_result_o = alu_result;
        // CSR result
        end else if (csr_valid_i) begin
            flu_result_o = csr_result;
        end else if (mult_valid) begin
            flu_result_o = mult_result;
            flu_trans_id_o = mult_trans_id;
        end
    end

    // ready flags for FLU
    always_comb begin
        flu_ready_o = csr_ready & mult_ready;
    end

    // 4. Multiplication (Sequential)
    fu_data_t mult_data;
    // input silencing of multiplier
    assign mult_data  = mult_valid_i ? fu_data_i  : '0;

    mult i_mult (
        .clk_i,
        .rst_ni,
        .flush_i,
        .mult_valid_i,
        .fu_data_i       ( mult_data     ),
        .result_o        ( mult_result   ),
        .mult_valid_o    ( mult_valid    ),
        .mult_ready_o    ( mult_ready    ),
        .mult_trans_id_o ( mult_trans_id )
    );

    // ----------------
    // FPU
    // ----------------
    generate
        if (FP_PRESENT) begin : fpu_gen
            fu_data_t fpu_data;
            assign fpu_data  = fpu_valid_i ? fu_data_i  : '0;

            fpu_wrap fpu_i (
                .clk_i,
                .rst_ni,
                .flush_i,
                .fpu_valid_i,
                .fpu_ready_o,
                .fu_data_i ( fpu_data ),
                .fpu_fmt_i,
                .fpu_rm_i,
                .fpu_frm_i,
                .fpu_prec_i,
                .fpu_trans_id_o,
                .result_o ( fpu_result_o ),
                .fpu_valid_o,
                .fpu_exception_o
            );
        end else begin : no_fpu_gen
            assign fpu_ready_o     = '0;
            assign fpu_trans_id_o  = '0;
            assign fpu_result_o    = '0;
            assign fpu_valid_o     = '0;
            assign fpu_exception_o = '0;
        end
    endgenerate

    // ----------------
    // Load-Store Unit
    // ----------------
    fu_data_t lsu_data;

    assign lsu_data  = lsu_valid_i ? fu_data_i  : '0;

    load_store_unit lsu_i (
        .clk_i,
        .rst_ni,
        .flush_i,
        .no_st_pending_o,
        .fu_data_i             ( lsu_data ),
        .lsu_ready_o,
        .lsu_valid_i,
        .load_trans_id_o,
        .load_result_o,
        .load_valid_o,
        .load_exception_o,
        .store_trans_id_o,
        .store_result_o,
        .store_valid_o,
        .store_exception_o,
        .commit_i              ( lsu_commit_i       ),
        .commit_ready_o        ( lsu_commit_ready_o ),
        .enable_translation_i,
        .en_ld_st_translation_i,
        .icache_areq_i,
        .icache_areq_o,
        .priv_lvl_i,
        .ld_st_priv_lvl_i,
        .sum_i,
        .mxr_i,
        .satp_ppn_i,
        .asid_i,
        .flush_tlb_i,
        .itlb_miss_o,
        .dtlb_miss_o,
        .dcache_req_ports_i,
        .dcache_req_ports_o,
        .amo_valid_commit_i,
        .amo_req_o,
        .amo_resp_i
    );

endmodule
