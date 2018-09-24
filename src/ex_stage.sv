
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

module ex_stage #(
    parameter int          ASID_WIDTH       = 1
)(
    input  logic                                   clk_i,    // Clock
    input  logic                                   rst_ni,   // Asynchronous reset active low
    input  logic                                   flush_i,

    input  fu_t                                    fu_i,
    input  fu_op                                   operator_i,
    input  logic [63:0]                            operand_a_i,
    input  logic [63:0]                            operand_b_i,
    input  logic [63:0]                            imm_i,
    input  logic [TRANS_ID_BITS-1:0]               trans_id_i,
    input  logic [63:0]                            pc_i,                  // PC of current instruction
    input  logic                                   is_compressed_instr_i, // we need to know if this was a compressed instruction
                                                                          // in order to calculate the next PC on a mis-predict
    // ALU 1
    output logic                                   alu_ready_o,           // FU is ready
    input  logic                                   alu_valid_i,           // Output is valid
    output logic                                   alu_valid_o,           // ALU result is valid
    output logic [63:0]                            alu_result_o,
    output logic [TRANS_ID_BITS-1:0]               alu_trans_id_o,        // ID of scoreboard entry at which to write back
    output exception_t                             alu_exception_o,
    // Branches and Jumps
    input  logic                                   branch_valid_i,        // we are using the branch unit
    input  branchpredict_sbe_t                     branch_predict_i,
    output branchpredict_t                         resolved_branch_o,     // the branch engine uses the write back from the ALU
    output logic                                   resolve_branch_o,      // to ID signaling that we resolved the branch
    // CSR
    input  logic                                   csr_valid_i,
    output logic [11:0]                            csr_addr_o,
    input  logic                                   csr_commit_i,
    // LSU
    output logic                                   lsu_ready_o,           // FU is ready
    input  logic                                   lsu_valid_i,           // Input is valid
    output logic                                   lsu_valid_o,           // Output is valid
    output logic [63:0]                            lsu_result_o,
    output logic [TRANS_ID_BITS-1:0]               lsu_trans_id_o,
    input  logic                                   lsu_commit_i,
    output logic                                   lsu_commit_ready_o,    // commit queue is ready to accept another commit request
    output exception_t                             lsu_exception_o,
    output logic                                   no_st_pending_o,
    input  logic                                   amo_valid_commit_i,
    // MULT
    output logic                                   mult_ready_o,      // FU is ready
    input  logic                                   mult_valid_i,      // Output is valid
    output logic [TRANS_ID_BITS-1:0]               mult_trans_id_o,
    output logic [63:0]                            mult_result_o,
    output logic                                   mult_valid_o,
    // FPU
    output logic                                   fpu_ready_o,      // FU is ready
    input  logic                                   fpu_valid_i,      // Output is valid
    input  logic [1:0]                             fpu_fmt_i,        // FP format
    input  logic [2:0]                             fpu_rm_i,         // FP rm
    input  logic [2:0]                             fpu_frm_i,        // FP frm csr
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

    logic alu_branch_res; // branch comparison result

    // -----
    // ALU
    // -----
    fu_data_t alu_data;
    assign alu_data.operator  = (alu_valid_i | branch_valid_i | csr_valid_i) ? operator_i  : ADD;
    assign alu_data.operand_a = (alu_valid_i | branch_valid_i | csr_valid_i) ? operand_a_i : '0;
    assign alu_data.operand_b = (alu_valid_i | branch_valid_i | csr_valid_i) ? operand_b_i : '0;
    assign alu_data.imm       = (alu_valid_i | branch_valid_i | csr_valid_i) ? imm_i : '0;

    // fixed latency FUs
    // TOOD(zarubaf) Re-name this module and re-factor ALU
    alu alu_i (
        .clk_i,
        .rst_ni,
        .flush_i,
        .pc_i,
        .trans_id_i,
        .alu_valid_i,
        .branch_valid_i,
        .csr_valid_i      ( csr_valid_i        ),
        .operator_i       ( alu_data.operator  ),
        .operand_a_i      ( alu_data.operand_a ),
        .operand_b_i      ( alu_data.operand_b ),
        .imm_i            ( alu_data.imm       ),
        .result_o         ( alu_result_o       ),
        .alu_valid_o,
        .alu_ready_o,
        .alu_trans_id_o,
        .alu_exception_o,

        .fu_valid_i       ( alu_valid_i || lsu_valid_i || csr_valid_i || mult_valid_i || fpu_valid_i ),
        .is_compressed_instr_i,
        .branch_predict_i,
        .resolved_branch_o,
        .resolve_branch_o,

        .commit_i        ( csr_commit_i ),
        .csr_addr_o      ( csr_addr_o   )
    );

    // ----------------
    // Multiplication
    // ----------------
    fu_data_t mult_data;
    assign mult_data.operator  = mult_valid_i ? operator_i  : MUL;
    assign mult_data.operand_a = mult_valid_i ? operand_a_i : '0;
    assign mult_data.operand_b = mult_valid_i ? operand_b_i : '0;

    mult i_mult (
        .clk_i,
        .rst_ni,
        .flush_i,
        .trans_id_i,
        .mult_valid_i,
        .operator_i      ( mult_data.operator  ),
        .operand_a_i     ( mult_data.operand_a ),
        .operand_b_i     ( mult_data.operand_b ),
        .result_o        ( mult_result_o       ),
        .mult_valid_o,
        .mult_ready_o,
        .mult_trans_id_o
    );

    // ----------------
    // FPU
    // ----------------
    generate
        if (FP_PRESENT) begin : fpu_gen
            fu_data_t fpu_data;
            assign fpu_data.operator  = fpu_valid_i ? operator_i  : FSGNJ;
            assign fpu_data.operand_a = fpu_valid_i ? operand_a_i : '0;
            assign fpu_data.operand_b = fpu_valid_i ? operand_b_i : '0;
            assign fpu_data.imm       = fpu_valid_i ? imm_i       : '0;

            fpu_wrap fpu_i (
                .clk_i,
                .rst_ni,
                .flush_i,
                .trans_id_i,
                .fu_i,
                .fpu_valid_i,
                .fpu_ready_o,
                .operator_i      ( fpu_data.operator            ),
                .operand_a_i     ( fpu_data.operand_a[FLEN-1:0] ),
                .operand_b_i     ( fpu_data.operand_b[FLEN-1:0] ),
                .operand_c_i     ( fpu_data.imm[FLEN-1:0]       ),
                .fpu_fmt_i,
                .fpu_rm_i,
                .fpu_frm_i,
                .fpu_trans_id_o,
                .result_o        ( fpu_result_o ),
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
    assign lsu_data.operator  = lsu_valid_i ? operator_i  : LD;
    assign lsu_data.operand_a = lsu_valid_i ? operand_a_i : '0;
    assign lsu_data.operand_b = lsu_valid_i ? operand_b_i : '0;
    assign lsu_data.imm       = lsu_valid_i ? imm_i       : '0;

    lsu lsu_i (
        .clk_i                                         ,
        .rst_ni                                        ,
        .flush_i                                       ,
        .no_st_pending_o                               ,
        .fu_i                                          ,
        .operator_i            (lsu_data.operator     ),
        .operand_a_i           (lsu_data.operand_a    ),
        .operand_b_i           (lsu_data.operand_b    ),
        .imm_i                 (lsu_data.imm          ),
        .lsu_ready_o                                   ,
        .lsu_valid_i                                   ,
        .trans_id_i                                    ,
        .lsu_trans_id_o                                ,
        .lsu_result_o                                  ,
        .lsu_valid_o                                   ,
        .commit_i              (lsu_commit_i          ),
        .commit_ready_o        (lsu_commit_ready_o    ),
        .enable_translation_i                          ,
        .en_ld_st_translation_i                        ,
        .icache_areq_i                                 ,
        .icache_areq_o                                 ,
        .priv_lvl_i                                    ,
        .ld_st_priv_lvl_i                              ,
        .sum_i                                         ,
        .mxr_i                                         ,
        .satp_ppn_i                                    ,
        .asid_i                                        ,
        .flush_tlb_i                                   ,
        .itlb_miss_o                                   ,
        .dtlb_miss_o                                   ,
        .dcache_req_ports_i                            ,
        .dcache_req_ports_o                            ,
        .lsu_exception_o                               ,
        .amo_valid_commit_i                            ,
        .amo_req_o                                     ,
        .amo_resp_i
    );

endmodule
