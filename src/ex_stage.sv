
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
    parameter ariane_pkg::ariane_cfg_t ArianeCfg = ariane_pkg::ArianeDefaultConfig
) (
    input  logic                                    clk_i,    // Clock
    input  logic                                    rst_ni,   // Asynchronous reset active low
    input  logic                                    flush_i,
    input  logic                                    debug_mode_i,

    input  logic [63:0]                             pc_i,                  // PC of current instruction
    input  logic                                    is_compressed_instr_i, // we need to know if this was a compressed instruction
                                                                          // in order to calculate the next PC on a mis-predict
    input  fu_data_t [ISSUE_WIDTH-1:0]              fu_data_i,
    // Fixed latency unit(s)
    output logic [NR_FLU-1:0][63:0]                 flu_result_o,
    output logic [NR_FLU-1:0][TRANS_ID_BITS-1:0]    flu_trans_id_o,        // ID of scoreboard entry at which to write back
    output exception_t [NR_FLU-1:0]                 flu_exception_o,
    output logic [NR_FLU-1:0]                       flu_ready_o,           // FLU is ready
    output logic [NR_FLU-1:0]                       flu_valid_o,           // FLU result is valid
    output logic [NR_FLU-1:0]                       flu_flush_o,           // FLU result is flushed due to the mispredict
    // Branches and Jumps
    // ALU 1 and 2
    input  logic [NR_ALU-1:0]                       alu_valid_i,           // Output is valid
    input  logic [NR_ALU-1:0][ISSUE_WIDTH_BITS-1:0] alu_fu_idx_i,
    // Branch Unit
    input  logic                                    branch_valid_i,        // we are using the branch unit
    input  branchpredict_sbe_t                      branch_predict_i,
    input  logic [ISSUE_WIDTH_BITS-1:0]             branch_fu_idx_i,
    output bp_resolve_t                             resolved_branch_o,     // the branch engine uses the write back from the ALU
    output logic                                    resolve_branch_o,      // to ID signaling that we resolved the branch
    // CSR
    input  logic                                    csr_valid_i,
    input  logic [ISSUE_WIDTH_BITS-1:0]             csr_fu_idx_i,
    output logic [11:0]                             csr_addr_o,
    input  logic                                    csr_commit_i,

    // MULT
    input  logic                                    mult_valid_i,          // Output is valid
    input  logic [ISSUE_WIDTH_BITS-1:0]             mult_fu_idx_i,

    // LSU
    output logic                                    lsu_ready_o,           // FU is ready
    input  logic [ISSUE_WIDTH_BITS-1:0]             lsu_fu_idx_i,
    input  logic                                    lsu_valid_i,           // Input is valid
    output logic                                    lsu_flush_o,          // mult result is flushed due to the mispredict

    output logic                                    load_valid_o,
    output logic [63:0]                             load_result_o,
    output logic [TRANS_ID_BITS-1:0]                load_trans_id_o,
    output exception_t                              load_exception_o,
    output logic                                    store_valid_o,
    output logic [63:0]                             store_result_o,
    output logic [TRANS_ID_BITS-1:0]                store_trans_id_o,
    output exception_t                              store_exception_o,

    input  logic                                    lsu_commit_i,
    output logic                                    lsu_commit_ready_o, // commit queue is ready to accept another commit request
    output logic                                    no_st_pending_o,
    input  logic                                    amo_valid_commit_i,
    // FPU
    output logic                                    fpu_ready_o,      // FU is ready
    input  logic [ISSUE_WIDTH_BITS-1:0]             fpu_fu_idx_i,
    input  logic                                    fpu_valid_i,      // Output is valid
    input  logic [1:0]                              fpu_fmt_i,        // FP format
    input  logic [2:0]                              fpu_rm_i,         // FP rm
    input  logic [2:0]                              fpu_frm_i,        // FP frm csr
    input  logic [6:0]                              fpu_prec_i,       // FP precision control
    output logic [TRANS_ID_BITS-1:0]                fpu_trans_id_o,
    output logic [63:0]                             fpu_result_o,
    output logic                                    fpu_valid_o,
    output logic                                    fpu_flush_o,      // fpu result is flushed due to the mispredict

    output exception_t                              fpu_exception_o,
    // Memory Management
    input  logic                                    enable_translation_i,
    input  logic                                    en_ld_st_translation_i,
    input  logic                                    flush_tlb_i,

    input  riscv::priv_lvl_t                        priv_lvl_i,
    input  riscv::priv_lvl_t                        ld_st_priv_lvl_i,
    input  logic                                    sum_i,
    input  logic                                    mxr_i,
    input  logic [43:0]                             satp_ppn_i,
    input  logic [ASID_WIDTH-1:0]                   asid_i,
    // icache translation requests
    input  icache_areq_o_t                          icache_areq_i,
    output icache_areq_i_t                          icache_areq_o,

    // interface to dcache
    input  dcache_req_o_t [2:0]                     dcache_req_ports_i,
    output dcache_req_i_t [2:0]                     dcache_req_ports_o,
    output amo_req_t                                amo_req_o,          // request to cache subsytem
    input  amo_resp_t                               amo_resp_i,         // response from cache subsystem
    // Performance counters
    output logic                                    itlb_miss_o,
    output logic                                    dtlb_miss_o
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
    logic [NR_ALU-1:0][63:0] alu_result;
    logic [63:0] branch_result, csr_result, mult_result;
    logic csr_ready, mult_ready;
    logic [TRANS_ID_BITS-1:0] mult_trans_id;
    logic mult_valid_o;
    logic [NR_ALU-1:0] alu_valid, alu_flush;
    logic csr_valid, mult_valid, fpu_valid, lsu_valid,
          csr_flush, mult_flush;
    logic [TRANS_ID_BITS-1:0] load_trans_id, store_trans_id;


    // 1. ALU (combinatorial)
    // data silence operation
    fu_data_t [NR_ALU-1:0] alu_data;
    always_comb begin
        // Flush ALU result if it is after a misprediction
        for (int unsigned i = 0; i < NR_ALU; i++) begin
            alu_flush[i] = alu_valid_i[i] & (alu_fu_idx_i[i] > branch_fu_idx_i) & branch_valid_i & resolved_branch_o.is_mispredict;
            alu_valid[i] = alu_valid_i[i] & ~((alu_fu_idx_i[i] > branch_fu_idx_i) & branch_valid_i & resolved_branch_o.is_mispredict);
        end

        // ALU 1
        if (alu_valid_i[0]) begin
            alu_data[0] = fu_data_i[alu_fu_idx_i[0]];
        end else begin
            alu_data[0] = '0;
        end

        // ALU 2 contains basic ALU and branch unit
        if (alu_valid_i[1]) begin
            alu_data[1] = fu_data_i[alu_fu_idx_i[1]];
        end else if (branch_valid_i) begin
            alu_data[1] = fu_data_i[branch_fu_idx_i];
        end else begin
            alu_data[1] = '0;
        end

    end

    alu alu_1_i (
        .clk_i,
        .rst_ni,
        .fu_data_i        ( alu_data[0]    ),
        .result_o         ( alu_result[0]  ),
        .alu_branch_res_o (                )
    );

    alu alu_2_i (
        .clk_i,
        .rst_ni,
        .fu_data_i        ( alu_data[1]       ),
        .result_o         ( alu_result[1]     ),
        .alu_branch_res_o ( alu_branch_res    )
    );

    // 2. Branch Unit (combinatorial)
    // we don't silence the branch unit as this is already critical and we do
    // not want to add another layer of logic
    branch_unit branch_unit_i (
        .clk_i,
        .rst_ni,
        .debug_mode_i,
        .fu_data_i  (fu_data_i[branch_fu_idx_i]),
        .pc_i,
        .is_compressed_instr_i,
        // any functional unit is valid, check that there is no accidental mis-predict
        .fu_valid_i ( (|alu_valid) || lsu_valid || csr_valid || mult_valid || fpu_valid ) ,
        .branch_valid_i,
        .branch_comp_res_i ( alu_branch_res ),
        .branch_result_o   ( branch_result ),
        .branch_predict_i,
        .resolved_branch_o,
        .resolve_branch_o,
        .branch_exception_o ( flu_exception_o[1])
    );
    assign flu_exception_o[0] = '0;

    // 3. CSR (sequential)
    assign csr_flush = csr_valid_i & (csr_fu_idx_i > branch_fu_idx_i) & branch_valid_i & resolved_branch_o.is_mispredict;
    assign csr_valid = csr_valid_i & ~((csr_fu_idx_i > branch_fu_idx_i) & branch_valid_i & resolved_branch_o.is_mispredict);
    csr_buffer csr_buffer_i (
        .clk_i,
        .rst_ni,
        .flush_i,
        .fu_data_i    ( fu_data_i[csr_fu_idx_i] ),
        .csr_valid_i  ( csr_valid               ),
        .csr_ready_o  ( csr_ready               ),
        .csr_result_o ( csr_result              ),
        .csr_commit_i,
        .csr_addr_o
    );

    // first FLU port is used by one ALU and one multiplier
    // second FLU port is used by one ALU, one csr and one branch unit
    assign flu_valid_o[0] = alu_valid[0] | mult_valid_o;
    assign flu_flush_o[0] = alu_flush[0] | mult_flush;
    assign flu_valid_o[1] = alu_valid[1] | branch_valid_i | csr_valid;
    assign flu_flush_o[1] = alu_flush[1] | csr_flush;

    // result MUX
    always_comb begin
        // default case
        flu_result_o[0] = alu_result[0];
        flu_trans_id_o[0] = fu_data_i[alu_fu_idx_i[0]].trans_id;
        flu_result_o[1] = alu_result[1];
        flu_trans_id_o[1] = fu_data_i[alu_fu_idx_i[1]].trans_id;

        // ALU 1 result
        if (mult_valid_o | mult_flush) begin
            flu_result_o[0] = mult_result;
            flu_trans_id_o[0] = mult_trans_id;
        end

        // ALU 2 result
        if (branch_valid_i) begin
            flu_result_o[1] = branch_result;
            flu_trans_id_o[1] = fu_data_i[branch_fu_idx_i];
        end else if (csr_valid | csr_flush) begin
            flu_result_o[1]  = csr_result;
            flu_trans_id_o[1] = fu_data_i[csr_fu_idx_i].trans_id;
        end
    end

    // ready flags for FLU
    always_comb begin
        flu_ready_o[0] = mult_ready;
        flu_ready_o[1] = csr_ready;
    end

    // 4. Multiplication (Sequential)
    fu_data_t mult_data;
    assign mult_flush = mult_valid_i & (mult_fu_idx_i > branch_fu_idx_i) & branch_valid_i & resolved_branch_o.is_mispredict;
    assign mult_valid = mult_valid_i & ~((mult_fu_idx_i > branch_fu_idx_i) & branch_valid_i & resolved_branch_o.is_mispredict);
    // input silencing of multiplier
    assign mult_data  = mult_valid ? fu_data_i[mult_fu_idx_i]  : '0;

    mult i_mult (
        .clk_i,
        .rst_ni,
        .flush_i,
        .mult_valid_i    ( mult_valid    ),
        .fu_data_i       ( mult_data     ),
        .result_o        ( mult_result   ),
        .mult_valid_o    ( mult_valid_o  ),
        .mult_ready_o    ( mult_ready    ),
        .mult_trans_id_o ( mult_trans_id )
    );

    // ----------------
    // FPU
    // ----------------
    generate
        if (FP_PRESENT) begin : fpu_gen
            fu_data_t fpu_data;
            assign fpu_flush_o = fpu_valid_i & (fpu_fu_idx_i > branch_fu_idx_i) & branch_valid_i & resolved_branch_o.is_mispredict;
            assign fpu_data  = fpu_valid ? fu_data_i[fpu_fu_idx_i] : '0;
            assign fpu_valid = fpu_valid_i & ~((fpu_fu_idx_i > branch_fu_idx_i) & branch_valid_i & resolved_branch_o.is_mispredict);
            fpu_wrap fpu_i (
                .clk_i,
                .rst_ni,
                .flush_i,
                .fpu_valid_i ( fpu_valid ),
                .fpu_ready_o,
                .fu_data_i   ( fpu_data  ),
                .fpu_fmt_i,
                .fpu_rm_i,
                .fpu_frm_i,
                .fpu_prec_i,
                .fpu_trans_id_o,
                .result_o    ( fpu_result_o ),
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

    assign lsu_flush_o = lsu_valid_i & (lsu_fu_idx_i > branch_fu_idx_i) & branch_valid_i & resolved_branch_o.is_mispredict;
    assign lsu_valid = lsu_valid_i & ~((lsu_fu_idx_i > branch_fu_idx_i) & branch_valid_i & resolved_branch_o.is_mispredict);
    assign lsu_data  = lsu_valid ? fu_data_i[lsu_fu_idx_i] : '0;
    assign load_trans_id_o = lsu_flush_o ? fu_data_i[lsu_fu_idx_i].trans_id : load_trans_id;
    assign store_trans_id_o = lsu_flush_o ? fu_data_i[lsu_fu_idx_i].trans_id : store_trans_id;

    load_store_unit #(
      .ArianeCfg ( ArianeCfg )
    ) lsu_i (
        .clk_i,
        .rst_ni,
        .flush_i,
        .no_st_pending_o,
        .fu_data_i             ( lsu_data           ),
        .lsu_ready_o,
        .lsu_valid_i           ( lsu_valid          ),
        .load_trans_id_o       ( load_trans_id      ),
        .load_result_o,
        .load_valid_o,
        .load_exception_o,
        .store_trans_id_o      ( store_trans_id     ),
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
