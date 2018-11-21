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
// Date: 09.05.2017
// Description: Branch target calculation and comparison

import ariane_pkg::*;

module branch_unit (
    input  fu_data_t                  fu_data_i,
    input  logic [63:0]               pc_i,                   // PC of instruction
    input  logic                      is_compressed_instr_i,
    input  logic                      fu_valid_i,             // any functional unit is valid, check that there is no accidental mis-predict
    input  logic                      branch_valid_i,
    input  logic                      branch_comp_res_i,      // branch comparison result from ALU
    output logic [63:0]               branch_result_o,

    input  branchpredict_sbe_t        branch_predict_i,       // this is the address we predicted
    output branchpredict_t            resolved_branch_o,      // this is the actual address we are targeting
    output logic                      resolve_branch_o,       // to ID to clear that we resolved the branch and we can
                                                              // accept new entries to the scoreboard
    output exception_t                branch_exception_o      // branch exception out
);
    logic [63:0] target_address;
    logic [63:0] next_pc;

    // here we handle the various possibilities of mis-predicts
    always_comb begin : mispredict_handler
        // set the jump base, for JALR we need to look at the register, for all other control flow instructions we can take the current PC
        automatic logic [63:0] jump_base;
        jump_base = (fu_data_i.operator == JALR) ? fu_data_i.operand_a : pc_i;

        resolve_branch_o                 = 1'b0;
        resolved_branch_o.target_address = 64'b0;
        resolved_branch_o.is_taken       = 1'b0;
        resolved_branch_o.valid          = branch_valid_i;
        resolved_branch_o.is_mispredict  = 1'b0;
        resolved_branch_o.clear          = 1'b0;
        resolved_branch_o.cf_type        = branch_predict_i.cf_type;
        // calculate next PC, depending on whether the instruction is compressed or not this may be different
        next_pc                          = pc_i + ((is_compressed_instr_i) ? 64'h2 : 64'h4);
        // calculate target address simple 64 bit addition
        target_address                   = $unsigned($signed(jump_base) + $signed(fu_data_i.imm));
        // on a JALR we are supposed to reset the LSB to 0 (according to the specification)
        if (fu_data_i.operator == JALR)
            target_address[0] = 1'b0;
        // if we need to put the branch target address in a destination register, output it here to WB
        branch_result_o = next_pc;

        // save PC - we need this to get the target row in the branch target buffer
        // we play this trick with the branch instruction which wraps a word boundary:
        //  /---------- Place the prediction on this PC
        // \/
        // ____________________________________________________
        // |branch [15:0] | branch[31:16] | compressed 1[15:0] |
        // |____________________________________________________
        // This will relief the pre-fetcher to re-fetch partially fetched unaligned branch instructions e.g.:
        // we don't have a back arch between the pre-fetcher and decoder/instruction FIFO.
        resolved_branch_o.pc = (is_compressed_instr_i || pc_i[1] == 1'b0) ? pc_i : ({pc_i[63:2], 2'b0} + 64'h4);

        if (branch_valid_i) begin
            // write target address which goes to pc gen
            resolved_branch_o.target_address = (branch_comp_res_i) ? target_address : next_pc;
            resolved_branch_o.is_taken       = branch_comp_res_i;
            // we've detected a branch in ID with the following parameters
            // we mis-predicted e.g.: the predicted address is unequal to the actual address
            if (target_address[0] == 1'b0) begin
                // we've got a valid branch prediction
                if (branch_predict_i.valid) begin
                    // if the outcome doesn't match we've got a mis-predict
                    if (branch_predict_i.predict_taken != branch_comp_res_i) begin
                        resolved_branch_o.is_mispredict  = 1'b1;
                    end
                    // check if the address of the predict taken branch is correct
                    if (branch_predict_i.predict_taken && target_address != branch_predict_i.predict_address) begin
                        resolved_branch_o.is_mispredict  = 1'b1;
                    end
                // branch-prediction didn't do anything (e.g.: it fetched PC + 2/4), so if this branch is taken
                // we also have a mis-predict
                end else begin
                    if (branch_comp_res_i) begin
                        resolved_branch_o.is_mispredict = 1'b1;
                    end
                end
            end
            // to resolve the branch in ID
            resolve_branch_o = 1'b1;
        // the other case would be that this instruction was no branch but branch prediction thought that it was one
        // this is essentially also a mis-predict
        end else if (fu_valid_i && branch_predict_i.valid && branch_predict_i.predict_taken) begin
            // re-set the branch to the next PC
            resolved_branch_o.is_mispredict  = 1'b1;
            resolved_branch_o.target_address = next_pc;
            // clear this entry so that we are not constantly mis-predicting
            resolved_branch_o.clear          = 1'b1;
            resolved_branch_o.valid          = 1'b1;
            resolve_branch_o                 = 1'b1;
        end
    end
    // use ALU exception signal for storing instruction fetch exceptions if
    // the target address is not aligned to a 2 byte boundary
    always_comb begin : exception_handling
        branch_exception_o.cause = riscv::INSTR_ADDR_MISALIGNED;
        branch_exception_o.valid = 1'b0;
        branch_exception_o.tval  = pc_i;
        // only throw exception if this is indeed a branch
        if (branch_valid_i && target_address[0] != 1'b0)
            branch_exception_o.valid = 1'b1;
    end
endmodule
