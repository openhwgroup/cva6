// Author: Florian Zaruba, ETH Zurich
// Date: 09.05.2017
// Description: Branch target calculation and comparison
//
//
// Copyright (C) 2017 ETH Zurich, University of Bologna
// All rights reserved.
//
// This code is under development and not yet released to the public.
// Until it is released, the code is under the copyright of ETH Zurich and
// the University of Bologna, and may contain confidential and/or unpublished
// work. Any reuse/redistribution is strictly forbidden without written
// permission from ETH Zurich.
//
// Bug fixes and contributions will eventually be released under the
// SolderPad open hardware license in the context of the PULP platform
// (http://www.pulp-platform.org), under the copyright of ETH Zurich and the
// University of Bologna.
//
import ariane_pkg::*;

module branch_unit (
    input  logic [TRANS_ID_BITS-1:0]  trans_id_i,
    input  fu_op                      operator_i,             // comparison operation to perform
    input  logic [63:0]               operand_a_i,            // contains content of RS 1
    input  logic [63:0]               operand_b_i,            // contains content of RS 2
    input  logic [63:0]               imm_i,                  // immediate to add to PC
    input  logic [63:0]               pc_i,                   // PC of instruction
    input  logic                      is_compressed_instr_i,
    input  logic                      fu_valid_i,             // any functional unit is valid, check that there is no accidental mis-predict
    input  logic                      branch_valid_i,
    output logic                      branch_ready_o,
    output logic                      branch_valid_o,
    output logic [63:0]               branch_result_o,
    output logic [TRANS_ID_BITS-1:0]  branch_trans_id_o,

    input  branchpredict_sbe          branch_predict_i,       // this is the address we predicted
    output branchpredict              resolved_branch_o,      // this is the actual address we are targeting
    output logic                      resolve_branch_o,       // to ID to clear that we resolved the branch and we can
                                                              // accept new entries to the scoreboard
    output exception                  branch_exception_o      // branch exception out
);
    logic [63:0] target_address;
    logic [63:0] next_pc;
    logic        comparison_result; // result of comparison
    logic        sgn;               // sign extend
    // branches are single cycle at the moment, feed-through the control signals
    assign branch_trans_id_o = trans_id_i;
    assign branch_valid_o    = branch_valid_i;
    assign branch_ready_o    = 1'b1; // we are always ready

    always_comb begin : branch_resolve
        // by default e.g.: when this is a jump, the branch is taken
        // so set the comparison result to 1
        comparison_result = 1'b1;
        // sign switch
        sgn = 1'b1;
        // if this is an unsigned operation clear the sign bit
        // this should ease data-path extraction
        if (operator_i inside {LTU, GEU})
            sgn = 1'b0;
        // get the right comparison result
        case (operator_i)
            EQ:  comparison_result = operand_a_i == operand_b_i;
            NE:  comparison_result = operand_a_i != operand_b_i;
            LTS: comparison_result = ($signed({sgn & operand_a_i[63], operand_a_i})   <  $signed({sgn & operand_b_i[63], operand_b_i}));
            GES: comparison_result = ($signed({sgn & operand_a_i[63], operand_a_i})  >=  $signed({sgn & operand_b_i[63], operand_b_i}));
            default: comparison_result = 1'b1;
        endcase
    end
    // here we handle the various possibilities of mis-predicts
    always_comb begin : mispredict_handler
        target_address                   = 64'b0;
        resolved_branch_o.pc             = pc_i;
        resolved_branch_o.target_address = 64'b0;
        resolved_branch_o.is_taken       = 1'b0;
        resolved_branch_o.valid          = branch_valid_i;
        resolved_branch_o.is_mispredict  = 1'b0;
        resolved_branch_o.is_lower_16    = 1'b0;
        resolved_branch_o.clear          = 1'b0;
        resolve_branch_o                 = 1'b0;
        // calculate next PC, depending on whether the instruction is compressed or not this may be different
        next_pc                          = pc_i + ((is_compressed_instr_i) ? 64'h2 : 64'h4);
        // calculate target address simple 64 bit addition
        target_address                   = $unsigned($signed(pc_i) + $signed(imm_i));
        // if we need to put the branch target address in a destination register, output it here to WB
        branch_result_o                  = target_address;

        if (branch_valid_i) begin
            // save PC - we need this to get the target row in the branch target buffer
            // we play this trick with the branch instruction which wraps a byte boundary:
            //  |---------- Place the prediction on this PC
            // \/
            // ____________________________________________________
            // |branch [15:0] | branch[31:16] | compressed 1[15:0] |
            // |____________________________________________________
            // This will relief the prefetcher to re-fetch partially fetched unaligned branch instructions e.g.:
            // we don't have a back arch between prefetcher and decoder/instruction FIFO.
            resolved_branch_o.pc = (is_compressed_instr_i || pc_i[1] == 1'b0) ? pc_i : ({pc_i[63:2], 2'b0} + 64'h4);
            // save if the branch instruction was in the lower 16 bit of the instruction word
            // the first case is a compressed instruction which is in slot 0
            // the other case is a misaligned uncompressed instruction which we only predict in the next cycle (see notes above)
            resolved_branch_o.is_lower_16 = (is_compressed_instr_i && pc_i[1] == 1'b0) || (!is_compressed_instr_i && pc_i[1] == 1'b1);
            // write target address which goes to pc gen
            resolved_branch_o.target_address = (comparison_result) ? target_address : next_pc;
            resolved_branch_o.is_taken       = comparison_result;
            // we've detected a branch in ID with the following parameters
            // we mis-predicted e.g.: the predicted address is unequal to the actual address
            if (target_address[0] == 1'b0) begin
                // we've got a valid branch prediction
                if (branch_predict_i.valid) begin
                    // if the address or the outcome don't match we've got a mis-predict
                    if (target_address != branch_predict_i.predict_address || branch_predict_i.predict_taken != comparison_result) begin
                        resolved_branch_o.is_mispredict  = 1'b1;
                    end
                // branch-prediction didn't do anything (e.g.: it fetched PC + 2/4), so if this branch is taken
                // we also have a mis-predict
                end else begin
                    if (comparison_result) begin
                        resolved_branch_o.is_mispredict = 1'b1;
                    end
                end
            end
            // to resolve the branch in ID -> only do this if this was indeed a branch (hence vald_i is asserted)
            resolve_branch_o = 1'b1;
        // the other case would be that this instruction was no branch but branch prediction thought that it was one
        // this is essentially also a mis-predict
        end else if (fu_valid_i && branch_predict_i.valid) begin
            // re-set the branch to the next PC
            resolved_branch_o.is_mispredict  = 1'b1;
            resolved_branch_o.target_address = next_pc;
            // clear this entry so that we are not constantly mis-predicting
            resolved_branch_o.clear          = 1'b1;
            resolved_branch_o.valid          = 1'b1;
        end
    end
    // use ALU exception signal for storing instruction fetch exceptions if
    // the target address is not aligned to a 2 byte boundary
    always_comb begin : exception_handling
        branch_exception_o.cause = INSTR_ADDR_MISALIGNED;
        branch_exception_o.valid = 1'b0;
        branch_exception_o.tval  = pc_i;
        // only throw exception if this is indeed a branch
        if (branch_valid_i && target_address[0] != 1'b0)
            branch_exception_o.valid = 1'b1;
    end
endmodule