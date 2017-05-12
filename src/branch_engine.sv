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

module branch_engine (
    input  fu_op         operator_i,
    input  logic [63:0]  operand_a_i,
    input  logic [63:0]  operand_b_i,
    input  logic [63:0]  operand_c_i,
    input  logic [63:0]  imm_i,
    input  logic [63:0]  pc_i,
    input  logic         is_compressed_instr_i,
    input  logic         valid_i,

    input  logic [63:0]  predict_address_i,       // this is the address we predicted
    input  logic         predict_branch_valid_i,  // we predicted that this was a valid branch
    input  logic         predict_taken_i,
    output branchpredict branchpredict_o,         // this is the actual address we are targeting
    output exception     branch_ex_o              // branch exception out
);
    logic [63:0] target_address;
    logic [63:0] next_pc;
    logic        comparison_result; // result of comparison
    logic        sgn;               // sign extend

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

    always_comb begin : target_address_calc
        target_address                 = 64'b0;
        branchpredict_o.pc             = 64'b0;
        branchpredict_o.target_address = 64'b0;
        branchpredict_o.is_taken       = 1'b0;
        branchpredict_o.valid          = valid_i;
        branchpredict_o.is_mispredict  = 1'b0;
        // calculate next PC, depending on whether the instruction is compressed or not this may be different
        next_pc                        = pc_i + (is_compressed_instr_i) ? 64'h2 : 64'h4;
        // calculate target address simple 64 bit addition
        target_address                 = $signed(operand_c_i) + $signed(imm_i);
        // save pc
        branchpredict_o.pc = pc_i;
        // write target address which goes to pc gen
        branchpredict_o.target_address = (comparison_result) ? target_address : next_pc;
        branchpredict_o.is_taken       = comparison_result;

        if (valid_i) begin
            // we mis-predicted e.g.: the predicted address is unequal to the actual address
            if (target_address[1:0] == 2'b0) begin
                // TODO in case of branch which is not taken it is not necessary to check for the address
                if (   target_address != predict_address_i    // we mis-predicted the address of the branch
                    || predict_taken_i != comparison_result // we mis-predicted the outcome of the branch
                    || predict_branch_valid_i == 1'b0         // this means branch-prediction thought it was no branch but in reality it was one
                    ) begin
                    branchpredict_o.is_mispredict  = 1'b1;
                end
            end
        end
    end
    // use ALU exception signal for storing instruction fetch exceptions if
    // the target address is not aligned to a 4 byte boundary
    always_comb begin : exception_handling
        branch_ex_o.cause = INSTR_ADDR_MISALIGNED;
        branch_ex_o.tval  = 64'b0; // TODO
        branch_ex_o.valid = 1'b0;

        if (target_address[1:0] != 2'b0)
            branch_ex_o.valid = 1'b1;
    end
endmodule