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
    input  logic [63:0]  operand_a_i,
    input  logic [63:0]  operand_b_i,
    input  logic         valid_i,

    input  logic         comparison_result_i, // result of comparison
    input  logic [63:0]  predict_address_i,   // this is the address we predicted
    output branchpredict branchpredict_o,     // this is the actual address we are targeting
    output exception     branch_ex_o          // branch exception out
);
    logic [63:0] target_address;

    always_comb begin : target_address_calc
        target_address                 = 64'b0;
        branchpredict_o.pc             = 64'b0;
        branchpredict_o.target_address = 64'b0;
        branchpredict_o.is_taken       = 1'b0;
        branchpredict_o.valid          = valid_i;
        branchpredict_o.is_mispredict  = 1'b0;

        if (valid_i) begin
            // calculate target address simple 64 bit addition
            target_address = $signed(operand_a_i) + $signed(operand_b_i);
            // write target address
            branchpredict_o.target_address = target_address;
            branchpredict_o.is_taken       = comparison_result_i;
            // we mis-predicted e.g.: the predicted address is unequal to the actual address
            if (target_address != predict_address_i && target_address[1:0] == 2'b0) begin
                branchpredict_o.is_mispredict  = 1'b0;
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