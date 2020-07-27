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

module cva6_branch_unit (
    input  logic                      clk_i,
    input  logic                      rst_ni,
    input  logic                      debug_mode_i,
    input  cva6_pkg::fu_data_t      fu_data_i,
    input  logic [cva6_riscv::VLEN-1:0]    pc_i,                   // PC of instruction
    input  logic                      is_compressed_instr_i,
    input  logic                      fu_valid_i,             // any functional unit is valid, check that there is no accidental mis-predict
    input  logic                      branch_valid_i,
    input  logic                      branch_comp_res_i,      // branch comparison result from ALU
    output logic [cva6_riscv::VLEN-1:0]    branch_result_o,

    input  cva6_pkg::branchpredict_sbe_t        branch_predict_i,       // this is the address we predicted
    output cva6_pkg::bp_resolve_t               resolved_branch_o,      // this is the actual address we are targeting
    output logic                      resolve_branch_o,       // to ID to clear that we resolved the branch and we can
                                                              // accept new entries to the scoreboard
    output cva6_pkg::exception_t    branch_exception_o      // branch exception out
);
    logic [cva6_riscv::VLEN-1:0] target_address;
    logic [cva6_riscv::VLEN-1:0] next_pc;

   // here we handle the various possibilities of mis-predicts
    always_comb begin : mispredict_handler
        // set the jump base, for JALR we need to look at the register, for all other control flow instructions we can take the current PC
        automatic logic [cva6_riscv::VLEN-1:0] jump_base;
        // TODO(zarubaf): The ALU can be used to calculate the branch target
        jump_base = (fu_data_i.operator == cva6_pkg::JALR) ? fu_data_i.operand_a[cva6_riscv::VLEN-1:0] : pc_i;

        target_address                   = {cva6_riscv::VLEN{1'b0}};
        resolve_branch_o                 = 1'b0;
        resolved_branch_o.target_address = {cva6_riscv::VLEN{1'b0}};
        resolved_branch_o.is_taken       = 1'b0;
        resolved_branch_o.valid          = branch_valid_i;
        resolved_branch_o.is_mispredict  = 1'b0;
        resolved_branch_o.cf_type        = branch_predict_i.cf;
        // calculate next PC, depending on whether the instruction is compressed or not this may be different
        // TODO(zarubaf): We already calculate this a couple of times, maybe re-use?
        next_pc                          = pc_i + ((is_compressed_instr_i) ? {{cva6_riscv::VLEN-2{1'b0}}, 2'h2} : {{cva6_riscv::VLEN-3{1'b0}}, 3'h4});
        // calculate target address simple 64 bit addition
        target_address                   = $unsigned($signed(jump_base) + $signed(fu_data_i.imm[cva6_riscv::VLEN-1:0]));
        // on a JALR we are supposed to reset the LSB to 0 (according to the specification)
        if (fu_data_i.operator == cva6_pkg::JALR) target_address[0] = 1'b0;
        // we need to put the branch target address into rd, this is the result of this unit
        branch_result_o = next_pc;
        resolved_branch_o.pc = pc_i;
        // There are only two sources of mispredicts:
        // 1. Branches
        // 2. Jumps to register addresses
        if (branch_valid_i) begin
            // write target address which goes to PC Gen
            resolved_branch_o.target_address = (branch_comp_res_i) ? target_address : next_pc;
            resolved_branch_o.is_taken = branch_comp_res_i;
            // check the outcome of the branch speculation
            if (cva6_pkg::is_branch(fu_data_i.operator) && branch_comp_res_i != (branch_predict_i.cf == cva6_pkg::Branch)) begin
                // we mis-predicted the outcome
                // if the outcome doesn't match we've got a mis-predict
                resolved_branch_o.is_mispredict  = 1'b1;
                resolved_branch_o.cf_type = cva6_pkg::Branch;
            end
            if (fu_data_i.operator == cva6_pkg::JALR
                // check if the address of the jump register is correct and that we actually predicted
                && (branch_predict_i.cf == cva6_pkg::NoCF || target_address != branch_predict_i.predict_address)) begin
                resolved_branch_o.is_mispredict  = 1'b1;
                // update BTB only if this wasn't a return
                if (branch_predict_i.cf != cva6_pkg::Return) resolved_branch_o.cf_type = cva6_pkg::JumpR;
            end
            // to resolve the branch in ID
            resolve_branch_o = 1'b1;
        end
    end
    // use ALU exception signal for storing instruction fetch exceptions if
    // the target address is not aligned to a 2 byte boundary
    always_comb begin : exception_handling
        branch_exception_o.cause = cva6_riscv::INSTR_ADDR_MISALIGNED;
        branch_exception_o.valid = 1'b0;
        branch_exception_o.tval  = {{64-cva6_riscv::VLEN{pc_i[cva6_riscv::VLEN-1]}}, pc_i};
        // only throw exception if this is indeed a branch
        if (branch_valid_i && target_address[0] != 1'b0) branch_exception_o.valid = 1'b1;
    end
endmodule
