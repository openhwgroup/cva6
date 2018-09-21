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
// Date: 15.09.2018
// Description: Combinatorial AMO unit
module amo_alu (
        // AMO interface
        input  ariane_pkg::amo_t  amo_op,
        input  logic [63:0]       amo_operand_a,
        input  logic [63:0]       amo_operand_b,
        output logic [63:0]       amo_result_o // result of atomic memory operation
);

    // TODO(zarubaf) Very crude first implementation
    always_comb begin
        amo_result_o = '0;
        case (amo_op)
            ariane_pkg::AMO_SC: begin
                amo_result_o = amo_operand_b;
            end
            ariane_pkg::AMO_SWAP: begin
                amo_result_o = amo_operand_b;
            end
            ariane_pkg::AMO_ADD: begin
                amo_result_o = $signed(amo_operand_a) + $signed(amo_operand_b);
            end
            ariane_pkg::AMO_AND: begin
                amo_result_o = amo_operand_a & amo_operand_b;
            end
            ariane_pkg::AMO_OR: begin
                amo_result_o = amo_operand_a | amo_operand_b;
            end
            ariane_pkg::AMO_XOR: begin
               amo_result_o = amo_operand_a ^ amo_operand_b;
            end
            ariane_pkg::AMO_MAX: begin
                amo_result_o = ($signed(amo_operand_a) > $signed(amo_operand_b)) ? amo_operand_a : amo_operand_b;
            end
            ariane_pkg::AMO_MAXU: begin
                amo_result_o = (amo_operand_a > amo_operand_b) ? amo_operand_a : amo_operand_b;
            end
            ariane_pkg::AMO_MIN: begin
                amo_result_o = ($signed(amo_operand_a) < $signed(amo_operand_b)) ? amo_operand_a : amo_operand_b;
            end
            ariane_pkg::AMO_MINU: begin
                amo_result_o = (amo_operand_a < amo_operand_b) ? amo_operand_a : amo_operand_b;
            end
            default:;
        endcase
    end
endmodule
