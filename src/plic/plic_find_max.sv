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
//-------------------------------------------------------------------------------
//-- Title      : Find Maximun
//-- File       : plic_find_max.sv
//-- Author     : Gian Marti      <gimarti.student.ethz.ch>
//-- Author     : Thomas Kramer   <tkramer.student.ethz.ch>
//-- Author     : Thomas E. Benz  <tbenz.student.ethz.ch>
//-- Company    : Integrated Systems Laboratory, ETH Zurich
//-- Created    : 2018-03-31
//-- Last update: 2018-03-31
//-- Platform   : ModelSim (simulation), Synopsys (synthesis)
//-- Standard   : SystemVerilog IEEE 1800-2012
//-------------------------------------------------------------------------------
//-- Description: Find the element with the largest priority
//-------------------------------------------------------------------------------
//-- Revisions  :
//-- Date        Version  Author  Description
//-- 2018-03-31  2.0      tbenz   Created header
//-------------------------------------------------------------------------------

module plic_find_max #(
    parameter int NUM_OPERANDS      = 2,
    parameter int ID_BITWIDTH       = 4,
    parameter int PRIORITY_BITWIDTH = 3
)(
    input  logic [PRIORITY_BITWIDTH-1:0] priorities_i  [NUM_OPERANDS],
    input  logic [ID_BITWIDTH-1:0      ] identifiers_i [NUM_OPERANDS],
    output logic [PRIORITY_BITWIDTH-1:0] largest_priority_o,
    output logic [ID_BITWIDTH-1:0      ] identifier_of_largest_o
);

    localparam int max_stage            = ($clog2(NUM_OPERANDS)-1);
    localparam int num_operands_aligned = 2**(max_stage+1);

    logic [PRIORITY_BITWIDTH-1:0] priority_stages   [max_stage + 2][num_operands_aligned];
    logic [ID_BITWIDTH-1:0      ] identifier_stages [max_stage + 2][num_operands_aligned];


    always_comb begin : proc_zero_padding
        for (integer operand = 0; operand < num_operands_aligned; operand++) begin
            if(operand < NUM_OPERANDS) begin
                priority_stages  [0][operand] = priorities_i  [operand];
                identifier_stages[0][operand] = identifiers_i [operand];
            end else begin
                priority_stages  [0][operand] = '0;
                identifier_stages[0][operand] = '0;
            end
        end
    end

    for (genvar comparator_stage = max_stage; comparator_stage >= 0 ; comparator_stage--) begin
        for (genvar stage_index  = 0; stage_index < 2**comparator_stage; stage_index++)   begin
            plic_comparator #(
                .ID_BITWIDTH        (ID_BITWIDTH       ),
                .PRIORITY_BITWIDTH  (PRIORITY_BITWIDTH )
            ) comp_instance(
                .left_priority_i        ( priority_stages  [max_stage - comparator_stage][2*stage_index]     ),
                .right_priority_i       ( priority_stages  [max_stage - comparator_stage][2*stage_index + 1] ),
                .left_identifier_i      ( identifier_stages[max_stage - comparator_stage][2*stage_index]     ),
                .right_identifier_i     ( identifier_stages[max_stage - comparator_stage][2*stage_index + 1] ),
                .larger_priority_o      ( priority_stages  [max_stage - (comparator_stage-1)][stage_index]   ),
                .identifier_of_larger_o ( identifier_stages[max_stage - (comparator_stage-1)][stage_index]   )
            );
        end
    end

    assign largest_priority_o      = priority_stages  [max_stage+1][0];
    assign identifier_of_largest_o = identifier_stages[max_stage+1][0];
endmodule
