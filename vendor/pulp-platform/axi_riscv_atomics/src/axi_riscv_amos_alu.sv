// Copyright (c) 2018 ETH Zurich, University of Bologna
//
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// AXI RISC-V Atomic Operations (AMOs) ALU
module axi_riscv_amos_alu # (
    parameter int unsigned DATA_WIDTH = 0
) (
    input  logic [5:0]              amo_op_i,
    input  logic [DATA_WIDTH-1:0]   amo_operand_a_i,
    input  logic [DATA_WIDTH-1:0]   amo_operand_b_i,
    output logic [DATA_WIDTH-1:0]   amo_result_o
);

    logic [DATA_WIDTH:0] adder_sum;
    logic [DATA_WIDTH:0] adder_operand_a, adder_operand_b;

    assign adder_sum = adder_operand_a + adder_operand_b;

    always_comb begin

        adder_operand_a = $signed(amo_operand_a_i);
        adder_operand_b = $signed(amo_operand_b_i);

        amo_result_o = amo_operand_a_i;

        if (amo_op_i == axi_pkg::ATOP_ATOMICSWAP) begin
            // Swap operation
            amo_result_o = amo_operand_b_i;
        end else if ((amo_op_i[5:4] == axi_pkg::ATOP_ATOMICLOAD) | (amo_op_i[5:4] == axi_pkg::ATOP_ATOMICSTORE)) begin
            // Load operation
            unique case (amo_op_i[2:0])
                // the default is to output operand_a
                axi_pkg::ATOP_ADD: amo_result_o = adder_sum[DATA_WIDTH-1:0];
                axi_pkg::ATOP_CLR: amo_result_o = amo_operand_a_i & (~amo_operand_b_i);
                axi_pkg::ATOP_SET: amo_result_o = amo_operand_a_i | amo_operand_b_i;
                axi_pkg::ATOP_EOR: amo_result_o = amo_operand_a_i ^ amo_operand_b_i;
                axi_pkg::ATOP_SMAX: begin
                    adder_operand_b = -$signed(amo_operand_b_i);
                    amo_result_o = adder_sum[DATA_WIDTH] ? amo_operand_b_i : amo_operand_a_i;
                end
                axi_pkg::ATOP_SMIN: begin
                    adder_operand_b = -$signed(amo_operand_b_i);
                    amo_result_o = adder_sum[DATA_WIDTH] ? amo_operand_a_i : amo_operand_b_i;
                end
                axi_pkg::ATOP_UMAX: begin
                    adder_operand_a = $unsigned(amo_operand_a_i);
                    adder_operand_b = -$unsigned(amo_operand_b_i);
                    amo_result_o = adder_sum[DATA_WIDTH] ? amo_operand_b_i : amo_operand_a_i;
                end
                axi_pkg::ATOP_UMIN: begin
                    adder_operand_a = $unsigned(amo_operand_a_i);
                    adder_operand_b = -$unsigned(amo_operand_b_i);
                    amo_result_o = adder_sum[DATA_WIDTH] ? amo_operand_a_i : amo_operand_b_i;
                end
                default: amo_result_o = '0;
            endcase
        end
    end

    // Validate parameters.
// pragma translate_off
`ifndef VERILATOR
    initial begin: validate_params
        assert (DATA_WIDTH > 0)
            else $fatal(1, "DATA_WIDTH must be greater than 0!");
    end
`endif
// pragma translate_on

endmodule
