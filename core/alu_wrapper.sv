// Copyright 2025 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Original authors: Gianmarco Ottavi,  University of Bologna
//                   Riccardo Tedeschi, University of Bologna
// Description: ALU(s) wrapper

module alu_wrapper
  import ariane_pkg::*;
#(
    parameter config_pkg::cva6_cfg_t CVA6Cfg = config_pkg::cva6_cfg_empty,
    parameter type fu_data_t = logic
) (
    input  logic                                               clk_i,
    input  logic                                               rst_ni,
    input  alu_bypass_t                                        alu_bypass_i,
    input  fu_data_t    [CVA6Cfg.NrALUs-1:0]                   fu_data_i,
    output logic        [CVA6Cfg.NrALUs-1:0][CVA6Cfg.XLEN-1:0] result_o,
    output logic                                               alu_branch_res_o
);

  logic [CVA6Cfg.NrALUs-1:0][CVA6Cfg.XLEN-1:0] result;

  alu #(
      .CVA6Cfg  (CVA6Cfg),
      .HasBranch(1'b1),
      .fu_data_t(fu_data_t)
  ) alu_i (
      .clk_i           (clk_i),
      .rst_ni          (rst_ni),
      .fu_data_i       (fu_data_i[0]),
      .result_o        (result[0]),
      .alu_branch_res_o(alu_branch_res_o)
  );

  if (CVA6Cfg.SuperscalarEn) begin : gen_alu2

    fu_data_t fu_data;

    always_comb begin
      fu_data = fu_data_i[1];

      if (alu_bypass_i.rs1_from_rd) begin
        fu_data.operand_a = result[0];
      end
      if (alu_bypass_i.rs2_from_rd) begin
        fu_data.operand_b = result[0];
      end
    end

    alu #(
        .CVA6Cfg  (CVA6Cfg),
        .HasBranch(1'b0),
        .fu_data_t(fu_data_t)
    ) alu2_i (
        .clk_i           (clk_i),
        .rst_ni          (rst_ni),
        .fu_data_i       (fu_data),
        .result_o        (result[1]),
        .alu_branch_res_o(  /* Unconnected */)
    );
  end

  if (CVA6Cfg.ALUBypass && CVA6Cfg.RVZCB) begin : gen_standalone_bitman_cpop

    logic [1:0][$clog2(CVA6Cfg.XLEN):0] cpop;
    logic [1:0][CVA6Cfg.XLEN-1:0] operand_a_bitmanip;

    always_comb begin
      operand_a_bitmanip[0] = fu_data_i[0].operand_a;
      operand_a_bitmanip[1] = fu_data_i[1].operand_a;

      if (CVA6Cfg.IS_XLEN64 && fu_data_i[0].operation == CPOPW) begin
        operand_a_bitmanip[0] = fu_data_i[0].operand_a[31:0];
      end
      if (CVA6Cfg.IS_XLEN64 && fu_data_i[1].operation == CPOPW) begin
        operand_a_bitmanip[1] = fu_data_i[1].operand_a[31:0];
      end
    end

    popcount #(
        .INPUT_WIDTH(riscv::XLEN)
    ) i_cpop_count_1 (
        .data_i    (operand_a_bitmanip[0]),
        .popcount_o(cpop[0])
    );

    popcount #(
        .INPUT_WIDTH(riscv::XLEN)
    ) i_cpop_count_2 (
        .data_i    (operand_a_bitmanip[1]),
        .popcount_o(cpop[1])
    );

    assign result_o[0] = (fu_data_i[0].operation inside {CPOP, CPOPW}) ? {{(riscv::XLEN - ($clog2(
        riscv::XLEN
    ) + 1)) {1'b0}}, cpop[0]} : result[0];
    assign result_o[1] = (fu_data_i[1].operation inside {CPOP, CPOPW}) ? {{(riscv::XLEN - ($clog2(
        riscv::XLEN
    ) + 1)) {1'b0}}, cpop[1]} : result[1];

  end else begin : gen_no_standalone_bitman_cpop
    assign result_o = result;
  end

endmodule
