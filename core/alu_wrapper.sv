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

  alu #(
      .CVA6Cfg  (CVA6Cfg),
      .HasBranch(1'b1),
      .fu_data_t(fu_data_t)
  ) alu_i (
      .clk_i           (clk_i),
      .rst_ni          (rst_ni),
      .fu_data_i       (fu_data_i[0]),
      .fu_data_cpop_i  (fu_data_i[0]),
      .result_o        (result_o[0]),
      .alu_branch_res_o(alu_branch_res_o)
  );

  if (CVA6Cfg.SuperscalarEn) begin : gen_alu2

    fu_data_t fu_data_bypass;

    always_comb begin
      fu_data_bypass = fu_data_i[1];

      if (alu_bypass_i.rs1_from_rd) begin
        fu_data_bypass.operand_a = result_o[0];
      end
      if (alu_bypass_i.rs2_from_rd) begin
        fu_data_bypass.operand_b = result_o[0];
      end
    end

    alu #(
        .CVA6Cfg  (CVA6Cfg),
        .HasBranch(1'b0),
        .fu_data_t(fu_data_t)
    ) alu2_i (
        .clk_i           (clk_i),
        .rst_ni          (rst_ni),
        .fu_data_i       (fu_data_bypass),
        .fu_data_cpop_i  (fu_data_i[1]),
        .result_o        (result_o[1]),
        .alu_branch_res_o(  /* Unconnected */)
    );
  end

endmodule
