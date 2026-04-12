// Copyright 2024 OpenHW Group
// Solderpad Hardware License, Version 2.1
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
//
// SVA assertions for CVA6 ALU module
// Contributor: Angad Singh <s.angad2.2004@gmail.com>

module cva6_alu_sva #(
  parameter int unsigned XLEN = 64
) (
  input logic clk_i,
  input logic rst_ni,
  input logic [XLEN-1:0] result_o,
  input logic            alu_branch_res_o,
  input logic            adder_z_flag,
  input logic            less
);

  // Rule 1: SLTS/SLTU result must only be 0 or 1
  property sltu_result_one_bit;
    @(posedge clk_i) disable iff (!rst_ni)
    (result_o == '0) || (result_o == {{XLEN-1{1'b0}}, 1'b1});
  endproperty

  // Rule 2: Zero flag must be HIGH only when result is zero
  property zero_flag_correct;
    @(posedge clk_i) disable iff (!rst_ni)
    adder_z_flag |-> (result_o == '0);
  endproperty
  assert property (zero_flag_correct)
    else $error("FAIL: zero flag HIGH but result is not zero");

  // Rule 3: less flag must be 0 or 1 only
  property less_flag_binary;
    @(posedge clk_i) disable iff (!rst_ni)
    (less == 1'b0) || (less == 1'b1);
  endproperty
  assert property (less_flag_binary)
    else $error("FAIL: less flag is not binary");

  // Rule 4: branch result must be binary
  property branch_res_binary;
    @(posedge clk_i) disable iff (!rst_ni)
    (alu_branch_res_o == 1'b0) || (alu_branch_res_o == 1'b1);
  endproperty
  assert property (branch_res_binary)
    else $error("FAIL: branch result is not binary");

endmodule
