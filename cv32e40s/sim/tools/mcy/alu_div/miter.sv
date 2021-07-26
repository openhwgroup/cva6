//
// Copyright 2020 OpenHW Group
// Copyright 2020 Symbiotic EDA
//
// Licensed under the Solderpad Hardware License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// https://solderpad.org/licenses/
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
//

module miter
(
    input  logic                    clk,
    input  logic                    rst_n,
    // input IF
    input  logic [31:0]      ref_OpA_DI,
    input  logic [31:0]      ref_OpB_DI,
    input  logic [5:0]       ref_OpBShift_DI,
    input  logic             ref_OpBIsZero_SI,
    //
    input  logic             ref_OpBSign_SI, // gate this to 0 in case of unsigned ops
    input  logic [1:0]       ref_OpCode_SI,  // 0: udiv, 2: urem, 1: div, 3: rem


    input  logic [31:0]      uut_OpA_DI,
    input  logic [31:0]      uut_OpB_DI,
    input  logic [5:0]       uut_OpBShift_DI,
    input  logic             uut_OpBIsZero_SI,
    //
    input  logic             uut_OpBSign_SI, // gate this to 0 in case of unsigned ops
    input  logic [1:0]       uut_OpCode_SI,  // 0: udiv, 2: urem, 1: div, 3: rem

    // handshake
    input  logic             in_valid,
    // output IF
    input  logic             out_ready
  );

logic ref_valid_out;
logic uut_valid_out;
logic [31:0] ref_result_div;
logic [31:0] uut_result_div;

  riscv_alu_div ref (
		.mutsel    (1'b 0),
    .Clk_CI    (clk),
    .Rst_RBI   (rst_n),

    // input IF
    .OpA_DI       (ref_OpA_DI),
    .OpB_DI       (ref_OpB_DI),
    .OpBShift_DI  (ref_OpBShift_DI),
    .OpBIsZero_SI (ref_OpBIsZero_SI),

    .OpBSign_SI   (ref_OpBSign_SI),
    .OpCode_SI    (ref_OpCode_SI),

    .Res_DO       (ref_result_div),

    // Hand-Shake
    .InVld_SI     (in_valid),
    .OutRdy_SI    (out_ready),
    .OutVld_SO    (ref_valid_out)
	);

	riscv_alu_div uut (
		.mutsel    (1'b 1),
    .Clk_CI    (clk),
    .Rst_RBI   (rst_n),

    // input IF
    .OpA_DI       (uut_OpA_DI),
    .OpB_DI       (uut_OpB_DI),
    .OpBShift_DI  (uut_OpBShift_DI),
    .OpBIsZero_SI (uut_OpBIsZero_SI),

    .OpBSign_SI   (uut_OpBSign_SI),
    .OpCode_SI    (uut_OpCode_SI),

    .Res_DO       (uut_result_div),

    // Hand-Shake
    .InVld_SI     (in_valid),
    .OutRdy_SI    (out_ready),
    .OutVld_SO    (uut_valid_out)
	);

logic init_cycle = 1'b1;
always @ (posedge clk) begin
  init_cycle = 1'b0;
end

always @(*) begin
  if (init_cycle) assume (!rst_n);
  if (rst_n) begin
    assume (out_ready); //too slow with backpressure
    // if (in_valid) begin
    // module depends on inputs not changing even if in_valid is false:
    // have to comment this out or it fails equivalence with itself
      assume (ref_OpA_DI == uut_OpA_DI);
      assume (ref_OpB_DI == uut_OpB_DI);
      assume (ref_OpBShift_DI == uut_OpBShift_DI);
      assume (ref_OpBIsZero_SI == uut_OpBIsZero_SI);
      assume (ref_OpBSign_SI == uut_OpBSign_SI);
      assume (ref_OpBSign_SI == uut_OpBSign_SI);
      assume (ref_OpCode_SI == uut_OpCode_SI);
    // end
    assert (ref_valid_out == uut_valid_out);
    if (ref_valid_out) begin
      assert (ref_result_div == uut_result_div);
    end
  end
end




endmodule
