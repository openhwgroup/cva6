// Copyright 2019 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// TODO(zarubaf): This is not really a tech cell - move it to common cells

module pulp_clock_gating_async #(
  parameter int unsigned STAGES = 2
) (
  input  logic clk_i,
  input  logic rstn_i,
  input  logic en_async_i,
  output logic en_ack_o,
  input  logic test_en_i,
  output logic clk_o
);

  logic [STAGES-1:0] r_reg;

  assign en_ack_o =  r_reg[STAGES-1];

  // synchronize enable signal
  always_ff @ (posedge clk_i or negedge rstn_i) begin
    if (!rstn_i) begin
      r_reg <= '0;
    end else begin
      r_reg <= {r_reg[STAGES-2:0], en_async_i};
    end
  end

  pulp_clock_gating i_clk_gate (
    .clk_i,
    .en_i ( r_reg[STAGES-1] ),
    .test_en_i,
    .clk_o
  );

endmodule