// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Stream arbiter: Arbitrates a parametrizable number of input streams (i.e., valid-ready
// handshaking with dependency rules as in AXI4) to a single output stream.  Once `oup_valid_o` is
// asserted, `oup_data_o` remains invariant until the output handshake has occurred.  The
// arbitration scheme is round-robin with "look ahead", see the `rrarbiter` for details.

module stream_arbiter #(
    parameter type      DATA_T = logic,   // Vivado requires a default value for type parameters.
    parameter integer   N_INP = -1,       // Synopsys DC requires a default value for parameters.
    parameter           ARBITER = "rr"    // "rr" or "prio"
) (
    input  logic              clk_i,
    input  logic              rst_ni,

    input  DATA_T [N_INP-1:0] inp_data_i,
    input  logic  [N_INP-1:0] inp_valid_i,
    output logic  [N_INP-1:0] inp_ready_o,

    output DATA_T             oup_data_o,
    output logic              oup_valid_o,
    input  logic              oup_ready_i
);

  stream_arbiter_flushable #(
    .DATA_T   (DATA_T),
    .N_INP    (N_INP),
    .ARBITER  (ARBITER)
  ) i_arb (
    .clk_i        (clk_i),
    .rst_ni       (rst_ni),
    .flush_i      (1'b0),
    .inp_data_i   (inp_data_i),
    .inp_valid_i  (inp_valid_i),
    .inp_ready_o  (inp_ready_o),
    .oup_data_o   (oup_data_o),
    .oup_valid_o  (oup_valid_o),
    .oup_ready_i  (oup_ready_i)
  );

endmodule
