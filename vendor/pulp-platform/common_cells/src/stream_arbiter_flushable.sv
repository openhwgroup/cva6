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
// arbitration scheme is fair round-robin tree, see `rr_arb_tree` for details.

module stream_arbiter_flushable #(
    parameter type      DATA_T = logic,   // Vivado requires a default value for type parameters.
    parameter integer   N_INP = -1,       // Synopsys DC requires a default value for parameters.
    parameter           ARBITER = "rr"    // "rr" or "prio"
) (
    input  logic              clk_i,
    input  logic              rst_ni,
    input  logic              flush_i,

    input  DATA_T [N_INP-1:0] inp_data_i,
    input  logic  [N_INP-1:0] inp_valid_i,
    output logic  [N_INP-1:0] inp_ready_o,

    output DATA_T             oup_data_o,
    output logic              oup_valid_o,
    input  logic              oup_ready_i
);

  if (ARBITER == "rr") begin : gen_rr_arb
    rr_arb_tree #(
      .NumIn      (N_INP),
      .DataType   (DATA_T),
      .ExtPrio    (1'b0),
      .AxiVldRdy  (1'b1),
      .LockIn     (1'b1)
    ) i_arbiter (
      .clk_i,
      .rst_ni,
      .flush_i,
      .rr_i   ('0),
      .req_i  (inp_valid_i),
      .gnt_o  (inp_ready_o),
      .data_i (inp_data_i),
      .gnt_i  (oup_ready_i),
      .req_o  (oup_valid_o),
      .data_o (oup_data_o),
      .idx_o  ()
    );

  end else if (ARBITER == "prio") begin : gen_prio_arb
    rr_arb_tree #(
      .NumIn      (N_INP),
      .DataType   (DATA_T),
      .ExtPrio    (1'b1),
      .AxiVldRdy  (1'b1),
      .LockIn     (1'b1)
    ) i_arbiter (
      .clk_i,
      .rst_ni,
      .flush_i,
      .rr_i   ('0),
      .req_i  (inp_valid_i),
      .gnt_o  (inp_ready_o),
      .data_i (inp_data_i),
      .gnt_i  (oup_ready_i),
      .req_o  (oup_valid_o),
      .data_o (oup_data_o),
      .idx_o  ()
    );

  end else begin : gen_arb_error
    // pragma translate_off
    $fatal(1, "Invalid value for parameter 'ARBITER'!");
    // pragma translate_on
  end

endmodule
