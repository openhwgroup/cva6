// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Author: Florian Zaruba <zarubaf@iis.ee.ethz.ch>, ETH Zurich
// Date: 16.03.2019
// Description: Priority arbiter with Lock in. Port 0 has priority over port 1, port 1 over port2
//              and so on. If the `LOCK_IN` feature is activated the arbitration decision is kept
//              when the `en_i` is low.

// Dependencies: relies on fast leading zero counter tree "onehot_to_bin" in common_cells
module prioarbiter #(
  parameter int unsigned NUM_REQ = 13,
  parameter int unsigned LOCK_IN = 0
) (
  input logic                         clk_i,
  input logic                         rst_ni,

  input logic                         flush_i, // clears the fsm and control signal registers
  input logic                         en_i,    // arbiter enable
  input logic [NUM_REQ-1:0]           req_i,   // request signals

  output logic [NUM_REQ-1:0]          ack_o,   // acknowledge signals
  output logic                        vld_o,   // request ack'ed
  output logic [$clog2(NUM_REQ)-1:0]  idx_o    // idx output
);

  localparam SEL_WIDTH = $clog2(NUM_REQ);

  logic [SEL_WIDTH-1:0] arb_sel_lock_d, arb_sel_lock_q;
  logic lock_d, lock_q;

  logic [$clog2(NUM_REQ)-1:0] idx;

  // shared
  assign vld_o = (|req_i) & en_i;
  assign idx_o  = (lock_q) ? arb_sel_lock_q : idx;

  // Arbiter
  // Port 0 has priority over all other ports
  assign ack_o[0] = (req_i[0]) ? en_i : 1'b0;
  // check that the priorities
  for (genvar i = 1; i < NUM_REQ; i++) begin : gen_arb_req_ports
      // for every subsequent port check the priorities of the previous port
      assign ack_o[i] = (req_i[i] & ~(|ack_o[i-1:0])) ? en_i : 1'b0;
  end

  onehot_to_bin #(
    .ONEHOT_WIDTH ( NUM_REQ )
  ) i_onehot_to_bin (
    .onehot ( ack_o ),
    .bin    ( idx   )
  );

  if (LOCK_IN) begin : gen_lock_in
    // latch decision in case we got at least one req and no acknowledge
    assign lock_d         = (|req_i) & ~en_i;
    assign arb_sel_lock_d = idx_o;
  end else begin
    // disable
    assign lock_d         = '0;
    assign arb_sel_lock_d = '0;
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin : p_regs
    if (!rst_ni) begin
      lock_q         <= 1'b0;
      arb_sel_lock_q <= '0;
    end else begin
      if (flush_i) begin
        lock_q         <= 1'b0;
        arb_sel_lock_q <= '0;
      end else begin
        lock_q         <= lock_d;
        arb_sel_lock_q <= arb_sel_lock_d;
      end
    end
  end

endmodule : prioarbiter



