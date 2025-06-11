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
// Author: Michael Schaffner <schaffner@iis.ee.ethz.ch>, ETH Zurich
// Date: 16.08.2018
// Description: Fair round robin arbiter with lock feature.
//
// The rrarbiter employs fair round robin arbitration - i.e. the priorities
// rotate each cycle.
//
// The lock-in feature prevents the arbiter from changing the arbitration
// decision when the arbiter is disabled. I.e., the index of the first request
// that wins the arbitration will be locked until en_i is asserted again.
//
// Dependencies: relies on rr_arb_tree from common_cells.

module rrarbiter #(
  parameter int unsigned NUM_REQ   = 64,
  parameter bit          LOCK_IN   = 1'b0
) (
  input logic                         clk_i,
  input logic                         rst_ni,

  input logic                         flush_i, // clears arbiter state
  input logic                         en_i,    // arbiter enable
  input logic [NUM_REQ-1:0]           req_i,   // request signals

  output logic [NUM_REQ-1:0]          ack_o,   // acknowledge signals
  output logic                        vld_o,   // request ack'ed
  output logic [$clog2(NUM_REQ)-1:0]  idx_o    // idx output
);

  logic req;
  assign vld_o = (|req_i) & en_i;

  rr_arb_tree #(
    .NumIn     ( NUM_REQ ),
    .DataWidth ( 1       ),
    .LockIn    ( LOCK_IN ))
  i_rr_arb_tree (
    .clk_i   ( clk_i      ),
    .rst_ni  ( rst_ni     ),
    .flush_i ( flush_i    ),
    .rr_i    ( '0         ),
    .req_i   ( req_i      ),
    .gnt_o   ( ack_o      ),
    .data_i  ( '0         ),
    .gnt_i   ( en_i & req ),
    .req_o   ( req        ),
    .data_o  (            ),
    .idx_o   ( idx_o      )
  );

endmodule : rrarbiter
