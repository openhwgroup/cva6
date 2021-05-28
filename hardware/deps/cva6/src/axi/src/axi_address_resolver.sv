// Copyright (c) 2014-2018 ETH Zurich, University of Bologna
//
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Fabian Schuiki <fschuiki@iis.ee.ethz.ch>

/// An address resolver.
///
/// Matches an address against a routing table and produces the index of the
/// matching slave.
module axi_address_resolver #(
  /// The address width.
  parameter int ADDR_WIDTH = -1,
  /// The number of slaves.
  parameter int NUM_SLAVE = -1,
  /// The number of rules.
  parameter int NUM_RULES = -1
)(
  AXI_ROUTING_RULES.xbar               rules       ,
  input  logic [ADDR_WIDTH-1:0]        addr_i      ,
  output logic [$clog2(NUM_SLAVE)-1:0] match_idx_o ,
  output logic                         match_ok_o
);

  logic [NUM_SLAVE-1:0][NUM_RULES-1:0] matched_rules;
  logic [NUM_SLAVE-1:0]                matched_slaves;

  for (genvar i = 0; i < NUM_SLAVE; i++) begin : g_slave
    // Match each of the rules.
    for (genvar j = 0; j < NUM_RULES; j++) begin : g_rule
      logic [ADDR_WIDTH-1:0] base, mask;
      logic enabled;
      assign base    = rules.rules[i][j].base;
      assign mask    = rules.rules[i][j].mask;
      assign enabled = rules.rules[i][j].enabled;
      // If the rules is disabled, it matches nothing.
      assign matched_rules[i][j] = (enabled && (addr_i & mask) == (base & mask));
    end

    // Check which slaves matched.
    assign matched_slaves[i] = |matched_rules[i];
  end

  // // If anything matched the address, output ok.
  assign match_ok_o = |matched_slaves;

  // Determine the index of the slave that matched.
  find_first_one #(.WIDTH(NUM_SLAVE), .FLIP(0)) i_lzc (
    .in_i        ( matched_slaves ),
    .first_one_o ( match_idx_o    ),
    .no_ones_o   (                )
  );

  // Ensure that we have a one-hot match. If we don't, this implies that the
  // rules in the routing table are not mututally exclusive.
  `ifndef SYNTHESIS
  always @(matched_rules, matched_slaves) begin
    assert ($onehot0(matched_rules)) else $error("%m: more than one rule matches 0x%0h: %0b", addr_i, matched_rules);
    assert ($onehot0(matched_slaves)) else $error("%m: more than one slave matches 0x%0h: %0b", addr_i, matched_slaves);
  end
  `endif

endmodule
