// Copyright 2020 ETH Zurich and University of Bologna.
//
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Author: Florian Zaruba <zarubaf@iis.ee.ethz.ch>

/// A stream interface with custom payload of type `payload_t`.
/// Handshaking rules as defined in the AXI standard.
interface STREAM_DV #(
  /// Custom payload type.
  parameter type payload_t = logic
)(
  /// Interface clock.
  input logic clk_i
);
  payload_t data;
  logic valid;
  logic ready;

  modport In (
    output ready,
    input valid, data
  );

  modport Out (
    output valid, data,
    input ready
  );

  /// Passive modport for scoreboard and monitors.
  modport Passive (
    input valid, ready, data
  );

  // Make sure that the handshake and payload is stable
  // pragma translate_off
  `ifndef VERILATOR
  assert property (@(posedge clk_i) (valid && !ready |=> $stable(data)));
  assert property (@(posedge clk_i) (valid && !ready |=> valid));
  `endif
  // pragma translate_on
endinterface
