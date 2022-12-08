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
//
// Author: Florian Zaruba <zarubaf@iis.ee.ethz.ch>

/// 4-phase handshake between isochronous clock domains
/// (i.e., clock domains which operate on an integer multiple of each other).
///
/// The internals of this modules are similar to a clock-domain crossing except that
/// they do not synchronize the handshake signals as signals can not become metastable (covered by STA).
/// The upstream circuit will only handshake iff the downstream circuit handshaked.
///
/// ## Optionally Passing of Data
///
/// If the passing of data is necessary this should be done out side the module, for example:
/// ```
/// `FFLNR(dst_data_o, src_data_i, (src_valid_i && src_ready_o), src_clk_i)
/// ```
///
/// This module differs to `isochronous_spill_register` that it doesn't buffer any data
/// and only toggles the source handshake once the destination handshake has been toggled.
///
/// # Restrictions
///
/// Source and destination clock domains must be an integer multiple of each other and
/// all timing-paths need to be covered by STA. For example a recommended SDC would be:
///
/// `create_generated_clock dst_clk_i -name dst_clk  -source src_clk_i -divide_by 2
///
/// There are _no_ restrictions on which clock domain should be the faster, any integer
/// ratio will work.

`include "common_cells/registers.svh"

module isochronous_4phase_handshake (
  input  logic src_clk_i,
  input  logic src_rst_ni,
  input  logic src_valid_i,
  output logic src_ready_o,
  input  logic dst_clk_i,
  input  logic dst_rst_ni,
  output logic dst_valid_o,
  input  logic dst_ready_i
);

  logic src_req_q, src_ack_q;
  logic dst_req_q, dst_ack_q;

  // source is making a request
  `FFLARN(src_req_q, ~src_req_q, (src_valid_i && src_ready_o), 1'b0, src_clk_i, src_rst_ni)
  // "synchronize" the acknowledge into the sending clock-domain
  `FFARN(src_ack_q, dst_ack_q, 1'b0, src_clk_i, src_rst_ni)
  // source is ready if the request wasn't yet acknowledged
  assign src_ready_o = (src_req_q == src_ack_q);

  // down-stream circuit is acknowledging the handshake
  `FFLARN(dst_ack_q, ~dst_ack_q, (dst_valid_o && dst_ready_i), 1'b0, dst_clk_i, dst_rst_ni)
  // "synchronize" the request into the receiving clock domain
  `FFARN(dst_req_q, src_req_q, 1'b0, dst_clk_i, dst_rst_ni)
  // destination is valid if we didn't yet get acknowledge
  assign dst_valid_o = (dst_req_q != dst_ack_q);

 // pragma translate_off
 // stability guarantees
  `ifndef VERILATOR
  assert property (@(posedge src_clk_i) disable iff (src_rst_ni)
    (src_valid_i && !src_ready_o |=> $stable(src_valid_i))) else $error("src_valid_i is unstable");
  assert property (@(posedge dst_clk_i) disable iff (dst_rst_ni)
    (dst_valid_o && !dst_ready_i |=> $stable(dst_valid_o))) else $error("dst_valid_o is unstable");
  `endif
  // pragma translate_on

endmodule
