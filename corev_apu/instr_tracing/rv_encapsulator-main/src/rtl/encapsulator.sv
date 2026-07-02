// Copyright 2025 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
// SPDX-License-Identifier: SHL-0.51

// Author:  Umberto Laghi
// Contact: umberto.laghi2@unibo.it
// Github:  @ubolakes

/* ENCAPSULATOR */
/*
this module generates the header and payload necessary based on the protocol used
*/

module encapsulator (
    // inputs
    input logic                                 clk_i,
    input logic                                 valid_i,
    input logic [encap_pkg::P_LEN-1:0]          packet_length_i,
    input logic [encap_pkg::FLOW_LEN-1:0]       flow_i,
    input logic                                 timestamp_present_i,
    //input logic                                 srcid_i,
    input logic [encap_pkg::T_LEN-1:0]          timestamp_i,
    //input logic [encap_pkg::TYPE_LEN-1:0]       type_i,
    input logic [encap_pkg::PAYLOAD_LEN-1:0]    trace_payload_i,

    // outputs
    output logic                                valid_o,
    output encap_pkg::encap_fifo_entry_s        encap_fifo_entry_o
);
  // pragma translate_off
  int f;
  initial begin
    f = $fopen("encaps.traces", "w");
  end
  final $fclose(f);
  // pragma translate_on

always_comb begin
    // initialization
    valid_o = '0;
    encap_fifo_entry_o = '0;

    // assignments
    if (valid_i) begin
        valid_o = '1;
        // header
        encap_fifo_entry_o.header.length = packet_length_i;
        encap_fifo_entry_o.header.flow = flow_i;
        encap_fifo_entry_o.header.extend = timestamp_present_i;
        // srcID
        //encap_fifo_entry_o.srcid = srcid_i;
        // timestamp
        encap_fifo_entry_o.timestamp = timestamp_i;
        // payload
        encap_fifo_entry_o.payload.trace_payload = trace_payload_i;
    end
end
// pragma translate_off
always_ff @(posedge clk_i) begin
    if (valid_o) begin
        $fwrite(
        f,
        "%h\n",encap_fifo_entry_o);
    end
end 
// pragma translate_on

endmodule