// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Stream filter: If `drop_i` is `1`, signal `ready` to the upstream regardless of the downstream,
// and do not propagate `valid` downstream.  Otherwise, connect upstream to downstream.
module stream_filter (
    input  logic valid_i,
    output logic ready_o,

    input  logic drop_i,

    output logic valid_o,
    input  logic ready_i
);

    assign valid_o = drop_i ? 1'b0 : valid_i;
    assign ready_o = drop_i ? 1'b1 : ready_i;

endmodule
