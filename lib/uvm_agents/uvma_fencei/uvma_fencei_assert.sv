// Copyright 2020 OpenHW Group
// Copyright 2020 Datum Technology Corporation
// Copyright 2020 Silicon Labs, Inc.
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     https://solderpad.org/licenses/
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

module uvma_fencei_assert
  import uvm_pkg::*;
  (
    input                    clk,
    input                    reset_n,

    input                    flush_req,
    input                    flush_ack
  );

  // ---------------------------------------------------------------------------
  // Local variables
  // ---------------------------------------------------------------------------
  string info_tag = "UVMA_FENCEI_ASSERT";

  // ---------------------------------------------------------------------------
  // Clocking blocks
  // ---------------------------------------------------------------------------

  // Single clock, single reset design, use default clocking
  default clocking @(posedge clk); endclocking
  default disable iff !(reset_n);

  // ---------------------------------------------------------------------------
  // Begin module code
  // ---------------------------------------------------------------------------

  // Fence request may not deassert until acknowledged
  property p_req_until_ack;
    flush_req ##0 !flush_ack |=> flush_req;
  endproperty : p_req_until_ack

  a_req_until_ack: assert property(p_req_until_ack)
  else
    `uvm_error(info_tag, "flush request not held until ack")

endmodule : uvma_fencei_assert
