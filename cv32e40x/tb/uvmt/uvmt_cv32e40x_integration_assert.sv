// Copyright 2021 OpenHW Group
// Copyright 2021 Silicon Labs, Inc.
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
//
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0


module uvmt_cv32e40x_integration_assert
  import uvm_pkg::*;
(
  input clk_i,
  input rst_ni,

  input        fetch_enable_i,
  input [31:0] dm_halt_addr_i
);

  default clocking cb @(posedge clk_i); endclocking
  string info_tag = "CV32E40X_INTEGRATION_ASSERT";

  logic fetch_enable_i_sticky;
  always @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      fetch_enable_i_sticky <= 0;
    end else if (fetch_enable_i) begin
      fetch_enable_i_sticky <= 1;
    end
  end

  // Check that "dm_halt_addr_i" is stable after "fetch_enable_i"
  a_dmhaltaddr_stable : assert property (
    fetch_enable_i_sticky
    |->
    $stable(dm_halt_addr_i)
    ) else `uvm_error(info_tag, "dm_halt_addr_i changed after fetch_enable_i");

  // Check that "dm_halt_addr_i" is word-aligned
  a_dmhaltaddr_aligned : assert property (
    dm_halt_addr_i[1:0] == 2'b00
    ) else `uvm_error(info_tag, "dm_halt_addr_i not word-aligned");

endmodule : uvmt_cv32e40x_integration_assert
