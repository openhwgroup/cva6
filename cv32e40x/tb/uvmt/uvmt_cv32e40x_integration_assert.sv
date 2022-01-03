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


// This module contains assertions relating to the "Core Integration" chapter
// of the user manual

module uvmt_cv32e40x_integration_assert
  import uvm_pkg::*;
(
  input clk_i,
  input rst_ni,

  input fetch_enable_i,

  input [31:0] boot_addr_i,
  input [31:0] dm_exception_addr_i,
  input [31:0] dm_halt_addr_i,
  input [31:0] mtvec_addr_i,
  input [31:0] nmi_addr_i
);

  default clocking @(posedge clk_i); endclocking
  default disable iff !rst_ni;
  string info_tag = "CV32E40X_INTEGRATION_ASSERT";

  logic fetch_enable_i_sticky;
  always @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      fetch_enable_i_sticky <= 0;
    end else if (fetch_enable_i) begin
      fetch_enable_i_sticky <= 1;
    end
  end


  // Check that addresses are stable after "fetch_enable_i"

  property p_stable_addr(addr);
    fetch_enable_i_sticky |-> $stable(addr);
  endproperty

  a_stable_bootaddr : assert property (p_stable_addr(boot_addr_i))
    else `uvm_error(info_tag, "boot_addr_i changed after fetch_enable_i");

  a_stable_dmexceptionaddr : assert property (p_stable_addr(dm_exception_addr_i))
    else `uvm_error(info_tag, "dm_exception_addr_i changed after fetch_enable_i");

  a_stable_dmhaltaddr : assert property (p_stable_addr(dm_halt_addr_i))
    else `uvm_error(info_tag, "dm_halt_addr_i changed after fetch_enable_i");

  a_stable_mtvecaddr : assert property (p_stable_addr(mtvec_addr_i))
    else `uvm_error(info_tag, "mtvec_addr_i changed after fetch_enable_i");

  a_stable_nmiaddr : assert property (p_stable_addr(nmi_addr_i))
    else `uvm_error(info_tag, "nmi_addr_i changed after fetch_enable_i");


  // Check that addresses are word-aligned

  property p_aligned_addr(addr);
    addr[1:0] == 2'b00;
  endproperty

  a_aligned_bootaddr : assert property (p_aligned_addr(boot_addr_i))
    else `uvm_error(info_tag, "boot_addr_i not word-aligned");

  a_aligned_dmexceptionaddr : assert property (p_aligned_addr(dm_exception_addr_i))
    else `uvm_error(info_tag, "dm_exception_addr_i not word-aligned");

  a_aligned_dmhaltaddr : assert property (p_aligned_addr(dm_halt_addr_i))
    else `uvm_error(info_tag, "dm_halt_addr_i not word-aligned");

  //a_aligned_mtvecaddr is not required by the user manual as per now

  a_aligned_nmiaddr : assert property (p_aligned_addr(nmi_addr_i))
    else `uvm_error(info_tag, "nmi_addr_i not word-aligned");

endmodule : uvmt_cv32e40x_integration_assert
