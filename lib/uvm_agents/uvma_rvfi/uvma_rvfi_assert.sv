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

module uvma_rvfi_assert
  import uvm_pkg::*;
  #(
    parameter int ADDR_WIDTH=32,
    parameter int DATA_WIDTH=32
  )
  (
    input                    clk,
    input                    reset_n,

    input                    req,
    input                    gnt,
    input [ADDR_WIDTH-1:0]   addr,
    input                    we,
    input [DATA_WIDTH/8-1:0] be,
    input [DATA_WIDTH-1:0]   wdata,
    input [DATA_WIDTH-1:0]   rdata,
    input                    rvalid,
    input                    rready
  );

  // ---------------------------------------------------------------------------
  // Local variables
  // ---------------------------------------------------------------------------
  string info_tag = "CV32E40P_RVFI_ASSERT";

  // ---------------------------------------------------------------------------
  // Clocking blocks
  // ---------------------------------------------------------------------------

  // Single clock, single reset design, use default clocking
  default clocking @(posedge clk); endclocking
  default disable iff !(reset_n);

  // ---------------------------------------------------------------------------
  // Begin module code
  // ---------------------------------------------------------------------------

  // R-3.1.1 : Address phase signals stable during address phase
  property p_addr_signal_stable(sig);
    req ##0 !gnt |=> $stable(sig);
  endproperty : p_addr_signal_stable

  a_addr_stable: assert property(p_addr_signal_stable(addr))
  else 
    `uvm_error(info_tag, "addr signal not stable in address phase")

  a_we_stable: assert property(p_addr_signal_stable(we))
  else 
    `uvm_error(info_tag, "we signal not stable in address phase")

  a_wdata_stable: assert property(p_addr_signal_stable(wdata))
  else 
    `uvm_error(info_tag, "wdata signal not stable in address phase")

  a_be_stable: assert property(p_addr_signal_stable(be))
  else 
    `uvm_error(info_tag, "be signal not stable in address phase")

  // R-3.1.2 : Req may not deassewrt until the gnt is asserted
  property p_req_until_gnt;
    req ##0 !gnt |=> req;
  endproperty : p_req_until_gnt
  a_req_until_gnt : assert property(p_req_until_gnt)
  else
    `uvm_error(info_tag, "req may not deassert until gnt asserted")

  // R-7 At least one byte enable must be set
  property p_be_not_zero;
    req |-> be != 0;
  endproperty : p_be_not_zero
  a_be_not_zero : assert property(p_be_not_zero)
  else
    `uvm_error(info_tag, "be was zero during an address cycle")

  // R-7 All ones must be contiguous in writes
  reg[3:0] contiguous_be[] = {
    4'b0001,
    4'b0011,
    4'b0111,
    4'b1111,
    4'b0010,
    4'b0110,
    4'b1110,
    4'b0100,
    4'b1100,
    4'b1000
  };
  bit be_inside_contiguous_be;
  always_comb begin
    be_inside_contiguous_be = be inside {contiguous_be};
  end
  property p_be_contiguous;
    req |-> be_inside_contiguous_be;
  endproperty : p_be_contiguous
  a_be_contiguous : assert property(p_be_contiguous)
  else
    `uvm_error(info_tag, $sformatf("be of 0x%0x was not contiguous", $sampled(be)));

  // R-8 Data address LSBs must be consistent with byte enables on writes
  function bit [1:0] get_addr_lsb(bit[3:0] be);
    casex (be)
      4'b???1: return 0;
      4'b??10: return 1;
      4'b?100: return 2;
      4'b1000: return 3;
    endcase
  endfunction : get_addr_lsb

  property p_addr_be_consistent;
    req |-> addr[1:0] == get_addr_lsb(be);
  endproperty : p_addr_be_consistent
  a_addr_be_consistent: assert property(p_addr_be_consistent)
  else
    `uvm_error(info_tag, $sformatf("be of 0x%01x not consistent with addr 0x%08x", $sampled(be), $sampled(addr)));

endmodule : uvma_rvfi_assert
