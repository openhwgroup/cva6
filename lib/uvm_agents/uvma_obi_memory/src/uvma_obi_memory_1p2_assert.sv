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

module uvma_obi_memory_1p2_assert
  // Known reuse of port list from uvma_obi_memory_assert
  //@DVT_LINTER_WAIVER_START "SR20211012_1" disable SVTB.33.1.0
  import uvm_pkg::*;
  #(
    parameter int unsigned ADDR_WIDTH  = 32,
    parameter int unsigned DATA_WIDTH  = 32,
    parameter int unsigned AUSER_WIDTH = 0,
    parameter int unsigned WUSER_WIDTH = 0,
    parameter int unsigned RUSER_WIDTH = 0,
    parameter int unsigned ID_WIDTH    = 0,
    parameter int unsigned ACHK_WIDTH  = 0,
    parameter int unsigned RCHK_WIDTH  = 0
  )

  (
    input                    clk,
    input                    reset_n,

    // A bus 1P1
    input                    req,
    input                    gnt,
    input [ADDR_WIDTH-1:0]   addr,
    input                    we,
    input [DATA_WIDTH/8-1:0] be,
    input [DATA_WIDTH-1:0]   wdata,

    // A bus 1P2
    input [((AUSER_WIDTH == 0) ? 0 : AUSER_WIDTH - 1) : 0] auser,
    input [((WUSER_WIDTH == 0) ? 0 : WUSER_WIDTH - 1) : 0] wuser,
    input [((ID_WIDTH == 0) ? 0 : ID_WIDTH - 1) : 0]       aid,
    input [5:0]                                            atop,
    input [1:0]                                            memtype,
    input [2:0]                                            prot,
    input                                                  reqpar,
    input                                                  gntpar,
    input [((ACHK_WIDTH == 0) ? 0 : ACHK_WIDTH - 1) : 0]   achk,

    // R bus 1P1
    input [DATA_WIDTH-1:0]   rdata,
    input                    rvalid,

    // R bus 1P2
    input                                                  rready,
    input                                                  err,
    input [((RUSER_WIDTH == 0) ? 0 : RUSER_WIDTH - 1) : 0] ruser,
    input [((ID_WIDTH == 0) ? 0 : ID_WIDTH - 1) : 0]       rid,
    input                                                  exokay,
    input                                                  rvalidpar,
    input                                                  rreadypar,
    input [((RCHK_WIDTH == 0) ? 0 : RCHK_WIDTH - 1) : 0]   rchk
  );

  // ---------------------------------------------------------------------------
  // Local parameters
  // ---------------------------------------------------------------------------
  localparam EFF_ID_WIDTH = ID_WIDTH == 0 ? 1 : ID_WIDTH;
  localparam ADDR_ALIGN_MASK = (1 << $clog2(DATA_WIDTH)) - 1;

  localparam ATOP_LR = {1'b1, 4'h2};
  localparam ATOP_SC = {1'b1, 4'h3};

  //@DVT_LINTER_WAIVER_END "SR20211012_1"

  // ---------------------------------------------------------------------------
  // Typedefs
  // ---------------------------------------------------------------------------
  typedef struct {
    bit [4:0]              atop;
    bit [EFF_ID_WIDTH-1:0] aid;
  } aid_q_t;

  // ---------------------------------------------------------------------------
  // Local variables
  // ---------------------------------------------------------------------------
  string info_tag = "OBIMEM1P2ASRT";

  reg atomic_in_flight;

  wire valid_a_phase;
  wire valid_r_phase;

  aid_q_t aid_q[3:0];
  bit [4:0] aid_wptr;
  bit [4:0] aid_rptr;

  bit atomic_trn_active;

  // ---------------------------------------------------------------------------
  // Clocking blocks
  // ---------------------------------------------------------------------------

  // Single clock, single reset design, use default clocking
  default clocking @(posedge clk); endclocking
  default disable iff !(reset_n);

  // ---------------------------------------------------------------------------
  // Begin module code
  // ---------------------------------------------------------------------------

  // Modeling logic and common decoding
  assign valid_a_phase = req && gnt;
  assign valid_r_phase = rvalid && rready;

  // R-3.1.1 : A phase signals stable during address phase
  property p_addr_signal_stable(sig);
    req ##0 !gnt |=> $stable(sig);
  endproperty : p_addr_signal_stable

  a_auser_stable: assert property(p_addr_signal_stable(auser))
  else
    `uvm_error(info_tag, "auser signal not stable in address phase")

  a_wuser_stable: assert property(p_addr_signal_stable(wuser))
  else
    `uvm_error(info_tag, "wuser signal not stable in address phase")

  a_aid_stable: assert property(p_addr_signal_stable(aid))
  else
    `uvm_error(info_tag, "aid signal not stable in address phase")

  a_atop_stable: assert property(p_addr_signal_stable(atop))
  else
    `uvm_error(info_tag, "atop signal not stable in address phase")

  a_memtype_stable: assert property(p_addr_signal_stable(memtype))
  else
    `uvm_error(info_tag, "memtype signal not stable in address phase")

  a_prot_stable: assert property(p_addr_signal_stable(prot))
  else
    `uvm_error(info_tag, "prot signal not stable in address phase")

  a_achk_stable: assert property(p_addr_signal_stable(achk))
  else
    `uvm_error(info_tag, "achk signal not stable in address phase")

  // R-3.1.2 : Req may not deassewrt until the gnt is asserted
  property p_req_until_gnt;
    req ##0 !gnt |=> req;
  endproperty : p_req_until_gnt
  a_req_until_gnt : assert property(p_req_until_gnt)
  else
    `uvm_error(info_tag, "req may not deassert until gnt asserted")

  // R-4.1.1 : R phase signals stable during respnose phase
  property p_r_signal_stable(sig);
    rvalid ##0 !rready |=> $stable(sig);
  endproperty : p_r_signal_stable

  a_rdata_stable: assert property(p_r_signal_stable(rdata))
  else
    `uvm_error(info_tag, "rdata signal not stable in response phase")

  a_err_stable: assert property(p_r_signal_stable(err))
  else
    `uvm_error(info_tag, "err signal not stable in response phase")

  a_ruser_stable: assert property(p_r_signal_stable(ruser))
  else
    `uvm_error(info_tag, "ruser signal not stable in response phase")

  a_rid_stable: assert property(p_r_signal_stable(rid))
  else
    `uvm_error(info_tag, "rid signal not stable in response phase")

  a_exokay_stable: assert property(p_r_signal_stable(exokay))
  else
    `uvm_error(info_tag, "exokay signal not stable in response phase")

  a_rchk_stable: assert property(p_r_signal_stable(rchk))
  else
    `uvm_error(info_tag, "rchk signal not stable in response phase")

  // R-4.1.2 : Req may not deassewrt until the gnt is asserted
  property p_rvalid_until_rready;
    rvalid ##0 !rready |=> rvalid;
  endproperty : p_rvalid_until_rready
  a_rvalid_until_rready : assert property(p_rvalid_until_rready)
  else
    `uvm_error(info_tag, "rvalid may not deassert until rready asserted")

  // These next 2 are not strictly a functional requirement, but the testbench should simulate this
  // Therefore these are coded as a set of cover properties

  // R-4.2.1 : master shall be allowed to de-assert (retract) rready at any time even if rvalid is deasserted
  property p_rready_assert_no_rvalid;
    !rvalid ##0 !rready ##1 !rvalid ##0 rready;
  endproperty : p_rready_assert_no_rvalid
  c_rready_assert_no_rvalid : cover property(p_rready_assert_no_rvalid);

  // R-4.2.2 : master shall be allowed to de-assert (retract) rready at any time even if rvalid is deasserted
  property p_rready_deassert_no_rvalid;
    !rvalid ##0 rready ##1 !rvalid ##0 !rready;
  endproperty : p_rready_deassert_no_rvalid
  c_rready_deassert_no_rvalid : cover property(p_rready_deassert_no_rvalid);

  // R-9 For each OBI transactions the slave shall mirror back the value recieved on aid via rid
  always @(posedge clk or negedge reset_n) begin
    if (!reset_n)  begin
      aid_wptr <= '0;
      aid_rptr <= '0;
      atomic_in_flight <= '0;
    end
    else begin
      if (valid_a_phase) begin
        aid_q[aid_wptr] <= '{atop, aid};
        aid_wptr <= aid_wptr + 1;
        if (atop) atomic_in_flight <= 1'b1;
      end
      if (valid_r_phase) begin
        if (aid_q[aid_rptr].atop) atomic_in_flight <= 1'b0;
        aid_rptr <= aid_rptr + 1;
      end
    end
  end

  property p_rid_follows_aid;
    rvalid |-> rid == aid_q[aid_rptr].aid;
  endproperty
  a_rid_follows_aid: assert property(p_rid_follows_aid)
  else
    `uvm_error(info_tag, $sformatf("rid of 0x%0x does not follow expected aid of 0x%0x", rid, aid_q[aid_rptr].aid))

  // R-10.4 An atomic transaction must use a naturally aligned address
  property p_atomic_addr_aligned;
    req ##0 atop |-> addr & (ADDR_ALIGN_MASK) == 0;
  endproperty
  a_atomic_addr_aligned : assert property(p_atomic_addr_aligned)
  else
    `uvm_error(info_tag, $sformatf("Atomic transaction does not use aligned address: 0x%08x", addr))

  // R-11 If an exclusive transaction is executing another may not be emitted
  property p_one_atomic_trn;
    req |-> !atomic_in_flight;
  endproperty : p_one_atomic_trn
  a_one_atomic_trn: assert property(p_one_atomic_trn)
  else
    `uvm_error(info_tag, "Detected multiple atomic transactions active at same time");

  // R-12.3 EXOKAY may only be asserted in response to transactions that are LR or SC
  property p_exokay_lr_sc;
    rvalid && exokay |-> aid_q[aid_rptr].atop inside {ATOP_LR, ATOP_SC};
  endproperty : p_exokay_lr_sc
  a_exokay_lr_sc: assert property(p_exokay_lr_sc)
  else
    `uvm_error(info_tag, "EXOKAY may only asserted in response to an LR or SC transaction (signaled via atop)")

endmodule : uvma_obi_memory_1p2_assert
