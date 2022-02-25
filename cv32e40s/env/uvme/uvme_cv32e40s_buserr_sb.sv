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


`ifndef __UVME_CV32E40S_BUSERR_SB_SV__
`define __UVME_CV32E40S_BUSERR_SB_SV__


`uvm_analysis_imp_decl(_obid)  // D-side OBI
`uvm_analysis_imp_decl(_obii)  // I-side OBI
`uvm_analysis_imp_decl(_rvfi)


// Class: uvme_cv32e40s_buserr_sb_c
// A scoreboard to check that OBI "err" bus faults arrive at the RVFI.
// For I-side "err"s, the main mode of checking is to store every err-flagged
//   OBI transaction in a queue, and then compare the PC addresses of RVFI
//   retires to see that they have the expected impact.
// For D-side "err"s, the main mode of checking is to watch for the first "err"
//   (in, potentially, a series of "err"s) and demand that no more than two
//   RVFI retires (non-debug/step) happen before we must enter the NMI handler.
// There are also a couple of other checks to see if all counts are as expected.
class uvme_cv32e40s_buserr_sb_c extends uvm_scoreboard;

  string info_tag = "BUSERRSB";

  uvm_analysis_imp_obid#(uvma_obi_memory_mon_trn_c, uvme_cv32e40s_buserr_sb_c)  obid;
  uvm_analysis_imp_obii#(uvma_obi_memory_mon_trn_c, uvme_cv32e40s_buserr_sb_c)  obii;
  uvm_analysis_imp_rvfi#(uvma_rvfi_instr_seq_item_c#(ILEN,XLEN), uvme_cv32e40s_buserr_sb_c)  rvfi;

  // OBI D-side variables:
  int cnt_obid_trn;      // Count of all obi d-side transactions
  int cnt_obid_err;      // Count of all d-side "err" transactions
  int cnt_obid_firsterr; // Count of all first d-side "err", in case of multiple "err" before handler "taken"
  // OBI I-side variables:
  int cnt_obii_trn;  // Count of all obi i-side transactions
  int cnt_obii_err;  // Count of all i-side "err" transactions
  // RVFI variables:
  int cnt_rvfi_trn;         // Count of all rvfi transactions
  int cnt_rvfi_nmihandl;    // Count of all nmi handler entries
  int cnt_rvfi_ifaulthandl; // Count of all instr bus fault handler entries
  int cnt_rvfi_errmatch;    // Count of all retires matched with expected I-side "err"
  int cnt_rvfi_errmatch_debug; // Count of all errmatch that happens under debug
  // Expectations variables:
  bit                       pending_nmi;       // Whether nmi happened and handler is expected
  int                       late_retires;      // Number of non-debug/step/handler retires since "pending_nmi"
  uvma_obi_memory_mon_trn_c obii_err_queue[$]; // All I-side OBI trns last seen with "err"

  `uvm_component_utils(uvme_cv32e40s_buserr_sb_c)

  extern function              new(string name="uvme_cv32e40s_buserr_sb", uvm_component parent=null);
  extern virtual function void write_obid(uvma_obi_memory_mon_trn_c trn);
  extern virtual function void write_obii(uvma_obi_memory_mon_trn_c trn);
  extern virtual function void write_rvfi(uvma_rvfi_instr_seq_item_c#(ILEN,XLEN) trn);
  extern virtual function void build_phase(uvm_phase phase);
  extern virtual function void check_phase(uvm_phase phase);
  extern function bit          should_instr_err(uvma_rvfi_instr_seq_item_c#(ILEN,XLEN) rvfi_trn);
  extern function void         remove_from_err_queue(uvma_obi_memory_mon_trn_c  trn);
  extern function void         add_to_err_queue(uvma_obi_memory_mon_trn_c  trn);

endclass : uvme_cv32e40s_buserr_sb_c


function uvme_cv32e40s_buserr_sb_c::new(string name="uvme_cv32e40s_buserr_sb", uvm_component parent=null);

  super.new(name, parent);

endfunction : new


function void uvme_cv32e40s_buserr_sb_c::write_obid(uvma_obi_memory_mon_trn_c trn);

  cnt_obid_trn++;

  if (trn.err) begin
    cnt_obid_err++;

    if (!pending_nmi) begin
      cnt_obid_firsterr++;
      pending_nmi = 1;
    end
  end

endfunction : write_obid


function void uvme_cv32e40s_buserr_sb_c::write_obii(uvma_obi_memory_mon_trn_c trn);

  cnt_obii_trn++;

  if (trn.err) begin
    cnt_obii_err++;
    add_to_err_queue(trn);
  end else begin
    // Acquit this address, as it was (re)fetched wo/ err
    remove_from_err_queue(trn);
  end

endfunction : write_obii


function void uvme_cv32e40s_buserr_sb_c::write_rvfi(uvma_rvfi_instr_seq_item_c#(ILEN,XLEN) trn);

  bit [31:0] mcause = trn.csrs["mcause"].rdata;
  bit [31:0] dcsr = trn.csrs["dcsr"].get_csr_retirement_data;
  bit step = dcsr[2];
  bit stepie = dcsr[11];

  cnt_rvfi_trn++;

  // Expected ifault retires
  if (should_instr_err(trn)) begin
    cnt_rvfi_errmatch++;

    //TODO:mateilga remove this separate counter when RVFI is updated with an intr cause field
    if (trn.dbg_mode) begin
      cnt_rvfi_errmatch_debug++;
    end

    assert (trn.trap)
      else `uvm_error(info_tag, $sformatf("retire at 0x%08x (expected 'err') lacks 'rvfi_trap'", trn.pc_rdata));
    assert ((cnt_rvfi_errmatch - cnt_rvfi_errmatch_debug) - cnt_rvfi_ifaulthandl <= 1)
      else `uvm_error(info_tag, "too many err retires without ifault handling");
  end

  // D-side NMI handler
  //TODO:mateilga update this to check the new intr cause field when RVFI is updated
  if (trn.intr && mcause[31] && (mcause[30:0] inside {128, 129})) begin
    cnt_rvfi_nmihandl++;

    assert (pending_nmi)
      else `uvm_error(info_tag, "nmi handlered entered without sb having seen an 'err' on d-bus");
    pending_nmi = 0;

    assert (cnt_obid_firsterr == cnt_rvfi_nmihandl)
      else `uvm_error(info_tag, "expected D-bus 'err' count equal to handler entry count");
  end

  // I-side exception handler
  //TODO:mateilga update this to check the new intr cause field when RVFI is updated. This will allow for counting handler entries during debug
  if (trn.intr && !mcause[31] && (mcause[31:0] == 48)) begin
    cnt_rvfi_ifaulthandl++;

    assert ((cnt_rvfi_errmatch - cnt_rvfi_errmatch_debug) == cnt_rvfi_ifaulthandl)
      else `uvm_error(info_tag, "ifault handler entered without matching an ifault retirement");
  end

  // Retires after D-side "first err"
  if (pending_nmi && !trn.dbg_mode && !(step && !stepie)) begin
    late_retires++;
    assert (late_retires <= 2 + 1)  // "+1" is for the "rvfi_valid" that belongs to before the nmi
      else `uvm_error(info_tag, "more than 2 instructions retired before the nmi was taken");
  end
  if (!pending_nmi) begin
    late_retires = 0;
  end

endfunction : write_rvfi


function void uvme_cv32e40s_buserr_sb_c::build_phase(uvm_phase phase);

  super.build_phase(phase);

  obid = new("obid", this);
  obii = new("obii", this);
  rvfi = new("rvfi", this);

endfunction : build_phase


function void uvme_cv32e40s_buserr_sb_c::check_phase(uvm_phase phase);

  super.check_phase(phase);

  // Check OBI D-side
  assert (cnt_obid_trn > 0)
    else `uvm_warning(info_tag, "zero D-side OBI transactions received");
  assert (cnt_obid_trn >= cnt_obid_err)
    else `uvm_error(info_tag, "obid 'err' transactions counted wrong");
  assert (cnt_obid_trn != cnt_obid_err)
    else `uvm_warning(info_tag, "all the D-side OBI transactions were errs");
  assert (cnt_obid_err >= cnt_obid_firsterr)
    else `uvm_error(info_tag, "obid 'first' transactions counted wrong");
  assert (!(cnt_obid_err && !cnt_obid_firsterr))
    else `uvm_error(info_tag, "'first' errs counted wrong");

  // Check RVFI D-side
  assert (cnt_rvfi_trn >= cnt_rvfi_nmihandl)
    else `uvm_error(info_tag, "rvfi 'nmi' transactions counted wrong");
  assert (cnt_rvfi_trn != cnt_rvfi_nmihandl)
    else `uvm_error(info_tag, "all the rvfi transactions where nmi entries");

  // Check OBI D-side vs RVFI
  assert (cnt_obid_firsterr inside {cnt_rvfi_nmihandl, cnt_rvfi_nmihandl + 1})
    else `uvm_error(info_tag, $sformatf("more/less 'err' (%0d) than nmi handling (%0d)", cnt_obid_firsterr, cnt_rvfi_nmihandl));

  // Check OBI I-side
  assert (cnt_obii_trn > 0)
    else `uvm_warning(info_tag, "zero I-side OBI transactions received");
  assert (cnt_obii_trn >= cnt_obii_err)
    else `uvm_error(info_tag, "obii 'err' transactions counted wrong");
  assert (cnt_obii_trn != cnt_obii_err)
    else `uvm_warning(info_tag, "all the I-side OBI transactions were errs");

  // Check RVFI I-side
  assert ((cnt_rvfi_errmatch - cnt_rvfi_errmatch_debug) >= cnt_rvfi_ifaulthandl)
    else `uvm_error(info_tag, "more instr fault handler than actual err retirements");
  assert ((cnt_rvfi_errmatch - cnt_rvfi_errmatch_debug) == cnt_rvfi_ifaulthandl)
    else `uvm_warning(info_tag, $sformatf("err retires (%0d) != handler entries (%0d)", (cnt_rvfi_errmatch - cnt_rvfi_errmatch_debug), cnt_rvfi_ifaulthandl));

  // Check OBI I-side vs RVFI
  assert (cnt_obii_err >= cnt_rvfi_ifaulthandl)
    else `uvm_error(info_tag, $sformatf("less I-side err (%0d) than exception handling (%0d)", cnt_obii_err, cnt_rvfi_ifaulthandl));
  assert (cnt_obii_err >= cnt_rvfi_errmatch)
    else `uvm_warning(info_tag, "more retired errs than fetches");

  // Check RVFI (just a sanity check)
  assert (cnt_rvfi_trn > 0)
    else `uvm_warning(info_tag, "zero rvfi transactions received");

  // Inform about the end state
  `uvm_info(info_tag, $sformatf("received %0d D-side 'err' transactions", cnt_obid_err), UVM_NONE)
  `uvm_info(info_tag, $sformatf("received %0d D-side 'first err' transactions", cnt_obid_firsterr), UVM_NONE)
  `uvm_info(info_tag, $sformatf("observed %0d rvfi nmi handler entries", cnt_rvfi_nmihandl), UVM_NONE)
  `uvm_info(info_tag, $sformatf("received %0d I-side 'err' transactions", cnt_obii_err), UVM_NONE)
  `uvm_info(info_tag, $sformatf("retired %0d expectedly ifault instructions", cnt_rvfi_errmatch), UVM_NONE)
  `uvm_info(info_tag, $sformatf("retired %0d expectedly ifault instructions during debug", cnt_rvfi_errmatch_debug), UVM_NONE)
  `uvm_info(info_tag, $sformatf("observed %0d rvfi ifault handler entries", cnt_rvfi_ifaulthandl), UVM_NONE)

endfunction : check_phase


function bit uvme_cv32e40s_buserr_sb_c::should_instr_err(uvma_rvfi_instr_seq_item_c#(ILEN,XLEN) rvfi_trn);

  uvma_obi_memory_addr_l_t  err_addrs[$];
  bit [31:0]                rvfi_addr = rvfi_trn.pc_rdata;

  // Extract all addrs from queue of I-side OBI "err" transactions
  foreach (obii_err_queue[i]) begin
    err_addrs[i] = obii_err_queue[i].address;
  end

  foreach (err_addrs[i]) begin
    bit compressed =
      (rvfi_trn.insn[1:0] != 2'b 11)
      && !({rvfi_addr[31:2], 2'b 00} inside {err_addrs});
    bit [31:0] hi_addr = err_addrs[i] + 4;
    bit [31:0] lo_addr = err_addrs[i] - (compressed ? 2 : 4);

    if ((lo_addr < rvfi_addr) && (rvfi_addr < hi_addr)) begin
      return 1;
    end
  end
  return 0;  // No match found, rvfi trn not expected to have "err"

endfunction : should_instr_err


function void uvme_cv32e40s_buserr_sb_c::remove_from_err_queue(uvma_obi_memory_mon_trn_c  trn);

  foreach (obii_err_queue[i]) begin
    if (obii_err_queue[i].address == trn.address) begin
      obii_err_queue.delete(i);
      return;
    end
  end

endfunction : remove_from_err_queue


function void uvme_cv32e40s_buserr_sb_c::add_to_err_queue(uvma_obi_memory_mon_trn_c  trn);

  remove_from_err_queue(trn);  // (In case of old entry w/ same addr)
  obii_err_queue.push_back(trn);

endfunction : add_to_err_queue


`endif  // __UVME_CV32E40S_BUSERR_SB_SV__
