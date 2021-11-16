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


`ifndef __UVME_CV32E40X_BUSERR_SB_SV__
`define __UVME_CV32E40X_BUSERR_SB_SV__


`uvm_analysis_imp_decl(_obid)  // D-side OBI
`uvm_analysis_imp_decl(_obii)  // I-side OBI
`uvm_analysis_imp_decl(_rvfi)


class uvme_cv32e40x_buserr_sb_c extends uvm_scoreboard;

  string info_tag = "BUSERRSB";

  uvm_analysis_imp_obid#(uvma_obi_memory_mon_trn_c, uvme_cv32e40x_buserr_sb_c)  obid;
  uvm_analysis_imp_obii#(uvma_obi_memory_mon_trn_c, uvme_cv32e40x_buserr_sb_c)  obii;
  uvm_analysis_imp_rvfi#(uvma_rvfi_instr_seq_item_c#(ILEN,XLEN), uvme_cv32e40x_buserr_sb_c)  rvfi;

  // OBI D-side variables
  int cnt_obid_trn;   // Count of all obi d-side transactions
  int cnt_obid_err;   // Count of all d-side "err" transactions
  int cnt_obid_first; // Count of all first d-side "err", in case of multiple "err" before handler "taken"
  // OBI I-side variables
  int cnt_obii_trn;  // Count of all obi i-side transactions
  int cnt_obii_err;   // Count of all i-side "err" transactions
  // RVFI variables
  int cnt_rvfi_trn;  // Count of all rvfi transactions
  int cnt_rvfi_nmi;  // Count of all nmi handler entries
  int cnt_rvfi_exce; // Count of all instr bus fault handler entries
  int cnt_rvfi_err;  // Count of all retires with expected I-side "err"
  // Expectation variables
  int pending_nmi;  // Whether nmi happened and handler is expected
  uvma_obi_memory_mon_trn_c obii_trn_errs[$];

  `uvm_component_utils(uvme_cv32e40x_buserr_sb_c)

  extern function              new(string name="uvme_cv32e40x_buserr_sb", uvm_component parent=null);
  extern virtual function void write_obid(uvma_obi_memory_mon_trn_c trn);
  extern virtual function void write_obii(uvma_obi_memory_mon_trn_c trn);
  extern virtual function void write_rvfi(uvma_rvfi_instr_seq_item_c#(ILEN,XLEN) trn);
  extern virtual function void build_phase(uvm_phase phase);
  extern virtual function void check_phase(uvm_phase phase);
  extern function logic        instr_should_err(uvma_rvfi_instr_seq_item_c#(ILEN,XLEN) rvfi_trn);
  extern function void         clean_errs_queue(uvma_obi_memory_mon_trn_c  trn);

endclass : uvme_cv32e40x_buserr_sb_c


function uvme_cv32e40x_buserr_sb_c::new(string name="uvme_cv32e40x_buserr_sb", uvm_component parent=null);

  super.new(name, parent);

endfunction : new


function void uvme_cv32e40x_buserr_sb_c::write_obid(uvma_obi_memory_mon_trn_c trn);

  cnt_obid_trn++;

  if (trn.err) begin
    cnt_obid_err++;
    // TODO:ropeders store in queue to later compare vs CSRs?

    // TODO:ropeders how to assert when handler must come?

    if (!pending_nmi) begin
      cnt_obid_first++;
      pending_nmi = 1;  // TODO:ropeders no race conditions here?
    end
  end

  // TODO:ropeders have count of longest streak of multiple errs?

endfunction : write_obid


function void uvme_cv32e40x_buserr_sb_c::write_obii(uvma_obi_memory_mon_trn_c trn);

  cnt_obii_trn++;

  // TODO:ropeders remove from "tainted queue" if addr was now re-fetched
  clean_errs_queue(trn);

  if (trn.err) begin
    cnt_obii_err++;

    // TODO:ropeders save PC (or even more)?

    obii_trn_errs.push_back(trn);
    // TODO:ropeders assert uvm_warning expecting [1:0] of addr to be zero?
  end

endfunction : write_obii


function void uvme_cv32e40x_buserr_sb_c::write_rvfi(uvma_rvfi_instr_seq_item_c#(ILEN,XLEN) trn);

  logic [31:0] mcause;

  mcause = trn.csrs["mcause"].get_csr_retirement_data;

  cnt_rvfi_trn++;

  // TODO:ropeders
  if (instr_should_err(trn)) begin
    // TODO:ropeders count retired I-side "err"
    cnt_rvfi_err++;
    // TODO:ropeders add asserts

    // TODO:ropeders check expected etc
    // TODO:ropeders clean queue if >depth?
  end

  // TODO:ropeders count "at most two instructions may retire before the NMI is taken"?

  // D-side NMI counting
  if (trn.intr && mcause[31] && (mcause[30:0] inside {128, 129})) begin
    // TODO:ropeders no magic numbers ^
    // TODO:ropeders make the filter/detection correct ^
    // TODO:ropeders compare pc vs nmi handler address? ^

    cnt_rvfi_nmi++;

    assert (pending_nmi)
      else `uvm_error(info_tag, "nmi handlered entered without sb having seen an 'err' on d-bus");
    pending_nmi = 0;  // TODO:ropeders ensure no race condition with obi analysis port

    assert (cnt_obid_first == cnt_rvfi_nmi)
      else `uvm_error(info_tag, "expected D-bus 'err' count equal to handler entry count");
  end

  // I-side exception counting
  if (trn.intr && !mcause[31] && (mcause[31:0] == 48)) begin
    // TODO:ropeders "rvfi_intr" on traps doesn't feel semantically correct vs the signal name ^
    // TODO:ropeders no magic numbers ^

    cnt_rvfi_exce++;

    // TODO:ropeders assert that this entry was expected (count vs count)
    // TODO:ropeders assert that rvfi_trap was on in the previous retire?
  end

  // TODO:ropeders track rvfi_intr and "previous_rvfi"?  (and also check later)

  // TODO:ropeders add checking in other function?
  // TODO:ropeders must check that all obi err has rvfi nmi entry within some max number?
  // TODO:ropeders check match of PC addr and other CSRs?

endfunction : write_rvfi


function void uvme_cv32e40x_buserr_sb_c::build_phase(uvm_phase phase);

  super.build_phase(phase);

  obid = new("obid", this);
  obii = new("obii", this);
  rvfi = new("rvfi", this);

endfunction : build_phase


function void uvme_cv32e40x_buserr_sb_c::check_phase(uvm_phase phase);

  super.check_phase(phase);

  // Check OBI D-side counting
  assert (cnt_obid_trn > 0)
    else `uvm_warning(info_tag, "zero D-side OBI transactions received");
  assert (cnt_obid_trn >= cnt_obid_err)
    else `uvm_error(info_tag, "obid 'err' transactions counted wrong");
  assert (cnt_obid_trn != cnt_obid_err)
    else `uvm_warning(info_tag, "all the D-side OBI transactions were errs");
  assert (cnt_obid_err >= cnt_obid_first)
    else `uvm_error(info_tag, "obid 'first' transactions counted wrong");
  `uvm_info(info_tag, $sformatf("received %0d D-side 'err' transactions", cnt_obid_err), UVM_NONE)  // TODO:ropeders change

  // Check RVFI
  assert (cnt_rvfi_trn > 0)
    else `uvm_warning(info_tag, "zero rvfi transactions received");

  // Check RVFI D-side counting
  assert (cnt_rvfi_trn >= cnt_rvfi_nmi)
    else `uvm_error(info_tag, "rvfi 'nmi' transactions counted wrong");
  assert (cnt_rvfi_trn != cnt_rvfi_nmi)
    else `uvm_warning(info_tag, "all the rvfi transactions where nmi entries");
  `uvm_info(info_tag, $sformatf("observed %0d rvfi nmi handler entries", cnt_rvfi_nmi), UVM_NONE)  // TODO:ropeders change

  // Check OBI D-side vs RVFI counting
  assert (cnt_obid_first == cnt_rvfi_nmi)
    else `uvm_error(info_tag, $sformatf("more/less 'err' (%0d) than nmi handling (%0d)", cnt_obid_first, cnt_rvfi_nmi));
  `uvm_info(info_tag, $sformatf("observed %0d first D-side 'err' and %0d handler entries", cnt_obid_first, cnt_rvfi_nmi), UVM_NONE)
    // TODO:ropeders change ^
  // TODO:ropeders "cnt_obid_first" could be 1 higher if sim exits early? No more, right?

  // Check OBI I-side counting
  assert (cnt_obii_trn > 0)
    else `uvm_warning(info_tag, "zero I-side OBI transactions received");
  assert (cnt_obii_trn >= cnt_obii_err)
    else `uvm_error(info_tag, "obii 'err' transactions counted wrong");
  assert (cnt_obii_trn != cnt_obii_err)
    else `uvm_warning(info_tag, "all the I-side OBI transactions were errs");
  //TODO:ropeders any more asserts to add?
  `uvm_info(info_tag, $sformatf("received %0d I-side 'err' transactions", cnt_obii_err), UVM_NONE)  // TODO:ropeders change

  // Check TODO instr bus fault prediction counting
  //TODO:ropeders any more asserts to add?

  // Check RVFI I-side counting
  assert (cnt_obii_err >= cnt_rvfi_exce)
    else `uvm_error(info_tag, $sformatf("less I-side 'err' (%0d) than exception handling (%0d)", cnt_obii_err, cnt_rvfi_exce));
  //TODO:ropeders any more asserts to add?
  `uvm_info(info_tag, $sformatf("observed %0d rvfi instr bus fault entries", cnt_rvfi_exce), UVM_NONE)  // TODO:ropeders change

  // Check TODO I-side vs RVFI counting
  assert (cnt_rvfi_err >= cnt_rvfi_exce)
    else `uvm_error(info_tag, "more instr fault handler than actual err retirements");
  assert (cnt_rvfi_err == cnt_rvfi_exce)
    else `uvm_warning(info_tag, $sformatf("num err retires (%0d) != num handler entries (%0d)", cnt_rvfi_err, cnt_rvfi_exce));
      // TODO:ropeders is this a correct assumption? ^
  // TODO:ropeders assert (while running) that diff of ^ is never bigger than 1?
  assert (cnt_obii_err >= cnt_rvfi_err)
    else `uvm_warning(info_tag, "more retired errs than fetches");  // TODO:ropeders is this correct?
  `uvm_info(info_tag, $sformatf("retired %0d expectedly err'ed instructions", cnt_rvfi_err), UVM_NONE);  // TODO:ropeders change?
  //TODO:ropeders assert "cnt_rvfi_exce" vs some I-side prediction

  // TODO:ropeders how to check I-side vs D-side, "new bus faults occuring while an NMI is pending will be discarded"

endfunction : check_phase


function logic uvme_cv32e40x_buserr_sb_c::instr_should_err(uvma_rvfi_instr_seq_item_c#(ILEN,XLEN) rvfi_trn);

  uvma_obi_memory_addr_l_t  err_addrs[$];
  logic [31:0]              rvfi_addr;

  // Extract all addrs from queue of I-side OBI "err" transactions
  foreach (obii_trn_errs[i]) err_addrs[i] = obii_trn_errs[i].address;

  rvfi_addr = rvfi_trn.pc_wdata;

  // TODO return: is rvfi addr in addrs list?
  // TODO:ropeders take heed of compressed/misaligned instrs
  foreach (err_addrs[i]) begin
    if ((err_addrs[i] <= rvfi_addr) && (rvfi_addr < err_addrs[i]+4)) begin
      return 1;
      // TODO:ropeders check "top" of instr too (not just bottom addr)
      // TODO:ropeders remove found item from queue?
    end
  end
  return 0;  // No match found, rvfi trn not expected to have "err"

endfunction : instr_should_err


function void uvme_cv32e40x_buserr_sb_c::clean_errs_queue(uvma_obi_memory_mon_trn_c  trn);

  foreach (obii_trn_errs[i]) begin
    if (obii_trn_errs[i].address == trn.address) begin
      obii_trn_errs.delete(i);
      return;
    end
  end

endfunction : clean_errs_queue


`endif  // __UVME_CV32E40X_BUSERR_SB_SV__
