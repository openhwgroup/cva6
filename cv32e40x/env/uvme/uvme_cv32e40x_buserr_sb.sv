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


`uvm_analysis_imp_decl(_obid)
`uvm_analysis_imp_decl(_rvfi)


class uvme_cv32e40x_buserr_sb_c extends uvm_scoreboard;

  string info_tag = "BUSERRSB";

  uvm_analysis_imp_obid#(uvma_obi_memory_mon_trn_c, uvme_cv32e40x_buserr_sb_c)  obid;
  uvm_analysis_imp_rvfi#(uvma_rvfi_instr_seq_item_c#(ILEN,XLEN), uvme_cv32e40x_buserr_sb_c)  rvfi;

  int cnt_obid_trn;  // Count of all obi d-side transactions
  int cnt_obid_err;  // Count of all d-side "err" transactions
  int cnt_obid_first;  // Count of all first d-side "err", in case of multiple "err" before handler "taken"
  int cnt_rvfi_trn;  // Count of all rvfi transactions
  int cnt_rvfi_nmi;  // Count of all nmi entries
    // TODO:ropeders count load/store separately?

  `uvm_component_utils(uvme_cv32e40x_buserr_sb_c)

  extern function new(string name="uvme_cv32e40x_buserr_sb", uvm_component parent=null);
  extern virtual function void write_obid(uvma_obi_memory_mon_trn_c trn);
  extern virtual function void write_rvfi(uvma_rvfi_instr_seq_item_c#(ILEN,XLEN) trn);
  extern virtual function void build_phase(uvm_phase phase);
  extern virtual function void check_phase(uvm_phase phase);

endclass : uvme_cv32e40x_buserr_sb_c


function uvme_cv32e40x_buserr_sb_c::new(string name="uvme_cv32e40x_buserr_sb", uvm_component parent=null);

  super.new(name, parent);

endfunction : new


function void uvme_cv32e40x_buserr_sb_c::write_obid(uvma_obi_memory_mon_trn_c trn);

  cnt_obid_trn++;

  if (trn.err) begin
    cnt_obid_err++;
    // TODO:ropeders store in queue for later comparison?
  end

  // TODO:ropeders count "first" errs

endfunction : write_obid


function void uvme_cv32e40x_buserr_sb_c::write_rvfi(uvma_rvfi_instr_seq_item_c#(ILEN,XLEN) trn);

  logic [31:0] mcause;

  cnt_rvfi_trn++;

  // TODO:ropeders filter/detect and count "taken" nmis
  if (trn.intr) $display("TODO intr handler rvfi");
  mcause = trn.csrs["mcause"].get_csr_retirement_data;
  if (trn.intr && mcause[31] && (mcause[30:0] inside {128, 129})) begin
    // TODO:ropeders no magic numbers ^
    // TODO:ropeders make the filter/detection correct ^

    cnt_rvfi_nmi++;
    // TODO:ropeders store in queue for later comparison?
  end

  // TODO:ropeders track rvfi_intr and "previous_rvfi"?  (and also check later)

  // TODO:ropeders add checking in other function?
  // TODO:ropeders must check that all obi err has rvfi nmi entry within some max number?
  // TODO:ropeders must check that nmi entry has a preceding obi err?
  // TODO:ropeders check match of PC addr etc?

endfunction : write_rvfi


function void uvme_cv32e40x_buserr_sb_c::build_phase(uvm_phase phase);

  super.build_phase(phase);

  obid = new("obid", this);
  rvfi = new("rvfi", this);

endfunction : build_phase


function void uvme_cv32e40x_buserr_sb_c::check_phase(uvm_phase phase);

  super.check_phase(phase);

  assert (cnt_obid_trn > 0) else `uvm_warning(info_tag, "Zero D-side transactions received");
  assert (cnt_obid_trn >= cnt_obid_err) else `uvm_error(info_tag, "obid 'err' transactions counted wrong");
  assert (cnt_obid_err >= cnt_obid_first) else `uvm_error(info_tag, "obid 'first' transactions counted wrong");
  `uvm_info(info_tag, $sformatf("received %0d D-side 'err' transactions", cnt_obid_err), UVM_NONE)  // TODO:ropeders change

  assert (cnt_rvfi_trn > 0) else `uvm_warning(info_tag, "Zero rvfi transactions received");
  assert (cnt_rvfi_trn >= cnt_rvfi_nmi) else `uvm_error(info_tag, "rvfi 'nmi' transactions counted wrong");
  `uvm_info(info_tag, $sformatf("received %0d rvfi transactions", cnt_rvfi_trn), UVM_NONE)  // TODO:ropeders remove
  `uvm_info(info_tag, $sformatf("received %0d rvfi nmi entries", cnt_rvfi_nmi), UVM_NONE)  // TODO:ropeders change

endfunction : check_phase


`endif  // __UVME_CV32E40X_BUSERR_SB_SV__
