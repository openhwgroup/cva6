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

  uvm_analysis_imp_obid#(uvma_obi_memory_mon_trn_c, uvme_cv32e40x_buserr_sb_c)  obid;
  uvm_analysis_imp_rvfi#(uvma_rvfi_instr_seq_item_c#(ILEN,XLEN), uvme_cv32e40x_buserr_sb_c)  rvfi;

  // TODO:ropeders count "err" transactions on d-side
  // TODO:ropeders count "first err" transactions on d-side (using flags)
  // TODO:ropeders count transactions on d-side?

  `uvm_component_utils(uvme_cv32e40x_buserr_sb_c)

  extern function new(string name="uvme_cv32e40x_buserr_sb", uvm_component parent=null);
  extern virtual function void write_obid(uvma_obi_memory_mon_trn_c trn);
  extern virtual function void write_rvfi(uvma_rvfi_instr_seq_item_c#(ILEN,XLEN) trn);
  extern virtual function void build_phase(uvm_phase phase);

endclass : uvme_cv32e40x_buserr_sb_c


function uvme_cv32e40x_buserr_sb_c::new(string name="uvme_cv32e40x_buserr_sb", uvm_component parent=null);

  super.new(name, parent);

endfunction : new


function void uvme_cv32e40x_buserr_sb_c::write_obid(uvma_obi_memory_mon_trn_c trn);

  $display("TODO write_obid");

endfunction : write_obid


function void uvme_cv32e40x_buserr_sb_c::write_rvfi(uvma_rvfi_instr_seq_item_c#(ILEN,XLEN) trn);

  $display("TODO write_rvfi");

endfunction : write_rvfi


function void uvme_cv32e40x_buserr_sb_c::build_phase(uvm_phase phase);

  super.build_phase(phase);

  obid = new("obid", this);
  rvfi = new("rvfi", this);

endfunction : build_phase


`endif  // __UVME_CV32E40X_BUSERR_SB_SV__
