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


`uvm_analysis_imp_decl(_rvfi)


covergroup cg_counters
  with function sample(uvma_rvfi_instr_seq_item_c#(ILEN, XLEN) rvfi);

  `per_instance_fcov

  cp_inhibit_mcycle : coverpoint rvfi.csrs["mcountinhibit"].get_csr_retirement_data()[0];
  cp_inhibit_minstret : coverpoint rvfi.csrs["mcountinhibit"].get_csr_retirement_data()[2];
  //cp_inhibit_mhpm : ???;
  cp_is_csr_read : coverpoint ((rvfi.insn[6:0] == 7'b 1110011) && (rvfi.insn[13:12] != 2'b 00) && (rvfi.insn[11:7] != 0)) {
    bins is_csr_read = {1};
  }
  cp_is_dbg_mode : coverpoint rvfi.dbg_mode {
    bins dbg_mode = {1};
  }
  cp_mcycle : coverpoint (rvfi.insn[31:20] == 12'h B00);
  cp_minstret : coverpoint (rvfi.insn[31:20] == 12'h B02);
  // TODO:ropeders add all coverpoints

  x_check_inhibit_mcycle : cross cp_inhibit_mcycle, cp_is_csr_read, cp_mcycle {
    option.at_least = 2;
  }
  x_check_inhibit_minstret : cross cp_inhibit_minstret, cp_is_csr_read, cp_minstret {
    option.at_least = 2;
  }
  x_minstret_in_dbg : cross cp_is_dbg_mode, cp_inhibit_mcycle, cp_is_csr_read, cp_minstret {
    option.at_least = 2;
    ignore_bins ig = binsof(cp_inhibit_mcycle) intersect {1} || binsof(cp_minstret) intersect {0};
  }
  // TODO:ropeders add all crosses

endgroup : cg_counters


class uvme_counters_covg extends uvm_component;

  cg_counters  counters_cg;
  uvm_analysis_imp_rvfi#(uvma_rvfi_instr_seq_item_c#(ILEN, XLEN), uvme_counters_covg)  rvfi_mon_export;

  `uvm_component_utils(uvme_counters_covg);

  extern function new(string name = "counters_covg", uvm_component parent = null);
  extern function void build_phase(uvm_phase phase);
  extern function void write_rvfi(uvma_rvfi_instr_seq_item_c#(ILEN, XLEN) trn);

endclass : uvme_counters_covg


function uvme_counters_covg::new(string name = "counters_covg", uvm_component parent = null);

  super.new(name, parent);

  rvfi_mon_export = new("rvfi_mon_export", this);

endfunction : new


function void uvme_counters_covg::build_phase(uvm_phase phase);

  super.build_phase(phase);

  counters_cg = new();

endfunction : build_phase


function void uvme_counters_covg::write_rvfi(uvma_rvfi_instr_seq_item_c#(ILEN, XLEN) trn);

  counters_cg.sample(trn);

endfunction : write_rvfi
