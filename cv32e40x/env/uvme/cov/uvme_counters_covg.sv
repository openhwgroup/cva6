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


covergroup cg_counters (int num_mhpmcounters)
  with function sample(uvma_isacov_mon_trn_c isacov);

  `per_instance_fcov

  cp_inhibit_mcycle : coverpoint isacov.instr.rvfi.csrs["mcountinhibit"].get_csr_retirement_data()[0];
  cp_inhibit_minstret : coverpoint isacov.instr.rvfi.csrs["mcountinhibit"].get_csr_retirement_data()[2];
  cp_is_csr_read : coverpoint (isacov.instr.group == CSR_GROUP) && (isacov.instr.rd != 0) {
    bins is_csr_read = {1};
  }
  cp_is_dbg_mode : coverpoint isacov.instr.rvfi.dbg_mode {
    bins dbg_mode = {1};
  }
  cp_mcycle : coverpoint (isacov.instr.csr == uvma_isacov_pkg::MCYCLE);
  cp_minstret : coverpoint (isacov.instr.csr == uvma_isacov_pkg::MINSTRET);
  cp_num_mhpmcounters : coverpoint num_mhpmcounters {
    bins min = {0};
    bins def = {1};
    bins any = {[2:28]};
    bins max = {29};
  }

  cross_check_mcycle : cross cp_inhibit_mcycle, cp_is_csr_read, cp_mcycle {
    option.at_least = 2;
  }
  cross_check_minstret : cross cp_inhibit_minstret, cp_is_csr_read, cp_minstret {
    option.at_least = 2;
  }
  cross_mcycle_in_dbg : cross cp_is_dbg_mode, cp_inhibit_mcycle, cp_is_csr_read, cp_mcycle {
    option.at_least = 2;
    ignore_bins ig = binsof(cp_inhibit_mcycle) intersect {1} || binsof(cp_mcycle) intersect {0};
  }
  cross_minstret_in_dbg : cross cp_is_dbg_mode, cp_inhibit_mcycle, cp_is_csr_read, cp_minstret {
    option.at_least = 2;
    ignore_bins ig = binsof(cp_inhibit_mcycle) intersect {1} || binsof(cp_minstret) intersect {0};
  }
endgroup : cg_counters



covergroup cg_mhpm (int idx)
  with function sample(uvma_isacov_mon_trn_c isacov);

  `per_instance_fcov

  cp_inhibit : coverpoint isacov.instr.rvfi.csrs["mcountinhibit"].get_csr_retirement_data()[idx] {
    bins inhibit = {1};
    bins no_inhibit = {0};
  }
  cp_event : coverpoint isacov.instr.rvfi.csrs[$sformatf("mhpmevent%0d", idx)].get_csr_retirement_data() {
    bins events = {[1:$]};
    bins no_events = {0};
  }
  cp_is_csr_read : coverpoint (isacov.instr.group == CSR_GROUP) && (isacov.instr.rd != 0) {
    bins is_csr_read = {1};
  }
  cp_is_mhpm_idx : coverpoint (isacov.instr.csr == (uvma_isacov_pkg::MCYCLE + idx)) {
    bins mhpm_idx = {1};
  }
  cp_is_mhpm_idx_h : coverpoint (isacov.instr.csr == (uvma_isacov_pkg::MCYCLEH + idx)) {
    bins mhpm_idx_h = {1};
  }
  cp_is_dbg_mode : coverpoint isacov.instr.rvfi.dbg_mode {
    bins dbg_mode = {1};
  }

  cross_check_mhpm : cross cp_inhibit, cp_event, cp_is_csr_read, cp_is_mhpm_idx {
    option.at_least = 2;
  }
  cross_check_mhpm_h : cross cp_inhibit, cp_event, cp_is_csr_read, cp_is_mhpm_idx_h {
    option.at_least = 2;
  }
  cross_mhpm_in_dbg: cross cp_is_dbg_mode, cp_inhibit, cp_event, cp_is_csr_read, cp_is_mhpm_idx {
    option.at_least = 2;
    ignore_bins ig = binsof(cp_inhibit) intersect {1} || binsof(cp_event) intersect{0};
  }

endgroup : cg_mhpm


covergroup cg_inhibit_mix (int idx)
  with function sample(uvma_isacov_mon_trn_c isacov);

  `per_instance_fcov

  cp_inhibit_mcycle : coverpoint isacov.instr.rvfi.csrs["mcountinhibit"].get_csr_retirement_data()[0];
  cp_inhibit_minstret : coverpoint isacov.instr.rvfi.csrs["mcountinhibit"].get_csr_retirement_data()[2];
  cp_is_csr_read : coverpoint (isacov.instr.group == CSR_GROUP) && (isacov.instr.rd != 0) {
    bins is_csr_read = {1};
  }
  cp_is_event_cycles : coverpoint isacov.instr.rvfi.csrs[$sformatf("mhpmevent%0d", idx)].get_csr_retirement_data() {
    bins event_cycles = {1};  // selector CYCLES is bit 0
  }
  cp_is_event_instr : coverpoint isacov.instr.rvfi.csrs[$sformatf("mhpmevent%0d", idx)].get_csr_retirement_data() {
    bins event_instr = {2};  // selector INSTR is bit 1
  }
  cp_is_mhpm_idx : coverpoint (isacov.instr.csr == (uvma_isacov_pkg::MCYCLE + idx)) {
    bins mhpm_idx = {1};
  }

  cross_check_mcycle : cross cp_inhibit_mcycle, cp_is_csr_read, cp_is_event_cycles, cp_is_mhpm_idx {
    option.at_least = 2;
  }
  cross_check_minstret : cross cp_inhibit_minstret, cp_is_csr_read, cp_is_event_instr, cp_is_mhpm_idx {
    option.at_least = 2;
  }

endgroup : cg_inhibit_mix



class cg_idx_wrapper extends uvm_component;

  cg_mhpm  mhpm_cg;
  cg_inhibit_mix  inhibit_mix_cg;

  function new(string name = "cg_mhpm_wrapper", uvm_component parent = null, int idx);
    super.new(name, parent);
    this.mhpm_cg = new(idx);
    this.inhibit_mix_cg = new(idx);
  endfunction : new

  function sample(uvma_isacov_mon_trn_c isacov);
    mhpm_cg.sample(isacov);
    inhibit_mix_cg.sample(isacov);
  endfunction : sample

endclass : cg_idx_wrapper


class uvme_counters_covg extends uvm_component;

  `uvm_analysis_imp_decl(_isacov)

  cg_counters  counters_cg;
  cg_idx_wrapper  idx_cgs[3:31];
  uvm_analysis_imp_isacov#(uvma_isacov_mon_trn_c, uvme_counters_covg)  isacov_mon_export;
  uvma_core_cntrl_cfg_c  cfg;

  `uvm_component_utils(uvme_counters_covg);

  extern function new(string name = "counters_covg", uvm_component parent = null);
  extern function void build_phase(uvm_phase phase);
  extern function void write_isacov(uvma_isacov_mon_trn_c trn);

endclass : uvme_counters_covg


function uvme_counters_covg::new(string name = "counters_covg", uvm_component parent = null);

  super.new(name, parent);

  isacov_mon_export = new("isacov_mon_export", this);

endfunction : new


function void uvme_counters_covg::build_phase(uvm_phase phase);

  super.build_phase(phase);

  void'(uvm_config_db#(uvma_core_cntrl_cfg_c)::get(this, "", "cfg", cfg));
  if (!cfg) `uvm_fatal("COUNTERSCOVG", "Configuration handle is null")

  counters_cg = new(cfg.num_mhpmcounters);
  for (int i = 3; i <=31; i++) idx_cgs[i] = new(.name($sformatf("cg_idx_wrapper_%02d", i)), .parent(this), .idx(i));

endfunction : build_phase


function void uvme_counters_covg::write_isacov(uvma_isacov_mon_trn_c trn);

  counters_cg.sample(trn);
  for (int i = 0; i < cfg.num_mhpmcounters; i++) void'(idx_cgs[i + 3].sample(trn));

endfunction : write_isacov
