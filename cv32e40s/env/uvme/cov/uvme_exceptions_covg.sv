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


covergroup cg_exceptions
  with function sample(uvma_isacov_mon_trn_c isacov);

  `per_instance_fcov

  cp_trap : coverpoint isacov.instr.rvfi.trap {
    bins trap = {1};
  }
  cp_intr : coverpoint isacov.instr.rvfi.intr {
    bins intr = {1};
  }
  cp_imm12 : coverpoint isacov.instr.csr_val {
    bins imm12[16] = {[0:$]};
    bins msb = {12'h 800};
    bins lsb = {12'h 001};
  }
  cp_is_csr : coverpoint (isacov.instr.group == CSR_GROUP) {
    bins is_csr = {1};
  }
  cp_is_ebreak : coverpoint (isacov.instr.name inside {EBREAK, C_EBREAK}) {
    bins is_ebreak = {1};
  }
  cp_no_ebreakm : coverpoint (isacov.instr.rvfi.csrs["dcsr"].get_csr_retirement_data()[15]) {
    bins no_ebreakm = {0};
  }
  cp_mcause : coverpoint isacov.instr.rvfi.csrs["mcause"].get_csr_retirement_data() {
    bins reset               = {0};
    bins ins_acc_fault       = {1};
    bins illegal_ins         = {2};
    bins breakpoint          = {3};
    bins load_acc_fault      = {5};
    bins store_amo_acc_fault = {7};
    bins ecall               = {11};
    bins ins_bus_fault       = {48};
  }
  cp_pcr_mtvec : coverpoint (isacov.instr.rvfi.pc_rdata[31:2] == isacov.instr.rvfi.csrs["mtvec"].get_csr_retirement_data()[31:2]) {
    bins one = {1};
  }
  cp_pcw_mtvec : coverpoint (isacov.instr.rvfi.pc_wdata[31:2] == isacov.instr.rvfi.csrs["mtvec"].get_csr_retirement_data()[31:2]) {
    bins one = {1};
  }

  cross_all_csrs : cross cp_imm12, cp_is_csr;  // CSR instructions shall try all 2^12 existing/nonexisting CSRs
  cross_trap_to_mtvec : cross cp_trap, cp_pcw_mtvec;  // Trap going to mtvec.base
  cross_trap_in_mtvec : cross cp_intr, cp_pcr_mtvec;  // Trap executing at mtvec.base
  cross_ebreak_trap : cross cp_is_ebreak, cp_no_ebreakm, cp_trap, cp_mcause {
    ignore_bins ig = ! binsof(cp_mcause) intersect {3};  // Shall hit specifically mcause == breakpoint
  }
  // TODO:ropeders cross mcause==3 and cp for instr/data trigger match with action==0
  cross_trap_mcause : cross cp_trap, cp_mcause {
    ignore_bins ig = binsof(cp_mcause) intersect {0};  // Can't trap with mcause == reset value
  }
  cross_intr_mcause : cross cp_intr, cp_mcause {
    ignore_bins ig = binsof(cp_mcause) intersect {0};  // Can't trap with mcause == reset value
  }

endgroup : cg_exceptions


class uvme_exceptions_covg extends uvm_component;

  `uvm_analysis_imp_decl(_isacov)

  cg_exceptions exceptions_cg;
  uvm_analysis_imp_isacov#(uvma_isacov_mon_trn_c, uvme_exceptions_covg) isacov_mon_export;

  `uvm_component_utils(uvme_exceptions_covg);

  extern function new(string name = "exceptions_covg", uvm_component parent = null);
  extern function void build_phase(uvm_phase phase);
  extern function void write_isacov(uvma_isacov_mon_trn_c isacov);

endclass : uvme_exceptions_covg


function uvme_exceptions_covg::new(string name = "exceptions_covg", uvm_component parent = null);

  super.new(name, parent);

  isacov_mon_export = new("isacov_mon_export", this);

endfunction : new


function void uvme_exceptions_covg::build_phase(uvm_phase phase);

  super.build_phase(phase);

  exceptions_cg = new();

endfunction : build_phase


function void uvme_exceptions_covg::write_isacov(uvma_isacov_mon_trn_c isacov);

  exceptions_cg.sample(isacov);

endfunction : write_isacov
