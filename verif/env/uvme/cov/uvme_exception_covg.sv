//
// Copyright 2024 OpenHW Group
// Copyright 2024 Thales
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

// Original Author: Ayoub JALALI (ayoub.jalali@external.thalesgroup.com)

covergroup cg_exception(
    string name,
    bit pmp_supported,
    bit unaligned_access_supported,
    bit ext_c_supported,
    bit mode_u_supported,
    bit mode_s_supported,
    bit debug_supported,
    bit [CSR_MASK_WL-1:0] cfg_illegal_csr
) with function sample (
    uvma_isacov_instr_c instr
);
  option.per_instance = 1;
  option.name = name;

`ifndef QUESTA
  cp_exception: coverpoint instr.cause {

    bins BREAKPOINT = {3} iff (instr.trap);

    bins ILLEGAL_INSTR = {2} iff (instr.trap);

    ignore_bins IGN_ADDR_MISALIGNED_EXC = {0, 4, 6} iff (unaligned_access_supported);
    ignore_bins IGN_INSTR_ADDR_MISALIGNED_EXC = {0} iff (ext_c_supported);
    bins INSTR_ADDR_MISALIGNED = {0} iff (instr.trap);

    bins LD_ADDR_MISALIGNED    = {4} iff (instr.trap);

    bins ST_ADDR_MISALIGNED    = {6} iff (instr.trap);

    ignore_bins IGN_ACCESS_FAULT_EXC = {1,5,7} iff (!pmp_supported);
    bins INSTR_ACCESS_FAULT = {1} iff (instr.trap);

    bins LD_ACCESS_FAULT    = {5} iff (instr.trap);

    bins ST_ACCESS_FAULT    = {7} iff (instr.trap);

    ignore_bins IGN_ENV_CALL_UMODE = {8} iff (!mode_u_supported);
    bins ENV_CALL_UMODE = {8} iff (instr.trap);

    ignore_bins IGN_ENV_CALL_SMODE = {9} iff (!mode_s_supported);
    bins ENV_CALL_SMODE = {9} iff (instr.trap);

    bins ENV_CALL_MMODE = {11} iff (instr.trap);

    bins INSTR_PAGE_FAULT = {12} iff (instr.trap);

    bins LOAD_PAGE_FAULT  = {13} iff (instr.trap);

    bins STORE_PAGE_FAULT = {15} iff (instr.trap);

    ignore_bins IGN_DEBUG_REQUEST = {24} iff (!debug_supported);
    bins DEBUG_REQUEST = {24} iff (instr.trap);

  }

  cp_trap: coverpoint instr.trap {
    bins is_trap = {1};
    bins no_trap = {0};
  }

  cp_is_ebreak: coverpoint instr.name {
    bins is_ebreak = {uvma_isacov_pkg::EBREAK,
                      uvma_isacov_pkg::C_EBREAK};
  }

  cp_is_dret: coverpoint instr.name {
    bins is_dret = {uvma_isacov_pkg::DRET};
  }

  cp_is_ecall: coverpoint instr.name {
    bins is_ecall = {uvma_isacov_pkg::ECALL};
  }

  cp_is_csr: coverpoint instr.group {
    bins is_csr_instr = {uvma_isacov_pkg::CSR_GROUP};
  }

  cp_is_write_csr: coverpoint instr.is_csr_write() {
    bins is_csr_write = {1};
  }

  cp_is_not_write_csr: coverpoint instr.is_csr_write() {
    bins is_not_csr_write = {0};
  }

  cp_illegal_csr: coverpoint instr.csr {
    bins UNSUPPORTED_CSR[] = {[uvma_isacov_pkg::USTATUS:uvma_isacov_pkg::MCONFIGPTR]} with (cfg_illegal_csr[item] == 1);
  }

  cp_ro_csr: coverpoint instr.csr {
    bins ONLY_READ_CSR[] = {[uvma_isacov_pkg::USTATUS:uvma_isacov_pkg::MCONFIGPTR]} with ((cfg_illegal_csr[item] == 0) && (item[11:10] == 2'b11));
  }

  cp_misalign_load: coverpoint instr.group {
    bins misalign_load = {uvma_isacov_pkg::MISALIGN_LOAD_GROUP};
  }

  cp_misalign_store: coverpoint instr.group {
    bins misalign_store = {uvma_isacov_pkg::MISALIGN_STORE_GROUP};
  }

  cp_add_mem: coverpoint instr.rvfi.mem_addr[1:0] {
    bins add_mem[] = {[0:$]};
  }

  cross_breakpoint : cross cp_exception, cp_is_ebreak {
    ignore_bins IGN = !binsof(cp_exception) intersect{3};
  }

  cross_ecall : cross cp_exception, cp_is_ecall {
    ignore_bins IGN = !binsof(cp_exception) intersect{11};
  }

  cross_dret : cross cp_exception, cp_is_dret iff(!debug_supported){
    ignore_bins IGN = !binsof(cp_exception) intersect{2};
  }

  cross_illegal_csr : cross cp_exception, cp_illegal_csr, cp_is_csr, cp_is_not_write_csr {
    ignore_bins IGN = !binsof(cp_exception) intersect{2};
  }

  cross_illegal_write_csr : cross cp_exception, cp_ro_csr, cp_is_write_csr {
    ignore_bins IGN = !binsof(cp_exception) intersect{2};
  }

  cross_misaligned_load : cross cp_exception, cp_misalign_load, cp_add_mem iff(!unaligned_access_supported){
    ignore_bins IGN_EXC = !binsof(cp_exception) intersect{4};
    ignore_bins IGN_ADD =  binsof(cp_add_mem) intersect{0};
  }

  cross_misaligned_store : cross cp_exception, cp_misalign_store, cp_add_mem iff(!unaligned_access_supported){
    ignore_bins IGN_EXC = !binsof(cp_exception) intersect{6};
    ignore_bins IGN_ADD =  binsof(cp_add_mem) intersect{0};
  }
`endif

endgroup : cg_exception

class uvme_exception_cov_model_c extends uvm_component;

    /*
    * Class members
    */
   // Objects
   uvme_cva6_cfg_c         cfg      ;
   uvme_cva6_cntxt_c       cntxt    ;

   // TLM
   uvm_tlm_analysis_fifo#(uvma_isacov_mon_trn_c)  mon_trn_fifo;

   uvma_isacov_mon_trn_c mon_trn;

  `uvm_component_utils(uvme_exception_cov_model_c)

   //Exception Covergroup
   cg_exception exception_cg;

   extern function new(string name = "exception_cov_model", uvm_component parent = null);
   extern function void build_phase(uvm_phase phase);
   extern task run_phase(uvm_phase phase);

endclass : uvme_exception_cov_model_c

function uvme_exception_cov_model_c::new(string name = "exception_cov_model", uvm_component parent = null);

   super.new(name, parent);

endfunction : new

function void uvme_exception_cov_model_c::build_phase(uvm_phase phase);

   super.build_phase(phase);

   void'(uvm_config_db#(uvme_cva6_cfg_c)::get(this, "", "cfg", cfg));
   if (!cfg) begin
      `uvm_fatal("CFG", "Configuration handle is null")
   end

   exception_cg = new("exception_cg",
                      .pmp_supported(cfg.pmp_supported),
                      .unaligned_access_supported(cfg.unaligned_access_supported),
                      .ext_c_supported(cfg.ext_c_supported),
                      .mode_u_supported(cfg.mode_u_supported),
                      .mode_s_supported(cfg.mode_s_supported),
                      .debug_supported(cfg.debug_supported),
                      .cfg_illegal_csr(cfg.unsupported_csr_mask));

   mon_trn_fifo   = new("mon_trn_fifo" , this);

endfunction : build_phase

task uvme_exception_cov_model_c::run_phase(uvm_phase phase);

  super.run_phase(phase);

   `uvm_info("EXCEPTION_COVG", "The Exception env coverage model is running", UVM_LOW);

  forever begin
      mon_trn_fifo.get(mon_trn);
      exception_cg.sample(mon_trn.instr);
    end

endtask : run_phase

