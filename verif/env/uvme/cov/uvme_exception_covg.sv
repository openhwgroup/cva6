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
    bit mode_u_supported,
    bit mode_s_supported,
    bit debug_supported
) with function sample (
    uvma_isacov_instr_c instr
);
  option.per_instance = 1;
  option.name = name;

  cp_exception: coverpoint instr.cause {
    bins NO_EXCEPTION = {0} iff (!instr.trap);

    bins BREAKPOINT = {3} iff (instr.trap);
    bins BREAKPOINT_EXC_RAISED = (NO_EXCEPTION => BREAKPOINT => NO_EXCEPTION);

    bins ILLEGAL_INSTR = {2} iff (instr.trap);
    bins ILLEGAL_INSTR_EXC_RAISED = (NO_EXCEPTION => ILLEGAL_INSTR => NO_EXCEPTION);

    ignore_bins IGN_ADDR_MISALIGNED_EXC = {0, 4, 6} iff (unaligned_access_supported);
    bins INSTR_ADDR_MISALIGNED = {0} iff (instr.trap);
    bins INSTR_ADDR_MISALIGNED_EXC_RAISED = (NO_EXCEPTION => INSTR_ADDR_MISALIGNED => NO_EXCEPTION);

    bins LD_ADDR_MISALIGNED    = {4} iff (instr.trap);
    bins LD_ADDR_MISALIGNED_EXC_RAISED = (NO_EXCEPTION => LD_ADDR_MISALIGNED => NO_EXCEPTION);

    bins ST_ADDR_MISALIGNED    = {6} iff (instr.trap);
    bins ST_ADDR_MISALIGNED_EXC_RAISED = (NO_EXCEPTION => ST_ADDR_MISALIGNED => NO_EXCEPTION);

    ignore_bins IGN_ACCESS_FAULT_EXC = {1,5,7} iff (!pmp_supported);
    bins INSTR_ACCESS_FAULT = {1} iff (instr.trap);
    bins INSTR_ACCESS_FAULT_EXC_RAISED = (NO_EXCEPTION => INSTR_ACCESS_FAULT => NO_EXCEPTION);

    bins LD_ACCESS_FAULT    = {5} iff (instr.trap);
    bins LD_ACCESS_FAULT_EXC_RAISED = (NO_EXCEPTION => LD_ACCESS_FAULT => NO_EXCEPTION);

    bins ST_ACCESS_FAULT    = {7} iff (instr.trap);
    bins ST_ACCESS_FAULT_EXC_RAISED = (NO_EXCEPTION => ST_ACCESS_FAULT => NO_EXCEPTION);

    ignore_bins IGN_ENV_CALL_UMODE = {8} iff (!mode_u_supported);
    bins ENV_CALL_UMODE = {8} iff (instr.trap);
    bins ENV_CALL_UMODE_EXC_RAISED = (NO_EXCEPTION => ENV_CALL_UMODE => NO_EXCEPTION);

    ignore_bins IGN_ENV_CALL_SMODE = {9} iff (!mode_s_supported);
    bins ENV_CALL_SMODE = {9} iff (instr.trap);
    bins ENV_CALL_SMODE_EXC_RAISED = (NO_EXCEPTION => ENV_CALL_SMODE => NO_EXCEPTION);

    bins ENV_CALL_MMODE = {11} iff (instr.trap);
    bins ENV_CALL_MMODE_EXC_RAISED = (NO_EXCEPTION => ENV_CALL_MMODE => NO_EXCEPTION);

    bins INSTR_PAGE_FAULT = {12} iff (instr.trap);
    bins INSTR_PAGE_FAULT_EXC_RAISED = (NO_EXCEPTION => INSTR_PAGE_FAULT => NO_EXCEPTION);

    bins LOAD_PAGE_FAULT  = {13} iff (instr.trap);
    bins LOAD_PAGE_FAULT_EXC_RAISED = (NO_EXCEPTION => LOAD_PAGE_FAULT => NO_EXCEPTION);

    bins STORE_PAGE_FAULT = {15} iff (instr.trap);
    bins STORE_PAGE_FAULT_EXC_RAISED = (NO_EXCEPTION => STORE_PAGE_FAULT => NO_EXCEPTION);

    ignore_bins IGN_DEBUG_REQUEST = {24} iff (!debug_supported);
    bins DEBUG_REQUEST = {24} iff (instr.trap);
    bins DEBUG_REQUEST_EXC_RAISED = (NO_EXCEPTION => DEBUG_REQUEST => NO_EXCEPTION);

  }

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
                      .mode_u_supported(cfg.mode_u_supported),
                      .mode_s_supported(cfg.mode_s_supported),
                      .debug_supported(cfg.debug_supported));

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

