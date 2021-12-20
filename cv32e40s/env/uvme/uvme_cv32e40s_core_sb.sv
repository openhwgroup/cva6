// Copyright 2020 OpenHW Group
// Copyright 2020 Datum Technology Corporation
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


`ifndef __UVME_CV32E40S_CORE_SB_SV__
`define __UVME_CV32E40S_CORE_SB_SV__

`uvm_analysis_imp_decl(_core_sb_rvfi_instr)
`uvm_analysis_imp_decl(_core_sb_rvvi_state)

class uvme_cv32e40s_core_sb_c extends uvm_scoreboard;

   // Fail-safe to kill the test with fatal error if the reorder queue gets to a certain size
   localparam RVFI_INSTR_REORDER_QUEUE_SIZE_LIMIT = 2;
   localparam RVFI_INSTR_QUEUE_SIZE_LIMIT = 2;

   // Objects
   uvme_cv32e40s_cfg_c    cfg;
   uvme_cv32e40s_cntxt_c  cntxt;

   // State queues
   uvma_rvfi_instr_seq_item_c#(ILEN,XLEN)  rvfi_instr_q[$];
   uvma_rvvi_state_seq_item_c#(ILEN,XLEN)  rvvi_state_q[$];
   uvma_rvfi_instr_seq_item_c#(ILEN,XLEN)  rvfi_instr_reorder_q[bit[uvma_rvfi_pkg::ORDER_WL-1:0]];

   // State variables
   int unsigned next_rvfi_order = 1;
   int unsigned next_rvvi_order = 1;

   // Maintain copy of GPRs updated by RVFI, workaround for limitiation of RVVI to only
   // report changed register writes (misses writes that do not actually change a value)
   bit[XLEN-1:0] x[32];

   // Check counters
   int unsigned pc_checked_cnt;
   int unsigned gpr_checked_cnt;
   int unsigned csr_checked_cnt;

   // Analysis exports
   uvm_analysis_imp_core_sb_rvfi_instr#(uvma_rvfi_instr_seq_item_c#(ILEN,XLEN), uvme_cv32e40s_core_sb_c) rvfi_instr_export;
   uvm_analysis_imp_core_sb_rvvi_state#(uvma_rvvi_state_seq_item_c#(ILEN,XLEN), uvme_cv32e40s_core_sb_c) rvvi_state_export;

   `uvm_component_utils_begin(uvme_cv32e40s_core_sb_c)
      `uvm_field_object(cfg  , UVM_DEFAULT)
      `uvm_field_object(cntxt, UVM_DEFAULT)
   `uvm_component_utils_end

   /**
    * Default constructor.
    */
   extern function new(string name="uvme_cv32e40s_core_sb", uvm_component parent=null);

   /**
    * Create and configures sub-scoreboards via:
    * 1. assign_cfg()
    * 2. assign_cntxt()
    * 3. create_sbs()
    */
   extern virtual function void build_phase(uvm_phase phase);

   /**
    * Main thread for the core scoreboard
    */
   extern task run_phase(uvm_phase phase);

   /**
    * Final state check for scoreboard
    */
   extern function void check_phase(uvm_phase phase);

   /**
    * Print out checked counters
    */
   extern function void report_phase(uvm_phase phase);

   /**
    * Print out checked counters when aborting test due to fatal or too many errors
    */
   extern function void pre_abort();

   /**
    * Analysis port write from RVFI instruction retirement monitor
    */
   extern virtual function void write_core_sb_rvfi_instr(uvma_rvfi_instr_seq_item_c#(ILEN,XLEN) rvfi_instr);

   /**
    * Analysis port write from RVVI state monitor
    */
   extern virtual function void write_core_sb_rvvi_state(uvma_rvvi_state_seq_item_c#(ILEN,XLEN) rvvi_state);

   /**
    * Check a retired instruction from RVVI against RVFI
    */
   extern virtual function void check_instr(uvma_rvfi_instr_seq_item_c#(ILEN,XLEN) rvfi_instr,
                                            uvma_rvvi_state_seq_item_c#(ILEN,XLEN) rvvi_state);

   /**
    * Check a GPR
    */
   extern virtual function void check_gpr(uvma_rvfi_instr_seq_item_c#(ILEN,XLEN) rvfi_instr,
                                          uvma_rvvi_state_seq_item_c#(ILEN,XLEN) rvvi_state);

   /**
    * Check a CSR
    */
   extern virtual function void check_csr(uvma_rvfi_instr_seq_item_c#(ILEN,XLEN) rvfi_instr,
                                          uvma_rvvi_state_seq_item_c#(ILEN,XLEN) rvvi_state);

   extern virtual function void check_instr_queue();

   extern virtual function void print_instr_checked_stats();

endclass : uvme_cv32e40s_core_sb_c


function uvme_cv32e40s_core_sb_c::new(string name="uvme_cv32e40s_core_sb", uvm_component parent=null);

   super.new(name, parent);

   rvfi_instr_export = new("rvfi_instr_export", this);
   rvvi_state_export = new("rvvi_state_export", this);
endfunction : new

function void uvme_cv32e40s_core_sb_c::build_phase(uvm_phase phase);

   super.build_phase(phase);

   void'(uvm_config_db#(uvme_cv32e40s_cfg_c)::get(this, "", "cfg", cfg));
   if (!cfg) begin
      `uvm_fatal("CFG", "Configuration handle is null")
   end

   void'(uvm_config_db#(uvme_cv32e40s_cntxt_c)::get(this, "", "cntxt", cntxt));
   if (!cntxt) begin
      `uvm_fatal("CNTXT", "Context handle is null")
   end

endfunction : build_phase

task uvme_cv32e40s_core_sb_c::run_phase(uvm_phase phase);

endtask : run_phase

function void uvme_cv32e40s_core_sb_c::check_phase(uvm_phase phase);

   // RVFI Reorder Instruction queue must be complete at the end of the test
   if (rvfi_instr_reorder_q.size()) begin
      `uvm_error("CORESB", $sformatf("RVFI reorder instruction queue is not empty at end of test (size: %0d)",
                                     rvfi_instr_reorder_q.size()));
   end

   // RVFI Instruction and RVVI instruction queues must be complete at the end of the test
   // Allow case where only single RVFI exists but RVVI has not finished yet
   if (!(rvfi_instr_q.size() == 1 && rvvi_state_q.size() == 0)) begin
      if (rvfi_instr_q.size()) begin
         `uvm_error("CORESB", $sformatf("RVFI expected instruction queue is not empty at end of test (size: %0d)",
                                       rvfi_instr_q.size()));
      end

      // RVVI Instruction queue must be complete at the end of the test
      if (rvvi_state_q.size()) begin
         `uvm_error("CORESB", $sformatf("RVVI expected instruction queue is not empty at end of test (size: %0d)",
                                       rvvi_state_q.size()));
      end
   end

endfunction : check_phase

function void uvme_cv32e40s_core_sb_c::report_phase(uvm_phase phase);
   print_instr_checked_stats();
endfunction : report_phase

function void uvme_cv32e40s_core_sb_c::pre_abort();
   print_instr_checked_stats();
endfunction : pre_abort

function void uvme_cv32e40s_core_sb_c::print_instr_checked_stats();
   `uvm_info("CORESB", $sformatf("checked %0d instruction retirements", pc_checked_cnt), UVM_NONE);
   `uvm_info("CORESB", $sformatf("checked %0d GPR updates", gpr_checked_cnt), UVM_NONE);
   `uvm_info("CORESB", $sformatf("checked %0d CSRs", csr_checked_cnt), UVM_NONE);
endfunction : print_instr_checked_stats

function void uvme_cv32e40s_core_sb_c::write_core_sb_rvfi_instr(uvma_rvfi_instr_seq_item_c#(ILEN,XLEN) rvfi_instr);

   // Skip if scoreboard disabled
   if (!cfg.scoreboarding_enabled)
      return;

   // If the next instruction's order field goes backward, then signal an error
   if (rvfi_instr.order < next_rvfi_order) begin
      `uvm_error("CORE_SB", $sformatf("Receied RVFI instruction with order fields less than expected, exp: %0d, insn.order: %0d",
                                      next_rvfi_order, rvfi_instr.order));
      return;
   end

   // If the next instruction's order field matches expected order, then add to queue
   if (rvfi_instr.order == next_rvfi_order) begin
      rvfi_instr_q.push_back(rvfi_instr);
      next_rvfi_order++;
   end
   // Add to the reordering queue
   else begin
      // Error if the order entry already exists
      if (rvfi_instr_reorder_q.exists(rvfi_instr.order)) begin
         `uvm_error("CORE_SB", $sformatf("Received RVFI instruction %0d out of order, but reorder queue entry already exists",
                                         rvfi_instr.order));
         return;
      end

      rvfi_instr_reorder_q[rvfi_instr.order] = rvfi_instr;
   end

   // Check if the hext ordered instruction is in the reorder queue
   while (rvfi_instr_reorder_q.exists(next_rvfi_order)) begin
      rvfi_instr_q.push_back(rvfi_instr_reorder_q[next_rvfi_order]);
      rvfi_instr_reorder_q.delete(next_rvfi_order);
      next_rvfi_order++;
   end

   // Fatal check for reorder size limit
   if (rvfi_instr_reorder_q.size() >= RVFI_INSTR_REORDER_QUEUE_SIZE_LIMIT) begin
      `uvm_error("CORE_SB", $sformatf("The RVFI reorder instruction queue is too large, size: %0d, next_rvfi_order: %0d",
                                      rvfi_instr_reorder_q.size(), next_rvfi_order));
   end

   // Fatal check for rvfi queue size limit
   if (rvfi_instr_q.size() >= RVFI_INSTR_QUEUE_SIZE_LIMIT) begin
      `uvm_error("CORE_SB", $sformatf("The RVFI instruction queue is too large, size: %0d, next_rvfi_order: %0d",
                                      rvfi_instr_q.size(), next_rvfi_order));
   end

   check_instr_queue();
endfunction : write_core_sb_rvfi_instr

function void uvme_cv32e40s_core_sb_c::write_core_sb_rvvi_state(uvma_rvvi_state_seq_item_c#(ILEN,XLEN) rvvi_state);
   if (!cfg.scoreboarding_enabled)
      return;

   // Discard invalid RVVI state updates
   if (!rvvi_state.valid)
      return;

   // Validate against expected order
   if (rvvi_state.order != next_rvvi_order) begin
      `uvm_error("CORESB", $sformatf("Received RVVI out of order: %0d, exp_order, %0d",
                                     rvvi_state.order, next_rvvi_order));
      return;
   end
   next_rvvi_order++;

   rvvi_state_q.push_back(rvvi_state);

   check_instr_queue();

endfunction : write_core_sb_rvvi_state

function void uvme_cv32e40s_core_sb_c::check_instr_queue();

   while (rvvi_state_q.size() && rvfi_instr_q.size()) begin
      uvma_rvfi_instr_seq_item_c#(ILEN,XLEN) rvfi_instr = rvfi_instr_q.pop_front();
      uvma_rvvi_state_seq_item_c#(ILEN,XLEN) rvvi_state = rvvi_state_q.pop_front();

      // First check instruction
      check_instr(rvfi_instr, rvvi_state);

      // Now check GPR state
      check_gpr(rvfi_instr, rvvi_state);

      // Check CSRs
      if (!cfg.disable_all_csr_checks)
         check_csr(rvfi_instr, rvvi_state);
   end

endfunction : check_instr_queue

function void uvme_cv32e40s_core_sb_c::check_instr(uvma_rvfi_instr_seq_item_c#(ILEN,XLEN) rvfi_instr,
                                                   uvma_rvvi_state_seq_item_c#(ILEN,XLEN) rvvi_state);

   `uvm_info("CORE_SB", $sformatf("Check PC: %0d RVFI.size() = %0d, RVVI.size() = %0d",
                                  pc_checked_cnt, rvfi_instr_q.size(), rvvi_state_q.size()), UVM_HIGH);
   pc_checked_cnt++;


   // CHECK: ORDER
   if (rvfi_instr.order != rvvi_state.order) begin
      `uvm_error("CORESB", $sformatf("ORDER mismatch, rvfi.order = %0d, rvvi.order = %0d",
                                     rvfi_instr.order, rvvi_state.order));
   end

   // CHECK: PC
   if (rvfi_instr.pc_rdata != rvvi_state.pc) begin
      `uvm_error("CORESB", $sformatf("PC Mismatch, rvfi_order: %0d, rvvi_order: %0d, rvfi.pc = 0x%08x, rvvi.pc = 0x%08x",
                                     rvfi_instr.order, rvvi_state.order, rvfi_instr.pc_rdata, rvvi_state.pc));
   end

   // CHECK: insn
   if (!rvfi_instr.trap) begin
      if (rvfi_instr.insn != rvvi_state.insn) begin
         `uvm_error("CORESB", $sformatf("INSN Mismatch, order: %0d, rvfi.pc = 0x%08x, rvfi.insn = 0x%08x, rvvi.insn = 0x%08x",
                                       rvfi_instr.order, rvfi_instr.pc_rdata, rvfi_instr.insn, rvvi_state.insn));
      end
   end

   // Heartbeat message
   if (pc_checked_cnt && ((pc_checked_cnt % PC_CHECKED_HEARTBEAT)== 0)) begin
      `uvm_info("CORE_SB", $sformatf("Compared %0d instructions", pc_checked_cnt), UVM_LOW);
   end

endfunction : check_instr

function void uvme_cv32e40s_core_sb_c::check_gpr(uvma_rvfi_instr_seq_item_c#(ILEN,XLEN) rvfi_instr,
                                                 uvma_rvvi_state_seq_item_c#(ILEN,XLEN) rvvi_state);

   // gpt_checked_cnt represents the GPR "updates" checked, so skip writes to x0
   if (rvfi_instr.rd1_addr !=0 || rvfi_instr.rd2_addr != 0)
      gpr_checked_cnt++;

   // Update the local register map
   if (rvfi_instr.rd1_addr != 0)
      x[rvfi_instr.rd1_addr] = rvfi_instr.rd1_wdata;
   if (rvfi_instr.rd2_addr != 0)
      x[rvfi_instr.rd2_addr] = rvfi_instr.rd2_wdata;

   for (int i = 0; i < 32; i++) begin
      if (x[i] != rvvi_state.x[i]) begin
         `uvm_error("CORESB", $sformatf("GPR Mismatch, order: %0d, pc: 0x%08x, rvfi_x[%0d] = 0x%08x, rvvi_x[%0d] = 0x%08x",
                                          rvfi_instr.order,
                                          rvfi_instr.pc_rdata,
                                          i, x[i],
                                          i, rvvi_state.x[i]));
      end
   end

endfunction : check_gpr

function void uvme_cv32e40s_core_sb_c::check_csr(uvma_rvfi_instr_seq_item_c#(ILEN,XLEN) rvfi_instr,
                                                 uvma_rvvi_state_seq_item_c#(ILEN,XLEN) rvvi_state);

   foreach (rvfi_instr.csrs[i]) begin
      bit[XLEN-1:0] exp_csr_value;
      bit[XLEN-1:0] csr_mask = {XLEN{1'b1}};
      string        csr = rvfi_instr.csrs[i].csr;

      // Skip disabled CSR checks from configuration object
      if (cfg.is_csr_check_disabled(csr)) continue;

      // Ensure that CSR from RVFI exists in the RVVI state object
      if (!rvvi_state.csr.exists(csr)) begin
         `uvm_fatal("CORESB", $sformatf("CSR %s from RVFI does not exist in RVVI state interface", csr));
      end

      // Adjust CSR mask
      // Skip dcsr.nmip check in non-debug mode
      if (csr == "dcsr" && !rvfi_instr.dbg_mode) begin
         csr_mask[3] = 0;
      end

      csr_checked_cnt++;

      exp_csr_value = rvfi_instr.csrs[i].get_csr_retirement_data();

      if ((exp_csr_value & csr_mask) != rvvi_state.csr[csr]) begin
         `uvm_error("CORESB", $sformatf("CSR Mismatch, order: %0d, pc: 0x%08x, csr: %s, rvfi = 0x%08x, rvvi = 0x%08x, mask = 0x%08x",
                                        rvfi_instr.order,
                                        rvfi_instr.pc_rdata,
                                        csr,
                                        exp_csr_value,
                                        rvvi_state.csr[csr],
                                        csr_mask));
      end
   end

endfunction : check_csr

`endif // __UVME_CV32E40S_CORE_SB_SV_
