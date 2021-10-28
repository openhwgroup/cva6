//
// Copyright 2020 OpenHW Group
// Copyright 2020 Datum Technology Corporation
// Copyright 2020 Silicon Labs, Inc.
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


`ifndef __UVMA_RVFI_INSTR_MON_SV__
`define __UVMA_RVFI_INSTR_MON_SV__


/**
 * Component sampling transactions from a Clock & Reset virtual interface
 * (uvma_rvfi_instr_if).
 */
class uvma_rvfi_instr_mon_c#(int ILEN=DEFAULT_ILEN,
                             int XLEN=DEFAULT_XLEN) extends uvm_monitor;

   // Objects
   int unsigned       nret_id;
   uvma_rvfi_cfg_c    cfg;
   uvma_rvfi_cntxt_c  cntxt;

   // TLM
   uvm_analysis_port#(uvma_rvfi_instr_seq_item_c#(ILEN,XLEN))  ap;

   string log_tag = "RVFIMONLOG";

   `uvm_component_utils_begin(uvma_rvfi_instr_mon_c)
      `uvm_field_int(nret_id, UVM_DEFAULT)
      `uvm_field_object(cfg  , UVM_DEFAULT)
      `uvm_field_object(cntxt, UVM_DEFAULT)
   `uvm_component_utils_end

   /**
    * Default constructor.
    */
   extern function new(string name="uvma_rvfi_instr_mon", uvm_component parent=null);

   /**
    * 1. Ensures cfg & cntxt handles are not null.
    * 2. Builds ap.
    */
   extern virtual function void build_phase(uvm_phase phase);

   /**
    * Oversees monitoring via monitor_clk() and monitor_reset() tasks in parallel
    * forks.
    */
   extern virtual task run_phase(uvm_phase phase);

   /**
    * Monitor the instruction interface
    */
   extern virtual task monitor_rvfi_instr();

endclass : uvma_rvfi_instr_mon_c

function uvma_rvfi_instr_mon_c::new(string name="uvma_rvfi_instr_mon", uvm_component parent=null);

   super.new(name, parent);

endfunction : new


function void uvma_rvfi_instr_mon_c::build_phase(uvm_phase phase);

   super.build_phase(phase);

   if ($test$plusargs("log_rvfi"))
      set_report_id_verbosity(log_tag, UVM_HIGH);

   void'(uvm_config_db#(uvma_rvfi_cfg_c#(ILEN,XLEN))::get(this, "", "cfg", cfg));
   if (!cfg) begin
      `uvm_fatal("CFG", "Configuration handle is null")
   end

   void'(uvm_config_db#(uvma_rvfi_cntxt_c#(ILEN,XLEN))::get(this, "", "cntxt", cntxt));
   if (!cntxt) begin
      `uvm_fatal("CNTXT", "Context handle is null")
   end

   ap = new("ap", this);

endfunction : build_phase

task uvma_rvfi_instr_mon_c::run_phase(uvm_phase phase);

   super.run_phase(phase);

   if (cfg.enabled) begin
      while (1) begin
         wait (cntxt.instr_vif[nret_id].reset_n === 1'b0);
         wait (cntxt.instr_vif[nret_id].reset_n === 1'b1);

         fork begin
            fork
               monitor_rvfi_instr();
            join_none

            wait (cntxt.instr_vif[nret_id].reset_n === 1'b0);

            disable fork;
         end
         join
      end
   end
endtask : run_phase

task uvma_rvfi_instr_mon_c::monitor_rvfi_instr();
   while(1) begin
      @(cntxt.instr_vif[nret_id].mon_cb);
      if (cntxt.instr_vif[nret_id].mon_cb.rvfi_valid) begin
         uvma_rvfi_instr_seq_item_c#(ILEN,XLEN) mon_trn;

         mon_trn = uvma_rvfi_instr_seq_item_c#(ILEN,XLEN)::type_id::create("rvfi_instr_mon_trn");

         mon_trn.nret_id  = nret_id;
         mon_trn.cycle_cnt = cntxt.instr_vif[nret_id].mon_cb.cycle_cnt;
         mon_trn.order     = cntxt.instr_vif[nret_id].mon_cb.rvfi_order;
         mon_trn.insn      = cntxt.instr_vif[nret_id].mon_cb.rvfi_insn;
         mon_trn.trap      = cntxt.instr_vif[nret_id].mon_cb.rvfi_trap;
         mon_trn.halt      = cntxt.instr_vif[nret_id].mon_cb.rvfi_halt;
         mon_trn.dbg       = cntxt.instr_vif[nret_id].mon_cb.rvfi_dbg;
         mon_trn.dbg_mode  = cntxt.instr_vif[nret_id].mon_cb.rvfi_dbg_mode;
         mon_trn.intr      = cntxt.instr_vif[nret_id].mon_cb.rvfi_intr;
         $cast(mon_trn.mode, cntxt.instr_vif[nret_id].mon_cb.rvfi_mode);
         mon_trn.ixl       = cntxt.instr_vif[nret_id].mon_cb.rvfi_ixl;
         mon_trn.pc_rdata  = cntxt.instr_vif[nret_id].mon_cb.rvfi_pc_rdata;
         mon_trn.pc_wdata  = cntxt.instr_vif[nret_id].mon_cb.rvfi_pc_wdata;

         mon_trn.rs1_addr   = cntxt.instr_vif[nret_id].mon_cb.rvfi_rs1_addr;
         mon_trn.rs1_rdata  = cntxt.instr_vif[nret_id].mon_cb.rvfi_rs1_rdata;

         mon_trn.rs2_addr   = cntxt.instr_vif[nret_id].mon_cb.rvfi_rs2_addr;
         mon_trn.rs2_rdata  = cntxt.instr_vif[nret_id].mon_cb.rvfi_rs2_rdata;

         mon_trn.rs3_addr   = cntxt.instr_vif[nret_id].mon_cb.rvfi_rs3_addr;
         mon_trn.rs3_rdata  = cntxt.instr_vif[nret_id].mon_cb.rvfi_rs3_rdata;

         mon_trn.rd1_addr   = cntxt.instr_vif[nret_id].mon_cb.rvfi_rd1_addr;
         mon_trn.rd1_wdata  = cntxt.instr_vif[nret_id].mon_cb.rvfi_rd1_wdata;

         mon_trn.rd2_addr   = cntxt.instr_vif[nret_id].mon_cb.rvfi_rd2_addr;
         mon_trn.rd2_wdata  = cntxt.instr_vif[nret_id].mon_cb.rvfi_rd2_wdata;

         mon_trn.mem_addr  = cntxt.instr_vif[nret_id].mon_cb.rvfi_mem_addr;
         mon_trn.mem_rdata = cntxt.instr_vif[nret_id].mon_cb.rvfi_mem_rdata;
         mon_trn.mem_rmask = cntxt.instr_vif[nret_id].mon_cb.rvfi_mem_rmask;
         mon_trn.mem_wdata = cntxt.instr_vif[nret_id].mon_cb.rvfi_mem_wdata;
         mon_trn.mem_wmask = cntxt.instr_vif[nret_id].mon_cb.rvfi_mem_wmask;

         // Get the CSRs
         foreach (cntxt.csr_vif[csr]) begin
            uvma_rvfi_csr_seq_item_c csr_trn = uvma_rvfi_csr_seq_item_c#(XLEN)::type_id::create({csr, "_trn"});

            csr_trn.csr = csr;
            csr_trn.nret_id = nret_id;
            csr_trn.rmask = cntxt.csr_vif[csr][nret_id].mon_cb.rvfi_csr_rmask;
            csr_trn.wmask = cntxt.csr_vif[csr][nret_id].mon_cb.rvfi_csr_wmask;
            csr_trn.rdata = cntxt.csr_vif[csr][nret_id].mon_cb.rvfi_csr_rdata;
            csr_trn.wdata = cntxt.csr_vif[csr][nret_id].mon_cb.rvfi_csr_wdata;

            mon_trn.csrs[csr] = csr_trn;
         end

         // Determine if interrupt is nmi or interrupt
         mon_trn.insn_nmi        = 0;
         mon_trn.insn_interrupt  = 0;

         // FIXME:strichmo:This should be incorporated into interrupts
         if (cfg.nmi_handler_enabled && mon_trn.pc_rdata == cfg.nmi_handler_addr) begin
            bit [XLEN-1:0] csr_mcause = mon_trn.csrs["mcause"].get_csr_retirement_data();

            mon_trn.insn_nmi = 1;
            mon_trn.insn_interrupt_id = { 1'b0, csr_mcause[XLEN-2:0] };
         end
         else if (mon_trn.intr) begin
             bit [XLEN-1:0] csr_mcause = mon_trn.csrs["mcause"].get_csr_retirement_data();

            if (csr_mcause[31]) begin
               mon_trn.insn_interrupt    = 1;
               mon_trn.insn_interrupt_id = { 1'b0, csr_mcause[XLEN-2:0] };
            end
         end

         // In debug mode, detect NMIP event
         if (cfg.nmi_handler_enabled && mon_trn.csrs["dcsr"].wmask[3] && mon_trn.csrs["dcsr"].wdata[3]) begin
            mon_trn.insn_nmi = 1;
         end

         // Detect instruction bus fault
         if (cfg.insn_bus_fault_enabled &&
             mon_trn.trap &&
             mon_trn.csrs["mcause"].get_csr_retirement_data() == cfg.insn_bus_fault_cause) begin
            mon_trn.insn_bus_fault = 1;
         end

         `uvm_info(log_tag, $sformatf("%s", mon_trn.convert2string()), UVM_HIGH);

         ap.write(mon_trn);
      end
   end

endtask : monitor_rvfi_instr

`endif // __UVMA_RVFI_INSTR_MON_SV__

