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


`ifndef __UVMA_RVVI_OVPSIM_STATE_MON_SV__
`define __UVMA_RVVI_OVPSIM_STATE_MON_SV__


/**
 * Component sampling transactions from the RVVI state interface
 * (rvvi_ovpsim_state4if).
 */
class uvma_rvvi_ovpsim_state_mon_c#(int ILEN=uvma_rvvi_pkg::DEFAULT_ILEN,
                                    int XLEN=uvma_rvvi_pkg::DEFAULT_XLEN) extends uvma_rvvi_state_mon_c#(ILEN,XLEN);

   int unsigned rvvi_order = 1;

   `uvm_component_utils_begin(uvma_rvvi_ovpsim_state_mon_c)
   `uvm_component_utils_end

   /**
    * Default constructor.
    */
   extern function new(string name="uvma_rvvi_ovpsim_state_mon", uvm_component parent=null);

   /**
    * Monitor the state interface
    */
   extern virtual task monitor_rvvi_state();

endclass : uvma_rvvi_ovpsim_state_mon_c

function uvma_rvvi_ovpsim_state_mon_c::new(string name="uvma_rvvi_ovpsim_state_mon", uvm_component parent=null);

   super.new(name, parent);

   log_tag = "RVVIOVPMONLOG";

endfunction : new

task uvma_rvvi_ovpsim_state_mon_c::monitor_rvvi_state();

   uvma_rvvi_ovpsim_cntxt_c#(ILEN,XLEN) rvvi_ovpsim_cntxt;

   // Cast into the OVPSIM context to get access to the BUS interface
   if (!$cast(rvvi_ovpsim_cntxt, cntxt)) begin
      `uvm_fatal(log_tag, "Failed to cast RVVI cntxt to RVVI ovpsim_cntxt");
   end

   while(1) begin
      uvma_rvvi_state_seq_item_c#(ILEN,XLEN) mon_trn;

      @(cntxt.state_vif.notify);

      mon_trn = uvma_rvvi_state_seq_item_c#(ILEN,XLEN)::type_id::create("rvvi_ovpsim_state_mon_trn");

      mon_trn.trap     = cntxt.state_vif.trap;
      mon_trn.halt     = cntxt.state_vif.halt;
      mon_trn.intr     = cntxt.state_vif.intr;
      mon_trn.valid    = cntxt.state_vif.valid;
      mon_trn.order    = cntxt.state_vif.order;
      mon_trn.insn     = cntxt.state_vif.insn;
      mon_trn.isize    = cntxt.state_vif.isize;
      $cast(mon_trn.mode, cntxt.state_vif.mode);
      mon_trn.ixl      = cntxt.state_vif.ixl;
      mon_trn.pc       = cntxt.state_vif.pc;
      mon_trn.pcnext   = cntxt.state_vif.pcnext;

      if (!rvvi_ovpsim_cntxt.ovpsim_io_vif.deferint) begin
         mon_trn.intr = 1;
      end

      if (rvvi_ovpsim_cntxt.ovpsim_io_vif.haltreq) begin
         mon_trn.halt = 1;
      end

      // The valid bit is misleading on RVVI.  A better indicator of a "valid" retired instruction
      // (which should be checked for ISA state) is that the order field increments
      if (mon_trn.order == rvvi_order) begin
         if (!mon_trn.valid) begin
            `uvm_info(log_tag, $sformatf("Used order proxy: %0d", mon_trn.order), UVM_HIGH);
         end
         mon_trn.valid = 1;
         rvvi_order++;
      end
      else begin
         mon_trn.valid = 0;
      end

      foreach (mon_trn.x[i])
         mon_trn.x[i] = cntxt.state_vif.x[i];

      // Detect any changed GPRs
      for (int i = 0; i < 32; i++) begin
         if (cntxt.state_vif.x[i] != last_x[i]) begin
            mon_trn.gpr_update[i] = cntxt.state_vif.x[i];
            last_x[i] = cntxt.state_vif.x[i];
         end
      end

      // Monitor CSRs
      foreach (cntxt.state_vif.csr[csr]) begin
         mon_trn.csr[csr] = cntxt.state_vif.csr[csr];
      end

      `uvm_info(log_tag, $sformatf("%s", mon_trn.convert2string()), UVM_HIGH);

      ap.write(mon_trn);
   end
endtask : monitor_rvvi_state

`endif // __UVMA_RVVI_OVPSIM_STATE_MON_SV__
