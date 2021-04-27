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

`ifndef __UVMA_RVVI_OVPSIM_DRV_SV__
`define __UVMA_RVVI_OVPSIM_DRV_SV__

/**
 * Component driving a Clock & Reset virtual interface (uvma_rvvi_ovpsim_if).
 */
class uvma_rvvi_ovpsim_drv_c#(int ILEN=uvma_rvvi_pkg::DEFAULT_ILEN, 
                              int XLEN=uvma_rvvi_pkg::DEFAULT_XLEN) extends uvma_rvvi_drv_c#(
   .ILEN(ILEN),
   .XLEN(XLEN)
);
   
   // OVPSim-based step-and-compare requires clock management
   uvma_clknrst_sqr_c clknrst_sequencer;
      
   `uvm_component_utils_begin(uvma_rvvi_ovpsim_drv_c)
   `uvm_component_utils_end
   
   /**
    * Default constructor.
    */
   extern function new(string name="uvma_rvvi_ovpsim_drv", uvm_component parent=null);
   
   /**
    * 1. Ensures cfg & cntxt handles are not null.
    * 2. Builds ap.
    */
   extern virtual function void build_phase(uvm_phase phase);

   /**
    * Initialize signals
    */
   extern virtual task reset_phase(uvm_phase phase);

   /**
    * stop the core (DUT) clock to allow the OVPSIM ISS to step
    */
   extern virtual task stop_clknrst();

   /**
    * restart the core (DUT) clock 
    */
   extern virtual task restart_clknrst();

   /**
    *  apply STEP instruction action to the RVVI
    *  must be implemented by derived implementations
    */
   extern virtual task stepi(REQ req);

   /**
    *  apply TRAP instruction action to the RVVI
    *  must be implemented by derived implementations
    */
   extern virtual task trap(REQ req);

   /**
    *  apply HALT instruction action to the RVVI
    *  must be implemented by derived implementations
    */
   extern virtual task halt(REQ req);

endclass : uvma_rvvi_ovpsim_drv_c

function uvma_rvvi_ovpsim_drv_c::new(string name="uvma_rvvi_ovpsim_drv", uvm_component parent=null);
   
   super.new(name, parent);
   
endfunction : new

function void uvma_rvvi_ovpsim_drv_c::build_phase(uvm_phase phase);
   
   super.build_phase(phase);
      
   log_tag = "RVVIOVPSIMDRV";

endfunction : build_phase

task uvma_rvvi_ovpsim_drv_c::reset_phase(uvm_phase phase);

   uvma_rvvi_ovpsim_cntxt_c#(ILEN,XLEN) rvvi_ovpsim_cntxt;
   // Cast into the OVPSIM context to get access to the BUS interface
   if (!$cast(rvvi_ovpsim_cntxt, cntxt)) begin
      `uvm_fatal(log_tag, "Failed to cast RVVI cntxt to RVVI ovpsim_cntxt");
   end

   super.reset_phase(phase);

   rvvi_ovpsim_cntxt.ovpsim_bus_vif.deferint = 1'b1;
   rvvi_ovpsim_cntxt.ovpsim_bus_vif.irq_i    = '0;

endtask : reset_phase

task uvma_rvvi_ovpsim_drv_c::stepi(REQ req);

   uvma_rvvi_ovpsim_cntxt_c#(ILEN,XLEN)            rvvi_ovpsim_cntxt;
   uvma_rvvi_ovpsim_control_seq_item_c#(ILEN,XLEN) rvvi_ovpsim_seq_item;

   // Cast into the OVPSIM context to get access to the BUS interface
   if (!$cast(rvvi_ovpsim_cntxt, cntxt)) begin
      `uvm_fatal(log_tag, "Failed to cast RVVI cntxt to RVVI ovpsim_cntxt");
   end
   if (!$cast(rvvi_ovpsim_seq_item, req)) begin
      `uvm_fatal(log_tag, "Failed to cast control_seq_item to ovpsim_control_seq_item");      
   end

   // Stop the clock
   stop_clknrst();

   // Signal an interrupt to the ISS if mcause and rvfi_intr signals external interrupt   
   // FIXME:strichmo:This should be using control rvvi interface signals
   if (rvvi_ovpsim_seq_item.intr && rvvi_ovpsim_seq_item.mcause[31]) begin   
      rvvi_ovpsim_cntxt.ovpsim_bus_vif.deferint = 1'b0;
      rvvi_ovpsim_cntxt.ovpsim_bus_vif.irq_i    = 1 << (rvvi_ovpsim_seq_item.mcause[4:0]);
      rvvi_ovpsim_cntxt.control_vif.stepi();
      @(rvvi_ovpsim_cntxt.state_vif.notify);
      rvvi_ovpsim_cntxt.ovpsim_bus_vif.deferint = 1'b1;
      @(posedge rvvi_ovpsim_cntxt.ovpsim_bus_vif.Clk);
   end

   // FIXME:HACK:strichmo:emulate rvfi_halt via PC (0x1)
   if (rvvi_ovpsim_seq_item.halt) begin
      rvvi_ovpsim_cntxt.ovpsim_bus_vif.haltreq  = 1'b1;      
      rvvi_ovpsim_cntxt.control_vif.stepi();
      @(rvvi_ovpsim_cntxt.state_vif.notify);
      rvvi_ovpsim_cntxt.ovpsim_bus_vif.haltreq = 1'b0;
      @(posedge rvvi_ovpsim_cntxt.ovpsim_bus_vif.Clk);    
   end

   // Step the ISS and wait for ISS to complete
   rvvi_ovpsim_cntxt.ovpsim_bus_vif.irq_i = rvvi_ovpsim_seq_item.mip;
   rvvi_ovpsim_cntxt.control_vif.stepi();
   @(rvvi_ovpsim_cntxt.state_vif.notify);

   // Restart the clock to the core
   restart_clknrst();

endtask : stepi

task uvma_rvvi_ovpsim_drv_c::trap(REQ req);

   `uvm_fatal("RVVIOVPSIMDRV", $sformatf("Action: %s not implemented yet", req.action.name()));

endtask : trap

task uvma_rvvi_ovpsim_drv_c::halt(REQ req);

   `uvm_fatal("RVVIOVPSIMDRV", $sformatf("Action: %s not implemented yet", req.action.name()));

endtask : halt

task uvma_rvvi_ovpsim_drv_c::stop_clknrst();

   uvma_clknrst_stop_clk_seq_c stop_clk_seq;
   stop_clk_seq = uvma_clknrst_stop_clk_seq_c::type_id::create("stop_clk_seq");
   assert(stop_clk_seq.randomize());
   stop_clk_seq.start(clknrst_sequencer);

endtask : stop_clknrst

task uvma_rvvi_ovpsim_drv_c::restart_clknrst();

   uvma_clknrst_restart_clk_seq_c restart_clk_seq;
   restart_clk_seq = uvma_clknrst_restart_clk_seq_c::type_id::create("restart_clk_seq");
   assert(restart_clk_seq.randomize());
   restart_clk_seq.start(clknrst_sequencer);

endtask : restart_clknrst

`endif // __UVMA_RVVI_OVPSIM_DRV_SV__

