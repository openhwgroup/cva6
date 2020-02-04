//
// Copyright 2020 OpenHW Group
// Copyright 2020 Datum Technologies
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



`ifndef __UVMT_CV32_SMOKE_TEST_SV__
`define __UVMT_CV32_SMOKE_TEST_SV__


/**
 *  The classic "smoke test".  The idea here is to bring up the environment,
 *  start the clock and reset, and see if any errors happen.  This test
 *  forces an end-of-sim via a backdoor write to the Virtual Peripherals in
 *  the dut_wrapper's mm_ram model.
 */
class uvmt_cv32_smoke_test_c extends uvmt_cv32_base_test_c;
   
   //constraint env_cfg_cons {
   //   env_cfg.enabled         == 1;
   //   env_cfg.is_active       == UVM_ACTIVE;
   //   env_cfg.trn_log_enabled == 1;
   //}
   
   `uvm_component_utils(uvmt_cv32_smoke_test_c)
   
   /**
    */
   extern function new(string name="uvmt_cv32_smoke_test", uvm_component parent=null);
   
   /**
    */
   extern virtual function void build_phase(uvm_phase phase);
   
   /**
    * 1. Assigns environment's virtual sequencer handle to vsequencer.
    * 2. Add register callback (reg_cbs) to all registers & fields.
    */
   extern virtual function void connect_phase(uvm_phase phase);
   
   /**
    */
   extern virtual task run_phase(uvm_phase phase);
   
   /**
    * Runs reset_vseq.
    */
   extern virtual task reset_phase(uvm_phase phase);
   
   /**
    * Writes contents of RAL to the DUT.
    */
   extern virtual task configure_phase(uvm_phase phase);
   
   /**
    * Prints out start of phase banners.
    */
   extern virtual function void phase_started(uvm_phase phase);
   
   /**
    * Indicates to the test bench (uvmt_cv32_tb) that the test has completed.
    * This is done by checking the properties of the phase argument.
    */
   extern virtual function void phase_ended(uvm_phase phase);
   
endclass : uvmt_cv32_smoke_test_c


function uvmt_cv32_smoke_test_c::new(string name="uvmt_cv32_smoke_test", uvm_component parent=null);
   
   super.new(name, parent);
   `uvm_info("TEST", "This is the SMOKE TEST", UVM_NONE)
   
endfunction : new


function void uvmt_cv32_smoke_test_c::build_phase(uvm_phase phase);
   
   super.build_phase(phase);
   
endfunction : build_phase


function void uvmt_cv32_smoke_test_c::connect_phase(uvm_phase phase);
   
   super.connect_phase(phase);
   
endfunction : connect_phase


task uvmt_cv32_smoke_test_c::run_phase(uvm_phase phase);
   
   // start_clk() and watchdog_timer() are called in the base_test
   super.run_phase(phase);
   
   // This a hack of the first order.  Typically the program running on
   // the core will write to the Virtual Peripheral to signal the
   // pass/fail status of the simulation.   Here, we are literally forcing it.
   phase.raise_objection(this);
   `uvm_info("TEST", "Started RUN", UVM_NONE)
   // kill some time
   repeat (1000) @(posedge clk_gen_vif.core_clock);
   // force-write "test passed"
   force uvmt_cv32_tb.dut_wrap.data_req   = 1;
   force uvmt_cv32_tb.dut_wrap.data_we    = 1;
   force uvmt_cv32_tb.dut_wrap.data_addr  = 32'h2000_0000;
   force uvmt_cv32_tb.dut_wrap.data_wdata = 123456789;
   force uvmt_cv32_tb.dut_wrap.data_rvalid = 0; // prevents "no rvalid when we the LSU is IDLE" assertion from firing
   repeat (1) @(posedge clk_gen_vif.core_clock);
   force uvmt_cv32_tb.dut_wrap.data_req   = 0;
   force uvmt_cv32_tb.dut_wrap.data_we    = 0;
   repeat (1) @(posedge clk_gen_vif.core_clock);
   force uvmt_cv32_tb.dut_wrap.data_req   = 1;
   force uvmt_cv32_tb.dut_wrap.data_we    = 1;
   // force-write "exit valid and exit value"
   force uvmt_cv32_tb.dut_wrap.data_addr  = 32'h2000_0004;
   force uvmt_cv32_tb.dut_wrap.data_wdata = 32'h5555_AAAA;
   repeat (2) @(posedge clk_gen_vif.core_clock);
   // Stop hacking at the TB
   release uvmt_cv32_tb.dut_wrap.data_rvalid;
   release uvmt_cv32_tb.dut_wrap.data_req;
   release uvmt_cv32_tb.dut_wrap.data_we;
   release uvmt_cv32_tb.dut_wrap.data_addr;
   release uvmt_cv32_tb.dut_wrap.data_wdata;
   `uvm_info("TEST", "Finished RUN", UVM_NONE)
   phase.drop_objection(this);
   
endtask : run_phase


task uvmt_cv32_smoke_test_c::reset_phase(uvm_phase phase);
   
   super.reset_phase(phase);
   
endtask : reset_phase


task uvmt_cv32_smoke_test_c::configure_phase(uvm_phase phase);
   
   uvm_status_e status;
   
   super.configure_phase(phase);
   
endtask : configure_phase


function void uvmt_cv32_smoke_test_c::phase_started(uvm_phase phase);
   
   super.phase_started(phase);
   
endfunction : phase_started


function void uvmt_cv32_smoke_test_c::phase_ended(uvm_phase phase);
   
   super.phase_ended(phase);
   
endfunction : phase_ended


`endif // __UVMT_CV32_SMOKE_TEST_SV__
