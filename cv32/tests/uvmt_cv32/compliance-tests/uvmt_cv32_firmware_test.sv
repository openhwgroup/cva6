//
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
// 



`ifndef __UVMT_CV32_FIRMWARE_TEST_SV__
`define __UVMT_CV32_FIRMWARE_TEST_SV__


/**
 *  CV32E40P "firmware" test.  
 *  This class relies on a pre-existing "firmware" file written in C and/or
 *  RISC-V assembly code.  This class will invoke the riscv-gcc-toolchain to
 *  translate the firmware into a "hexfile" that is read into the CV32E40P
 *  instruction memory in the testbench module.
 *
 *  This class doesn't care what the firmware does, it mearly compiles it.
 *
 */
class uvmt_cv32_firmware_test_c extends uvmt_cv32_base_test_c;
   
   //constraint env_cfg_cons {
   //   env_cfg.enabled         == 1;
   //   env_cfg.is_active       == UVM_ACTIVE;
   //   env_cfg.trn_log_enabled == 1;
   //}

   constraint test_type_cons {
     test_cfg.tpt == PREEXISTING_SELFCHECKING;
   }
   
   
   `uvm_component_utils(uvmt_cv32_firmware_test_c)
   
   /**
    */
   extern function new(string name="uvmt_cv32_firmware_test", uvm_component parent=null);
   
   /**
    * Runs reset_vseq.
    */
   extern virtual task reset_phase(uvm_phase phase);
   
   /**
    * Loads the test program (the "firmware") into memory.
    */
   extern virtual task configure_phase(uvm_phase phase);
   
   /**
    *  Enable program execution, wait for completion.
    */
   extern virtual task run_phase(uvm_phase phase);
   
   /**
    *  Start the interrupt sequencer to apply random interrupts during test
    */
   extern virtual task irq_noise();

endclass : uvmt_cv32_firmware_test_c


function uvmt_cv32_firmware_test_c::new(string name="uvmt_cv32_firmware_test", uvm_component parent=null);
   
   super.new(name, parent);
   `uvm_info("TEST", "This is the FIRMWARE TEST", UVM_NONE)
   
endfunction : new


task uvmt_cv32_firmware_test_c::reset_phase(uvm_phase phase);
   
   super.reset_phase(phase);
   
endtask : reset_phase


task uvmt_cv32_firmware_test_c::configure_phase(uvm_phase phase);
   
   //string firmware;
   //int    fd;
   
   super.configure_phase(phase);

   /*
   ** Moved to uvmt_cv32_dut_wrap.sv to avoid XMRs across packages.
   ** TODO: delete all this once you are confident of the approach.
   **
    // Load the pre-compiled firmware
    if($value$plusargs("firmware=%s", firmware)) begin
      // First, check if it exists...
      fd = $fopen (firmware, "r");   
      if (fd)  `uvm_info("TEST", $sformatf("%s was opened successfully : (fd=%0d)", firmware, fd), UVM_NONE)
      else     `uvm_fatal("TEST", $sformatf("%s was NOT opened successfully : (fd=%0d)", firmware, fd))
      $fclose(fd);
      // Now load it...
      `uvm_info("TEST", $sformatf("loading firmware %0s", firmware), UVM_NONE)
      $readmemh(firmware, uvmt_cv32_tb.dut_wrap.ram_i.dp_ram_i.mem);
    end
    else begin
      `uvm_error("TEST", "No firmware specified!")
    end
   */

endtask : configure_phase


task uvmt_cv32_firmware_test_c::run_phase(uvm_phase phase);
   
   // start_clk() and watchdog_timer() are called in the base_test
   super.run_phase(phase);
   
   if ($test$plusargs("gen_irq_noise")) begin
    fork    
      irq_noise();
    join_none
   end

   phase.raise_objection(this);
   @(posedge env_cntxt.clknrst_cntxt.vif.reset_n);
   repeat (33) @(posedge env_cntxt.clknrst_cntxt.vif.clk);
   core_cntrl_vif.go_fetch(); // Assert the Core's fetch_en
   `uvm_info("TEST", "Started RUN", UVM_NONE)
   // The firmware is expected to write exit status and pass/fail indication to the Virtual Peripheral
   wait (
          (vp_status_vif.exit_valid    == 1'b1) ||
          (vp_status_vif.tests_failed  == 1'b1) ||
          (vp_status_vif.tests_passed  == 1'b1)
        );
   repeat (100) @(posedge env_cntxt.clknrst_cntxt.vif.clk);
   //TODO: exit_value will not be valid - need to add a latch in the vp_status_vif
   `uvm_info("TEST", $sformatf("Finished RUN: exit status is %0h", vp_status_vif.exit_value), UVM_NONE)
   phase.drop_objection(this);
   
endtask : run_phase

task uvmt_cv32_firmware_test_c::irq_noise();
  `uvm_info("TEST", "Starting IRQ Noise thread in UVM test", UVM_NONE);
  while (1) begin
    uvme_cv32_interrupt_noise_c interrupt_noise_vseq;

    interrupt_noise_vseq = uvme_cv32_interrupt_noise_c::type_id::create("interrupt_noise_vseqr");
    assert(interrupt_noise_vseq.randomize() with {
      reserved_irq_mask == 32'h0;
    });
    interrupt_noise_vseq.start(vsequencer);
    break;
  end
endtask : irq_noise


`endif // __UVMT_CV32_FIRMWARE_TEST_SV__
