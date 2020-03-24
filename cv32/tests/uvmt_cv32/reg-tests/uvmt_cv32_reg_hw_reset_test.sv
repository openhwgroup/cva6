// COPYRIGHT HEADER


`ifndef __UVMT_CV32_HW_RESET_TEST_SV__
`define __UVMT_CV32_HW_RESET_TEST_SV__


/**
 * Checks that the reset value specified for registers in the RAL matches what
 * is in the DUT.
 */
class uvmt_cv32_hw_reset_test_c extends uvmt_cv32_reg_base_test_c;
   
   // Sequences
   rand uvme_cv32_reg_hw_reset_vseq_c  hw_reset_vseq;
   
   
   `uvm_component_utils(uvmt_cv32_hw_reset_test_c)
   
   
   constraint defaults_cons {
      soft hw_reset_vseq.single_block_mode == 1;
   }
   
   
   /**
    * Creates hw_reset_vseq.
    */
   extern function new(string name="uvmt_cv32_hw_reset_test", uvm_component parent=null);
   
   /**
    * Runs hw_reset_vseq on vsequencer.
    */
   extern virtual task main_phase(uvm_phase phase);
   
endclass : uvmt_cv32_hw_reset_test_c


function uvmt_cv32_hw_reset_test_c::new(string name="uvmt_cv32_hw_reset_test", uvm_component parent=null);
   
   super.new(name, parent);
   
   hw_reset_vseq = uvme_cv32_reg_hw_reset_vseq_c::type_id::create("hw_reset_vseq");
   
endfunction : new


task uvmt_cv32_hw_reset_test_c::main_phase(uvm_phase phase);
   
   super.main_phase(phase);
   
   `uvm_info("TEST", $sformatf("Starting hw_reset virtual sequence:\n%s", hw_reset_vseq.sprint()), UVM_NONE)
   //hw_reset_vseq.single_block = test_cfg.cli_selected_block;
   hw_reset_vseq.start(vsequencer);
   `uvm_info("TEST", "Finished hw_reset virtual sequence", UVM_NONE)
   
endtask : main_phase


`endif // __UVMT_CV32_HW_RESET_TEST_SV__
