// COPYRIGHT HEADER


`ifndef __UVMT_CV32_BIT_BASH_TEST_SV__
`define __UVMT_CV32_BIT_BASH_TEST_SV__


/**
 * Checks that all writable registers specified in the RAL are writable in the
 * DUT.
 */
class uvmt_cv32_bit_bash_test_c extends uvmt_cv32_reg_base_test_c;
   
   // Sequences
   rand uvme_cv32_reg_bit_bash_vseq_c  bit_bash_vseq;
   
   
   `uvm_component_utils(uvmt_cv32_bit_bash_test_c)
   
   
   constraint defaults_cons {
      soft bit_bash_vseq.single_block_mode == 1;
   }
   
   
   /**
    * Creates bit_bash_vseq.
    */
   extern function new(string name="uvmt_cv32_bit_bash_test", uvm_component parent=null);
   
   /**
    * Runs bit_bash_vseq on vsequencer.
    */
   extern virtual task main_phase(uvm_phase phase);
   
endclass : uvmt_cv32_bit_bash_test_c


function uvmt_cv32_bit_bash_test_c::new(string name="uvmt_cv32_bit_bash_test", uvm_component parent=null);
   
   super.new(name, parent);
   
   bit_bash_vseq = uvme_cv32_reg_bit_bash_vseq_c::type_id::create("bit_bash_vseq");
   
endfunction : new


task uvmt_cv32_bit_bash_test_c::main_phase(uvm_phase phase);
   
   super.main_phase(phase);
   
   `uvm_info("TEST", $sformatf("Starting bit bash virtual sequence:\n%s", bit_bash_vseq.sprint()), UVM_NONE)
   bit_bash_vseq.single_block = test_cfg.cli_selected_block;
   bit_bash_vseq.start(vsequencer);
   `uvm_info("TEST", "Finished bit bash virtual sequence", UVM_NONE)
   
endtask : main_phase


`endif // __UVMT_CV32_BIT_BASH_TEST_SV__
