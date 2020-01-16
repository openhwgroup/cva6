// COPYRIGHT HEADER


`ifndef __UVME_CV32_REG_BASE_VSEQ_SV__
`define __UVME_CV32_REG_BASE_VSEQ_SV__


/**
 * Abstract object from which all other CV32
 * register-oriented virtual sequences must extend.
 */
class uvme_cv32_reg_base_vseq_c extends uvme_cv32_base_vseq_c;
   
   `include "uvme_cv32_reg_ignore_all_list.sv"
   
   // Knobs
   rand bit       single_block_mode;
   uvm_reg_block  single_block     ;
   
   `uvm_object_utils_begin(uvme_cv32_reg_base_vseq_c)
      `uvm_field_int   (single_block_mode, UVM_DEFAULT)
      `uvm_field_object(single_block     , UVM_DEFAULT)
   `uvm_object_utils_end
   
   
   /**
    * Default constructor.
    */
   extern function new(string name="uvme_cv32_reg_base_vseq");
   
   /**
    * Executes run_single_block() or run_all_blocks(), depending on
    * single_block_mode.
    */
   extern virtual task body();
   
   /**
    * Pure virtual task
    */
   extern virtual task run_single_block();
   
   /**
    * Pure virtual task
    */
   extern virtual task run_all_blocks();
   
endclass : uvme_cv32_reg_base_vseq_c


`pragma protect begin


function uvme_cv32_reg_base_vseq_c::new(string name="uvme_cv32_reg_base_vseq");
   
   super.new(name);
   
endfunction : new


task uvme_cv32_reg_base_vseq_c::body();
   
   if (single_block_mode) begin
      run_single_block();
   end
   else begin
      run_all_blocks();
   end
   
endtask : body


task uvme_cv32_reg_base_vseq_c::run_single_block();
   
   `uvm_fatal("VSEQ", "Call to pure virtual task")
   
endtask : run_single_block


task uvme_cv32_reg_base_vseq_c::run_all_blocks();
   
   `uvm_fatal("VSEQ", "Call to pure virtual task")
   
endtask : run_all_blocks


`pragma protect end


`endif // __UVME_CV32_REG_BASE_VSEQ_SV__
