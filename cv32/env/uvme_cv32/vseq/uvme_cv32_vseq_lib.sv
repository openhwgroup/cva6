// COPYRIGHT HEADER


`ifndef __UVME_CV32_VSEQ_LIB_SV__
`define __UVME_CV32_VSEQ_LIB_SV__


/**
 * Virtual sequence library for CV32 environment.
 */
class uvme_cv32_vseq_lib_c extends uvm_sequence_library#(
   .REQ(uvm_sequence_item),
   .RSP(uvm_sequence_item)
);
   
   `uvm_object_utils          (uvme_cv32_vseq_lib_c)
   `uvm_sequence_library_utils(uvme_cv32_vseq_lib_c)
   
   
   /**
    * Initializes sequence library.
    */
   extern function new(string name="uvme_cv32_vseq_lib");
   
endclass : uvme_cv32_vseq_lib_c


function uvme_cv32_vseq_lib_c::new(string name="uvme_cv32_vseq_lib");
   
   super.new(name);
   init_sequence_library();
   
   // TODO Add sequences to uvme_cv32_vseq_lib_c
   //      Ex: add_sequence(uvme_cv32_abc_vseq_c::get_type());
   
endfunction : new


`endif // __UVME_CV32_VSEQ_LIB_SV__
