// COPYRIGHT HEADER


`ifndef __UVMT_CV32E40P_VSEQ_LIB_SV__
`define __UVMT_CV32E40P_VSEQ_LIB_SV__


/**
 * Object holding virtual sequence library for CV32E40P test cases.
 */
class uvmt_cv32e40p_vseq_lib_c extends uvm_sequence_library#(
   .REQ(uvm_sequence_item),
   .RSP(uvm_sequence_item)
);
   
   `uvm_object_utils          (uvmt_cv32e40p_vseq_lib_c)
   `uvm_sequence_library_utils(uvmt_cv32e40p_vseq_lib_c)
   
   
   /**
    * Initializes sequence library.
    */
   extern function new(string name="uvmt_cv32e40p_vseq_lib");
   
endclass : uvmt_cv32e40p_vseq_lib_c


function uvmt_cv32e40p_vseq_lib_c::new(string name="uvmt_cv32e40p_vseq_lib");
   
   super.new(name);
   init_sequence_library();
   
   // TODO Add sequences to uvmt_cv32e40p_vseq_lib_c
   //      Ex: add_sequence(uvmt_cv32e40p_abc_vseq_c::get_type());
   
endfunction : new


`endif // __UVMT_CV32E40P_VSEQ_LIB_SV__
