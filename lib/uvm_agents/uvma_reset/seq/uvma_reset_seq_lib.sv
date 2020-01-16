// COPYRIGHT HEADER


`ifndef __UVMA_RESET_SEQ_LIB_SV__
`define __UVMA_RESET_SEQ_LIB_SV__


/**
 * Object holding sequence library for Reset agent.
 */
class uvma_reset_seq_lib_c extends uvm_sequence_library#(
   .REQ(uvma_reset_seq_item_c),
   .RSP(uvma_reset_seq_item_c)
);
   
   `uvm_object_utils          (uvma_reset_seq_lib_c)
   `uvm_sequence_library_utils(uvma_reset_seq_lib_c)
   
   
   /**
    * Initializes sequence library
    */
   extern function new(string name="uvma_reset_seq_lib");
   
endclass : uvma_reset_seq_lib_c


function uvma_reset_seq_lib_c::new(string name="uvma_reset_seq_lib");
   
   super.new(name);
   init_sequence_library();
   
   // TODO Add sequences to uvma_reset_seq_lib_c
   //      Ex: add_sequence(uvma_reset_abc_seq_c::get_type());
   
endfunction : new


`endif // __UVMA_RESET_SEQ_LIB_SV__
