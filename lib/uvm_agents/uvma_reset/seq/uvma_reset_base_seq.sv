// COPYRIGHT HEADER


`ifndef __UVMA_RESET_BASE_SEQ_SV__
`define __UVMA_RESET_BASE_SEQ_SV__


/**
 * Abstract object from which all other Reset agent sequences must extend.
 * Subclasses must be run on Reset sequencer (uvma_reset_sqr_c) instance.
 */
class uvma_reset_base_seq_c extends uvm_sequence#(
   .REQ(uvma_reset_seq_item_c),
   .RSP(uvma_reset_seq_item_c)
);
   
   `uvm_object_utils(uvma_reset_base_seq_c)
   `uvm_declare_p_sequencer(uvma_reset_sqr_c)
   
   
   /**
    * Default constructor.
    */
   extern function new(string name="uvma_reset_base_seq");
   
endclass : uvma_reset_base_seq_c


`pragma protect begin


function uvma_reset_base_seq_c::new(string name="uvma_reset_base_seq");
   
   super.new(name);
   
endfunction : new


`pragma protect end


`endif // __UVMA_RESET_BASE_SEQ_SV__
