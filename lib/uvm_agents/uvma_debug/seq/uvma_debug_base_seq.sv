// COPYRIGHT HEADER


`ifndef __UVMA_DEBUG_BASE_SEQ_SV__
`define __UVMA_DEBUG_BASE_SEQ_SV__


/**
 * Abstract object from which all other Debug agent sequences must extend.
 * Subclasses must be run on Debug sequencer (uvma_debug_sqr_c) instance.
 */
class uvma_debug_base_seq_c extends uvm_sequence#(
   .REQ(uvma_debug_seq_item_c),
   .RSP(uvma_debug_seq_item_c)
);
   
   `uvm_object_utils(uvma_debug_base_seq_c)
   `uvm_declare_p_sequencer(uvma_debug_sqr_c)
   
   
   /**
    * Default constructor.
    */
   extern function new(string name="uvma_debug_base_seq");
   
endclass : uvma_debug_base_seq_c


`pragma protect begin


function uvma_debug_base_seq_c::new(string name="uvma_debug_base_seq");
   
   super.new(name);
   
endfunction : new


`pragma protect end


`endif // __UVMA_DEBUG_BASE_SEQ_SV__
