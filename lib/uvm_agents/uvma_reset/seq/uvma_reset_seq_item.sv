// COPYRIGHT HEADER


`ifndef __UVMA_RESET_SEQ_ITEM_SV__
`define __UVMA_RESET_SEQ_ITEM_SV__


/**
 * Object created by Reset agent sequences extending uvma_reset_seq_base_c.
 */
class uvma_reset_seq_item_c extends uvm_trn_seq_item_c;
   
   // TODO Add uvma_reset_seq_item_c fields
   //      Ex: rand bit [7:0]  abc;
   
   
   `uvm_object_utils_begin(uvma_reset_seq_item_c)
      // TODO Add uvma_reset_seq_item_c UVM field utils
      //      Ex: `uvm_field_int(abc, UVM_DEFAULT)
   `uvm_object_utils_end
   
   
   // TODO Add uvma_reset_seq_item_c constraints
   //      Ex: constraint default_cons {
   //             abc inside {0,2,4,8,16,32};
   //          }
   
   
   /**
    * Default constructor.
    */
   extern function new(string name="uvma_reset_seq_item");
   
endclass : uvma_reset_seq_item_c


`pragma protect begin


function uvma_reset_seq_item_c::new(string name="uvma_reset_seq_item");
   
   super.new(name);
   
endfunction : new


`pragma protect end


`endif // __UVMA_RESET_SEQ_ITEM_SV__
