// COPYRIGHT HEADER


`ifndef __UVMA_RESET_MON_TRN_SV__
`define __UVMA_RESET_MON_TRN_SV__


/**
 * Object rebuilt from the Reset monitor Analog of uvma_reset_seq_item_c.
 */
class uvma_reset_mon_trn_c extends uvm_trn_mon_trn_c;
   
   // Data
   // TODO Add uvma_reset_mon_trn_c data fields
   //      Ex: logic        abc;
   //          logic [7:0]  xyz;
   
   
   `uvm_object_utils_begin(uvma_reset_mon_trn_c)
      // TODO Add UVM field utils for data fields
      //      Ex: `uvm_field_int(abc, UVM_DEFAULT)
      //          `uvm_field_int(xyz, UVM_DEFAULT)
   `uvm_object_utils_end
   
   
   /**
    * Default constructor.
    */
   extern function new(string name="uvma_reset_mon_trn");
   
endclass : uvma_reset_mon_trn_c


`pragma protect begin


function uvma_reset_mon_trn_c::new(string name="uvma_reset_mon_trn");
   
   super.new(name);
   
endfunction : new


`pragma protect end


`endif // __UVMA_RESET_MON_TRN_SV__
