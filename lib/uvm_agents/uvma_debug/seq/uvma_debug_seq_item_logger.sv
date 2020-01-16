// COPYRIGHT HEADER


`ifndef __UVMA_DEBUG_SEQ_ITEM_LOGGER_SV__
`define __UVMA_DEBUG_SEQ_ITEM_LOGGER_SV__


/**
 * Component writing Debug sequence items debug data to disk as plain text.
 */
class uvma_debug_seq_item_logger_c extends uvm_logs_seq_item_logger_c#(
   .T_TRN  (uvma_debug_seq_item_c),
   .T_CFG  (uvma_debug_cfg_c     ),
   .T_CNTXT(uvma_debug_cntxt_c   )
);
   
   `uvm_component_utils(uvma_debug_seq_item_logger_c)
   
   
   /**
    * Default constructor.
    */
   function new(string name="uvma_debug_seq_item_logger", uvm_component parent=null);
      
      super.new(name, parent);
      
   endfunction : new
   
   /**
    * Writes contents of t to disk.
    */
   virtual function void write(uvma_debug_seq_item_c t);
      
      // TODO Implement uvma_debug_seq_item_logger_c::write()
      // Ex: fwrite($sformatf(" %t | %08h | %02b | %04d | %02h |", $realtime(), t.a, t.b, t.c, t.d));
      
   endfunction : write
   
   /**
    * Writes log header to disk.
    */
   virtual function void print_header();
      
      // TODO Implement uvma_debug_seq_item_logger_c::print_header()
      // Ex: fwrite("----------------------------------------------");
      //     fwrite(" TIME | FIELD A | FIELD B | FIELD C | FIELD D ");
      //     fwrite("----------------------------------------------");
      
   endfunction : print_header
   
endclass : uvma_debug_seq_item_logger_c


/**
 * Component writing DEBUG monitor transactions debug data to disk as JavaScript Object Notation (JSON).
 */
class uvma_debug_seq_item_logger_json_c extends uvma_debug_seq_item_logger_c;
   
   `uvm_component_utils(uvma_debug_seq_item_logger_json_c)
   
   
   /**
    * Set file extension to '.json'.
    */
   function new(string name="uvma_debug_seq_item_logger_json", uvm_component parent=null);
      
      super.new(name, parent);
      fextension = "json";
      
   endfunction : new
   
   /**
    * Writes contents of t to disk.
    */
   virtual function void write(uvma_debug_seq_item_c t);
      
      // TODO Implement uvma_debug_seq_item_logger_json_c::write()
      // Ex: fwrite({"{",
      //       $sformatf("\"time\":\"%0t\",", $realtime()),
      //       $sformatf("\"a\":%h,"        , t.a        ),
      //       $sformatf("\"b\":%b,"        , t.b        ),
      //       $sformatf("\"c\":%d,"        , t.c        ),
      //       $sformatf("\"d\":%h,"        , t.c        ),
      //     "},"});
      
   endfunction : write
   
   /**
    * Empty function.
    */
   virtual function void print_header();
      
      // Do nothing: JSON files do not use headers.
      
   endfunction : print_header
   
endclass : uvma_debug_seq_item_logger_json_c


`endif // __UVMA_DEBUG_SEQ_ITEM_LOGGER_SV__
