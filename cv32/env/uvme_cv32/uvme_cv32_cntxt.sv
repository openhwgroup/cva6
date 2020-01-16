// COPYRIGHT HEADER


`ifndef __UVME_CV32_CNTXT_SV__
`define __UVME_CV32_CNTXT_SV__


/**
 * Object encapsulating all state variables for CV32 environment
 * (uvme_cv32_env_c) components.
 */
class uvme_cv32_cntxt_c extends uvm_object;
   
   // Sub-environments context handles
   uvme_${sub_env_name}_cntxt_c  ${sub_env_name}_cntxt;
   
   // Agent context handles
   uvma_debug_cntxt_c  debug_cntxt;
   uvma_reset_cntxt_c  reset_cntxt;
   
   // TODO Add scoreboard context handles
   //      Ex: uvme_cv32_sb_cntxt_c  sb_egress_cntxt;
   //          uvme_cv32_sb_cntxt_c  sb_ingress_cntxt;
   
   // Events
   uvm_event  sample_cfg_e;
   uvm_event  sample_cntxt_e;
   
   
   `uvm_object_utils_begin(uvme_cv32_cntxt_c)
      `uvm_field_object(${sub_env_name}_cntxt, UVM_DEFAULT)
      
      `uvm_field_object(debug_cntxt, UVM_DEFAULT)
      `uvm_field_object(reset_cntxt, UVM_DEFAULT)
      
      // TODO Add scoreboard context field macros
      //      Ex: `uvm_field_object(sb_egress_cntxt , UVM_DEFAULT)
      //          `uvm_field_object(sb_ingress_cntxt, UVM_DEFAULT)
      
      `uvm_field_event(sample_cfg_e  , UVM_DEFAULT)
      `uvm_field_event(sample_cntxt_e, UVM_DEFAULT)
   `uvm_object_utils_end
   
   
   /**
    * Builds events and sub-context objects.
    */
   extern function new(string name="uvme_cv32_cntxt");
   
endclass : uvme_cv32_cntxt_c


`pragma protect begin


function uvme_cv32_cntxt_c::new(string name="uvme_cv32_cntxt");
   
   super.new(name);
   
   debug_cntxt = uvma_debug_cntxt_c::type_id::create("debug_cntxt");
   reset_cntxt = uvma_reset_cntxt_c::type_id::create("reset_cntxt");
   
   // TODO Create uvme_cv32_cntxt_c scoreboard context objects
   //      Ex: sb_egress_cntxt  = uvma_cv32_sb_cntxt_c::type_id::create("sb_egress_cntxt" );
   //          sb_ingress_cntxt = uvma_cv32_sb_cntxt_c::type_id::create("sb_ingress_cntxt");
   
   sample_cfg_e   = new("sample_cfg_e"  );
   sample_cntxt_e = new("sample_cntxt_e");
   
endfunction : new


`pragma protect end


`endif // __UVME_CV32_CNTXT_SV__
