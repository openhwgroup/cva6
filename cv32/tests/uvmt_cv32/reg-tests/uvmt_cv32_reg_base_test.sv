// COPYRIGHT HEADER


`ifndef __UVMT_CV32_REG_BASE_TEST_SV__
`define __UVMT_CV32_REG_BASE_TEST_SV__


/**
 * Test from which all other CV32 register-oriented tests must
 * extend.
 */
class uvmt_cv32_reg_base_test_c extends uvmt_cv32_base_test_c;
   
   `uvm_component_utils(uvmt_cv32_reg_base_test_c)
   
   /**
    * Default constructor.
    */
   extern function new(string name="uvmt_cv32_reg_base_test", uvm_component parent=null);
   
endclass : uvmt_cv32_reg_base_test_c


function uvmt_cv32_reg_base_test_c::new(string name="uvmt_cv32_reg_base_test", uvm_component parent=null);
   
   super.new(name, parent);
   
endfunction : new


`endif // __UVMT_CV32_REG_BASE_TEST_SV__
