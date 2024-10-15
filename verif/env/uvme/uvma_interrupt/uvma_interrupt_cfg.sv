// Copyright 2024 Thales DIS SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Ayoub JALALI (ayoub.jalali@external.thalesgroup.com)


`ifndef __UVMA_INTERRUPT_CFG_SV__
`define __UVMA_INTERRUPT_CFG_SV__


class uvma_interrupt_cfg_c extends uvm_object;
   
   // Common options
   rand bit                      enabled;
   rand uvm_active_passive_enum  is_active;

   rand bit                      cov_model_enabled;
   rand bit                      trn_log_enabled;

   rand bit                      enable_interrupt;
   bit                           interrupt_plusarg_valid;

   // Number of Interrupt vector supported
   rand int unsigned             num_irq_supported;

   // Interrupt memory ack
   rand bit [XLEN-1:0]           irq_addr;

   // enbale/disable clear mechanism
   rand bit                      enable_clear_irq;

   // Number of cycle before Timeout if the agent failed to write into irq_add
   rand int unsigned             irq_timeout;

   `uvm_object_utils_begin(uvma_interrupt_cfg_c)
      `uvm_field_int (                         enabled           , UVM_DEFAULT)
      `uvm_field_enum(uvm_active_passive_enum, is_active         , UVM_DEFAULT)   
      `uvm_field_int (                         cov_model_enabled , UVM_DEFAULT)
      `uvm_field_int (                         trn_log_enabled   , UVM_DEFAULT)
      `uvm_field_int (                         enable_interrupt  , UVM_DEFAULT)
      `uvm_field_int (                         interrupt_plusarg_valid  , UVM_DEFAULT)
      `uvm_field_int (                         num_irq_supported  , UVM_DEFAULT)
      `uvm_field_int (                         irq_addr           , UVM_DEFAULT)
      `uvm_field_int (                         enable_clear_irq   , UVM_DEFAULT)
      `uvm_field_int (                         irq_timeout        , UVM_DEFAULT)
      `uvm_object_utils_end
   

   constraint defaults_cons {   
      soft enabled           == 1;
      soft is_active         == UVM_PASSIVE;
      soft cov_model_enabled == 1;
      soft trn_log_enabled   == 1;
      
   }

  constraint default_enable_irq_cons {
      soft enable_interrupt  == 0;
      soft num_irq_supported == 2;
      soft enable_clear_irq  == 1;
      soft irq_timeout       == 10_000;
   }

   /**
    * Default constructor.
    */
   extern function new(string name="uvma_interrupt_cfg");

endclass : uvma_interrupt_cfg_c

function uvma_interrupt_cfg_c::new(string name="uvma_interrupt_cfg");
   
   super.new(name);

   // Read plusargs for defaults
   if ($test$plusargs("enable_interrupt")) begin
      interrupt_plusarg_valid = 1;
   end

endfunction : new

`endif // __UVMA_INTERRUPT_CFG_SV__
