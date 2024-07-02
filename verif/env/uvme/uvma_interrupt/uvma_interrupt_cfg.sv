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

   // Interrupt request latency modes
   rand uvma_interrupt_drv_req_enum  drv_req_mode;
   rand int unsigned                 drv_req_fixed_latency;
   rand int unsigned                 drv_req_random_latency_min;
   rand int unsigned                 drv_req_random_latency_max;

   `uvm_object_utils_begin(uvma_interrupt_cfg_c)
      `uvm_field_int (                         enabled           , UVM_DEFAULT)
      `uvm_field_enum(uvm_active_passive_enum, is_active         , UVM_DEFAULT)   
      `uvm_field_int (                         cov_model_enabled , UVM_DEFAULT)
      `uvm_field_int (                         trn_log_enabled   , UVM_DEFAULT)
      `uvm_field_int (                         enable_interrupt  , UVM_DEFAULT)
      `uvm_field_int (                         interrupt_plusarg_valid  , UVM_DEFAULT)
      `uvm_field_enum(uvma_interrupt_drv_req_enum, drv_req_mode  , UVM_DEFAULT)   
      `uvm_field_int (                         drv_req_fixed_latency , UVM_DEFAULT)
      `uvm_field_int (                         drv_req_random_latency_min , UVM_DEFAULT)
      `uvm_field_int (                         drv_req_random_latency_max , UVM_DEFAULT)
      `uvm_object_utils_end
   

   constraint defaults_cons {   
      soft enabled           == 1;
      soft is_active         == UVM_PASSIVE;
      soft cov_model_enabled == 1;
      soft trn_log_enabled   == 1;
      
   }

  constraint default_enable_irq_cons {
      soft enable_interrupt == 0;
   }

  constraint default_drive_req_mode_cons {
      soft drv_req_mode == UVMA_INTERRUPT_DRV_REQ_MODE_FIXED_LATENCY;
   }

  constraint default_fixed_req_latency_cons {
      soft drv_req_fixed_latency inside {[250:300]};
   }

   constraint valid_random_req_latency_cons {
      drv_req_random_latency_min < drv_req_random_latency_max;
   }

   constraint default_random_latency_cons {
      soft drv_req_random_latency_min inside {[50:100]};
      soft drv_req_random_latency_max inside {[150:200]};
   }

   /**
    * Default constructor.
    */
   extern function new(string name="uvma_interrupt_cfg");

   /**
    * Calculate a new random gnt latency
    */
   extern function int unsigned calc_random_req_latency();

endclass : uvma_interrupt_cfg_c

function uvma_interrupt_cfg_c::new(string name="uvma_interrupt_cfg");
   
   super.new(name);

   // Read plusargs for defaults
   if ($test$plusargs("enable_interrupt")) begin
      interrupt_plusarg_valid = 1;
   end

endfunction : new

function int unsigned uvma_interrupt_cfg_c::calc_random_req_latency();

   int unsigned req_latency;

   case (drv_req_mode)
      UVMA_INTERRUPT_DRV_REQ_MODE_CONSTANT      : req_latency = 0;
      UVMA_INTERRUPT_DRV_REQ_MODE_FIXED_LATENCY : req_latency = drv_req_fixed_latency;
      UVMA_INTERRUPT_DRV_REQ_MODE_RANDOM_LATENCY: begin
         req_latency = $urandom_range(drv_req_random_latency_min, drv_req_random_latency_max);
      end
   endcase

   return req_latency;

endfunction : calc_random_req_latency

`endif // __UVMA_INTERRUPT_CFG_SV__
