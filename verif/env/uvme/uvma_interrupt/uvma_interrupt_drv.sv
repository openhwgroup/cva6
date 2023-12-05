// Copyright 2024 Thales DIS SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Ayoub JALALI (ayoub.jalali@external.thalesgroup.com)

`ifndef __UVMA_INTERRUPT_DRV_SV__
`define __UVMA_INTERRUPT_DRV_SV__

/**
 * Component driving interrupt virtual interface (uvma_interrupt_if).
 */
class uvma_interrupt_drv_c extends uvm_driver#(uvma_interrupt_seq_item_c);

   // Objects
   uvma_interrupt_cfg_c                           cfg;
   uvma_interrupt_cntxt_c                         cntxt;

   uvma_interrupt_seq_item_c req_item;

   `uvm_component_utils_begin(uvma_interrupt_drv_c)
      `uvm_field_object(cfg  , UVM_DEFAULT)
      `uvm_field_object(cntxt, UVM_DEFAULT)
   `uvm_component_utils_end

   /**
    * Default constructor.
    */
   extern function new(string name="uvma_interrupt_drv", uvm_component parent=null);

   /**
    * 1. Ensures cfg & cntxt handles are not null.
    * 2. Builds ap.
    */
   extern virtual function void build_phase(uvm_phase phase);

   /**
    * Obtains the reqs from the sequence item port and calls drv_irq()
    */
   extern virtual task run_phase(uvm_phase phase);

   /**
    * Drives the virtual interface's (cntxt.interrupt_vif) signals using req's contents.
    */
   extern task drv_irq(uvma_interrupt_seq_item_c req);

   /**
    * Assert only one interrupt each time
    */
   extern task assert_irq_one_by_one(uvma_interrupt_seq_item_c req);

   /**
    * Assert one or more interrupt each time
    */
   extern task assert_irq_more(uvma_interrupt_seq_item_c req);

   /**
    * Randomize interrupt signal
    */
   extern task assert_irq_randomize(uvma_interrupt_seq_item_c req);

endclass : uvma_interrupt_drv_c

function uvma_interrupt_drv_c::new(string name="uvma_interrupt_drv", uvm_component parent=null);

   super.new(name, parent);

endfunction : new


function void uvma_interrupt_drv_c::build_phase(uvm_phase phase);

   super.build_phase(phase);

   void'(uvm_config_db#(uvma_interrupt_cfg_c)::get(this, "", "cfg", cfg));
   if (cfg == null) begin
      `uvm_fatal("CFG", "Configuration handle is null")
   end
   uvm_config_db#(uvma_interrupt_cfg_c)::set(this, "*", "cfg", cfg);

   void'(uvm_config_db#(uvma_interrupt_cntxt_c)::get(this, "", "cntxt", cntxt));
   if (cntxt == null) begin
      `uvm_fatal("CNTXT", "Context handle is null")
   end
   uvm_config_db#(uvma_interrupt_cntxt_c)::set(this, "*", "cntxt", cntxt);
   
   req_item = uvma_interrupt_seq_item_c::type_id::create("req_item");

endfunction : build_phase

task uvma_interrupt_drv_c::run_phase(uvm_phase phase);

   super.run_phase(phase);

   //Initial the interface before the CPU start
   cntxt.interrupt_vif.irq <= 'h0;

   if(!cfg.enable_interrupt) begin
      `uvm_warning(get_type_name(), "Driving Interrupt reqeust is disabled");
      return;
   end

   forever begin

      seq_item_port.get_next_item(req_item);  
      drv_irq(req_item);
      seq_item_port.item_done(); 
  
   end

endtask : run_phase

task uvma_interrupt_drv_c::drv_irq(uvma_interrupt_seq_item_c req);
   `uvm_info(get_type_name(), $sformatf("Driving:\n%s", req.sprint()), UVM_HIGH);

   case (req.irq_cntrl)
      UVMA_INTERRUPT_ONE_BY_ONE: begin
         assert_irq_one_by_one(req);
      end
      UVMA_INTERRUPT_MORE_THAN_ONE: begin
         assert_irq_more(req);
      end
      UVMA_INTERRUPT_RANDOMIZE: begin
         assert_irq_randomize(req);
      end
   endcase

endtask : drv_irq

task uvma_interrupt_drv_c::assert_irq_one_by_one(uvma_interrupt_seq_item_c req);

   #req.irq_delay;
   cntxt.interrupt_vif.irq <= req.interrupt_valid;
   `uvm_info(get_type_name(), $sformatf("Assert interrupt channel(s) %0b", req.interrupt_valid), UVM_HIGH)
   #req.irq_time;
   cntxt.interrupt_vif.irq <= 'h0;

endtask : assert_irq_one_by_one

task uvma_interrupt_drv_c::assert_irq_more(uvma_interrupt_seq_item_c req);

   #req.irq_delay;
   cntxt.interrupt_vif.irq <= req.interrupt_valid;
   #req.irq_time;
   cntxt.interrupt_vif.irq <= 'h0;

endtask : assert_irq_more

task uvma_interrupt_drv_c::assert_irq_randomize(uvma_interrupt_seq_item_c req);

   repeat(5) begin
      #req.irq_delay;
      cntxt.interrupt_vif.irq <= req.interrupt_valid;
      #req.irq_time;
   end

   cntxt.interrupt_vif.irq <= 'h0;
   cfg.calc_random_req_latency();

endtask : assert_irq_randomize

`endif // __UVMA_INTERRUPT_DRV_SV__
