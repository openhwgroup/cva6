// Copyright 2024 Thales DIS SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Ayoub JALALI (ayoub.jalali@external.thalesgroup.com)


`ifndef __UVMA_INTERRUPT_SEQ_SV__
`define __UVMA_INTERRUPT_SEQ_SV__

class uvma_interrupt_seq_c extends uvma_interrupt_base_seq_c;

   `uvm_object_utils(uvma_interrupt_seq_c)
   `uvm_declare_p_sequencer(uvma_interrupt_sqr_c)

   bit [XLEN-1:0] IRQ_ACK_VALUE = 'h0;
   int unsigned   IRQ_TIMEOUT;

   /**
    * Default constructor.
    */
   extern function new(string name="uvma_interrupt_seq");

   extern virtual task automatic clear_irq_channel(int channel, uvma_interrupt_seq_item_c  req_item);

   extern virtual task body();

endclass : uvma_interrupt_seq_c

task automatic uvma_interrupt_seq_c::clear_irq_channel(int channel, uvma_interrupt_seq_item_c  req_item);

   IRQ_TIMEOUT = cfg.irq_timeout;
   while(1) begin
      IRQ_ACK_VALUE = cntxt.mem.read(cfg.irq_addr);
      if (IRQ_ACK_VALUE[channel]) begin
        req_item.interrupt_vector[channel] = 1'h0;
        `uvm_info(get_type_name(), $sformatf("Clear interrupt channel N-%2d -> mem = 0x%x",channel, IRQ_ACK_VALUE), UVM_NONE);
        IRQ_TIMEOUT = cfg.irq_timeout;
        break;
      end
      else begin
        if (IRQ_TIMEOUT == 0) begin
          `uvm_fatal(get_type_name(), $sformatf("Timeout : failed to write into irq_add to clear pending interrupts"));
        end
        IRQ_TIMEOUT = IRQ_TIMEOUT - 1;
      end
      @(posedge cntxt.interrupt_vif.clk);
   end

endtask : clear_irq_channel

function uvma_interrupt_seq_c::new(string name="uvma_interrupt_seq");

   super.new(name);

endfunction : new

task uvma_interrupt_seq_c::body();

  if (cfg.enable_interrupt) begin
      for (int i = 0; i < cfg.num_irq_supported; i++) begin
          automatic int ii = i;
          automatic uvma_interrupt_seq_item_c  req_item_c;
            fork begin
               forever begin
                      // Set interrupt request per channel
                      req_item_c = uvma_interrupt_seq_item_c::type_id::create("req_item_c");
                      start_item(req_item_c);
                      if (!req_item_c.randomize() with {
                         req_item_c.interrupt_vector[ii] inside {0 , 1};
                         req_item_c.interrupt_channel_mask == 1<<ii;
                      })
                      `uvm_error(get_type_name(), "req_item_c.randomize() failed!")
                      finish_item(req_item_c);
                      #req_item_c.irq_set_delay;
                      // Clear interrupt request per channel
                      if (req_item_c.interrupt_vector[ii]) begin
                         req_item_c = uvma_interrupt_seq_item_c::type_id::create("req_item_c");
                         if (cfg.enable_clear_irq) begin
                            clear_irq_channel(ii, req_item_c);
                            start_item(req_item_c);
                            finish_item(req_item_c);
                            #req_item_c.irq_clear_delay;
                         end
                         else begin
                           req_item_c.interrupt_vector[ii] = 'h0;
                           start_item(req_item_c);
                           finish_item(req_item_c);
                           #req_item_c.irq_clear_delay;
                         end
                      end
                   end
               end
         join_none
      end
      wait fork;
  end
  else begin
     `uvm_info(get_type_name(), $sformatf("Interrupts are disabled"), UVM_NONE);
  end

endtask : body

`endif // __UVMA_INTERRUPT_SEQ_SV__
