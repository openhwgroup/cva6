// 
// Copyright 2021 OpenHW Group
// Copyright 2021 Datum Technology Corporation
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
// 
// Licensed under the Solderpad Hardware License v 2.1 (the "License"); you may
// not use this file except in compliance with the License, or, at your option,
// the Apache License version 2.0. You may obtain a copy of the License at
// 
//     https://solderpad.org/licenses/SHL-2.1/
// 
// Unless required by applicable law or agreed to in writing, any work
// distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
// WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
// License for the specific language governing permissions and limitations
// under the License.
// 


`ifndef __UVME_CV32E40P_VP_VSEQ_SV__
`define __UVME_CV32E40P_VP_VSEQ_SV__


/**
 * Virtual sequence implementing the cv32e40p virtual peripherals.
 * TODO Move most of the functionality to a cv32e env base class.
 */
class uvme_cv32e40p_vp_vseq_c extends uvme_cv32e40p_base_vseq_c;
   
   // Fields
   rand int unsigned      cycle_counter_frequency; ///< Measured in picoseconds
        longint unsigned  cycle_counter = 0;
        event             interrupt_timer_start;
        int unsigned      interrupt_timer_value;
        bit [31:0]        interrupt_timer_mask = 0;
   rand int unsigned      max_latency;
        int unsigned      signature_start_address;
        int unsigned      signature_end_address;
   
   
   `uvm_object_utils_begin(uvme_cv32e40p_vp_vseq_c)
      `uvm_field_int(cycle_counter_frequency, UVM_DEFAULT + UVM_DEC)
      `uvm_field_int(cycle_counter          , UVM_DEFAULT + UVM_DEC)
      `uvm_field_int(interrupt_timer_value  , UVM_DEFAULT + UVM_DEC)
      `uvm_field_int(interrupt_timer_mask   , UVM_DEFAULT          )
      `uvm_field_int(max_latency            , UVM_DEFAULT + UVM_DEC)
      `uvm_field_int(signature_start_address, UVM_DEFAULT          )
      `uvm_field_int(signature_end_address  , UVM_DEFAULT          )
   `uvm_object_utils_end
   
   
   /**
    * Describe defaults_cons
    */
   constraint defaults_cons {
      /*soft*/ cycle_counter_frequency == 10_000; // 10ns = 100 Mhz
      /*soft*/ max_latency == 10;
   }
   
   
   /**
    * Default constructor.
    */
   extern function new(string name="uvme_cv32e40p_vp_vseq");
   
   /**
    * TODO Describe uvme_cv32e40p_vp_vseq_c::body()
    */
   extern virtual task body();
   
   /**
    * TODO Describe uvme_cv32e40p_vp_vseq_c::do_response()
    */
   extern virtual task do_response(ref uvma_obi_memory_mon_trn_c mon_req);
   
   /**
    * TODO Describe uvme_cv32e40p_vp_vseq_c::do_mem_operation()
    */
   extern virtual task do_mem_operation(ref uvma_obi_memory_mon_trn_c mon_req);
   
   /**
    * TODO Describe uvme_cv32e40p_vp_vseq_c::vp_address_range_check()
    */
   extern virtual task vp_address_range_check(ref uvma_obi_memory_mon_trn_c mon_req);
   
   /**
    * TODO Describe uvme_cv32e40p_vp_vseq_c::vp_virtual_printer()
    */
   extern virtual task vp_virtual_printer(ref uvma_obi_memory_mon_trn_c mon_req);
   
   /**
    * TODO Describe uvme_cv32e40p_vp_vseq_c::vp_interrupt_timer_control()
    */
   extern virtual task vp_interrupt_timer_control(ref uvma_obi_memory_mon_trn_c mon_req);
   
   /**
    * TODO Describe uvme_cv32e40p_vp_vseq_c::vp_debug_control()
    */
   extern virtual task vp_debug_control(ref uvma_obi_memory_mon_trn_c mon_req);
   
   /**
    * TODO Describe uvme_cv32e40p_vp_vseq_c::(vp_rand_num_gen)
    */
   extern virtual task vp_rand_num_gen(ref uvma_obi_memory_mon_trn_c mon_req);
   
   /**
    * TODO Describe uvme_cv32e40p_vp_vseq_c::vp_cycle_counter()
    */
   extern virtual task vp_cycle_counter(ref uvma_obi_memory_mon_trn_c mon_req);
   
   /**
    * TODO Describe uvme_cv32e40p_vp_vseq_c::vp_instr_mem_intf_stall_ctrl()
    */
   extern virtual task vp_instr_mem_intf_stall_ctrl(ref uvma_obi_memory_mon_trn_c mon_req);
   
   /**
    * TODO Describe uvme_cv32e40p_vp_vseq_c::vp_vp_status_flags()
    */
   extern virtual task vp_vp_status_flags(ref uvma_obi_memory_mon_trn_c mon_req);
   
   /**
    * TODO Describe uvme_cv32e40p_vp_vseq_c::vp_sig_writer()
    */
   extern virtual task vp_sig_writer(ref uvma_obi_memory_mon_trn_c mon_req);
   
   /**
    * TODO Describe uvme_cv32e40p_vp_vseq_c::irq_o()
    */
   extern virtual task irq_o();
   
   /**
    * TODO Describe uvme_cv32e40p_vp_vseq_c::add_latencies()
    */
   extern virtual function void add_latencies(ref uvma_obi_memory_slv_seq_item_c slv_rsp);
   
endclass : uvme_cv32e40p_vp_vseq_c


function uvme_cv32e40p_vp_vseq_c::new(string name="uvme_cv32e40p_vp_vseq");
   
   super.new(name);
   void'(this.randomize());
   
endfunction : new


task uvme_cv32e40p_vp_vseq_c::body();
   
   uvma_obi_memory_mon_trn_c  mon_trn;
   
   fork
      begin
         `uvm_info("VP_VSEQ", "Started", UVM_LOW)
         forever begin
            // Wait for the monitor to send us the mstr's "req" with an access request
            p_sequencer.obi_memory_data_sequencer.mon_trn_fifo.get(mon_trn);
            `uvm_info("VP_VSEQ", $sformatf("Got mon_trn:\n%s", mon_trn.sprint()), UVM_DEBUG)
            do_response(mon_trn);
         end
      end
      
      begin
         forever begin
            `uvm_info("VP_VSEQ", $sformatf("Waiting %0d ps", cycle_counter_frequency), UVM_DEBUG)
            #(cycle_counter_frequency * 1ps);
            cycle_counter++;
         end
      end
      
      begin
         forever begin
            `uvm_info("VP_VSEQ", "Waiting for interrupt_timer_start", UVM_LOW)
            @interrupt_timer_start;
                  `uvm_info("VP_VSEQ", "@interrupt_timer_start", UVM_LOW)
            fork
               begin
                  while (interrupt_timer_value > 0) begin
                     @(cntxt.obi_memory_data_cntxt.vif.clk);
                     interrupt_timer_value = (interrupt_timer_value-1) & interrupt_timer_mask;
                  end
                  `uvm_info("VP_VSEQ", "Done waiting for interrupt_timer_value to be 0", UVM_LOW)
                  irq_o();
               end
               
               begin
                  `uvm_info("VP_VSEQ", "Waiting for interrupt_timer_start", UVM_LOW)
                  @interrupt_timer_start;
                  `uvm_info("VP_VSEQ", "@interrupt_timer_start", UVM_LOW)
               end
            join_any
            disable fork;
         end
      end
   join_none
   
endtask : body


task uvme_cv32e40p_vp_vseq_c::do_response(ref uvma_obi_memory_mon_trn_c mon_req);

   uvma_obi_memory_slv_seq_item_c  slv_rsp;
   
   bit  vp_handled = 1;
   bit  error;
   
   // "remap debug code to end of memory"
   // from mm_ram.sv
   /*
   if ( (data_addr_i >= dm_halt_addr_i) &&
        (data_addr_i < (dm_halt_addr_i + (2 ** DBG_ADDR_WIDTH)) )
      )
      // remap debug code to end of memory
      data_addr_dec  = (data_addr_i[RAM_ADDR_WIDTH-1:0] - dm_halt_addr_i[RAM_ADDR_WIDTH-1:0]) + 2**RAM_ADDR_WIDTH - 2**DBG_ADDR_WIDTH;
   */
   // @MIKE: We need to translate /\ /\ into code that applies here \/ \/
   if ((mon_req.address >= 2**20) && (mon_req.address < (2**22 + (2**14)))) begin
      mon_req.address  = (mon_req.address[21:0] - 2**20) + 2**22 - 2**14;
   end
   
   
   case(mon_req.address[31:0])
      32'h1000_0000               : vp_virtual_printer          (mon_req);
      32'h1500_0000, 32'h1500_0004: vp_interrupt_timer_control  (mon_req);
      32'h1500_0008               : vp_debug_control            (mon_req);
      32'h1500_1000               : vp_rand_num_gen             (mon_req);
      32'h1500_1004               : vp_cycle_counter            (mon_req);
      32'h1600_????               : vp_instr_mem_intf_stall_ctrl(mon_req);
      32'h2000_0000, 32'h2000_0004: vp_vp_status_flags          (mon_req);
      32'h2000_0008, 32'h2000_000C,
      32'h2000_0010               : vp_sig_writer               (mon_req);
      
      default: begin
         vp_handled = 0;
      end
   endcase
   
   if (!vp_handled) begin
      `uvm_info("VP_VSEQ", $sformatf("VP not handled: x%h", mon_req.address), UVM_HIGH)
      if (0/*mon_req.address[31:0] >= 2**20*/) begin
         `uvm_info("VP_VSEQ", $sformatf("address >= 2^20: x%h", mon_req.address), UVM_LOW)
         vp_address_range_check(mon_req);
      end
      else begin
         error  = mon_req.err;
         error |= (mon_req.address > (2**`UVME_CV32E40P_MEM_SIZE));

         if (!error) begin
            do_mem_operation(mon_req);
         end
         else begin
            `uvm_create(slv_rsp)
            add_latencies(slv_rsp);
            slv_rsp.err = error;
            `uvm_info("VP_VSEQ", $sformatf("Error!\n%s", mon_req.sprint()), UVM_LOW)
            if (mon_req.access_type == UVMA_OBI_MEMORY_ACCESS_READ) begin
               // TODO: need to figured out what a proper error response is
               slv_rsp.rdata = 32'hdead_beef;
            end
            slv_rsp.set_sequencer(p_sequencer.obi_memory_data_sequencer);
            `uvm_send(slv_rsp)
         end

      end
   end
   
endtask : do_response


task uvme_cv32e40p_vp_vseq_c::do_mem_operation(ref uvma_obi_memory_mon_trn_c mon_req);

   uvma_obi_memory_slv_seq_item_c  slv_rsp;
   `uvm_create(slv_rsp)
   add_latencies(slv_rsp);
   
   `uvm_info("VP_VSEQ", $sformatf("Performing operation:\n%s", mon_req.sprint()), UVM_HIGH)
   if (mon_req.access_type == UVMA_OBI_MEMORY_ACCESS_WRITE) begin
      foreach (mon_req.be[ii]) begin
         if (mon_req.be[ii] == 1) begin
            cntxt.mem[mon_req.address+ii] = mon_req.data[ii*8+:8];
         end
      end
      `uvm_info("VP_VSEQ", $sformatf("addr: %8h;  wdata: %8h", mon_req.address, {mon_req.data[3],mon_req.data[2],mon_req.data[1],mon_req.data[0]}), UVM_NONE)
   end
   else begin
      slv_rsp.rdata[31:24] = cntxt.mem[mon_req.address+3];
      slv_rsp.rdata[23:16] = cntxt.mem[mon_req.address+2];
      slv_rsp.rdata[15:08] = cntxt.mem[mon_req.address+1];
      slv_rsp.rdata[07:00] = cntxt.mem[mon_req.address+0];
      `uvm_info("VP_VSEQ", $sformatf("addr: %8h;  rdata: %8h", mon_req.address, slv_rsp.rdata), UVM_NONE)
   end
   
   slv_rsp.set_sequencer(p_sequencer.obi_memory_data_sequencer);
   `uvm_send(slv_rsp)

endtask : do_mem_operation


task uvme_cv32e40p_vp_vseq_c::vp_address_range_check(ref uvma_obi_memory_mon_trn_c mon_req);

   uvma_obi_memory_slv_seq_item_c  slv_rsp;
   
   if (mon_req.access_type == UVMA_OBI_MEMORY_ACCESS_WRITE) begin
      `uvm_create  (slv_rsp)
      add_latencies(slv_rsp);
      `uvm_info("VP_VSEQ", $sformatf("Call to virtual peripheral 'address_range_check':\n'%s", mon_req.sprint()), UVM_LOW)
      //slv_rsp.start(p_sequencer.obi_memory_data_sequencer);
      slv_rsp.set_sequencer(p_sequencer.obi_memory_data_sequencer);
      `uvm_send(slv_rsp)
      //`uvm_fatal("VP_VSEQ", $sformatf("Ending simulation due to:\n%s", mon_req.sprint()))
      `uvm_info("VP_VSEQ", $sformatf("mon_req:\n%s", mon_req.sprint()), UVM_NONE)
   end
   else begin
      do_mem_operation(mon_req);
   end
   
endtask : vp_address_range_check


task uvme_cv32e40p_vp_vseq_c::vp_virtual_printer(ref uvma_obi_memory_mon_trn_c mon_req);

   uvma_obi_memory_slv_seq_item_c  slv_rsp;
   
   if (mon_req.access_type == UVMA_OBI_MEMORY_ACCESS_WRITE) begin
      `uvm_create  (slv_rsp)
      add_latencies(slv_rsp);
      `uvm_info("VP_VSEQ", $sformatf("Call to virtual peripheral 'virtual_printer':\n%s", mon_req.sprint()), UVM_LOW)
      $write("%c", mon_req.data[7:0]);
      //slv_rsp.start(p_sequencer.obi_memory_data_sequencer);
      slv_rsp.set_sequencer(p_sequencer.obi_memory_data_sequencer);
      `uvm_send(slv_rsp)
   end
   else begin
      do_mem_operation(mon_req);
   end
   
endtask : vp_virtual_printer


task uvme_cv32e40p_vp_vseq_c::vp_interrupt_timer_control(ref uvma_obi_memory_mon_trn_c mon_req);
   
   uvma_obi_memory_slv_seq_item_c  slv_rsp;
   
   if (mon_req.access_type == UVMA_OBI_MEMORY_ACCESS_WRITE) begin
      `uvm_create  (slv_rsp)
      add_latencies(slv_rsp);
      `uvm_info("VP_VSEQ", $sformatf("Call to virtual peripheral 'interrupt_timer_control':\n%s", mon_req.sprint()), UVM_LOW)
      if (mon_req.address == 32'h1500_0000) begin
         interrupt_timer_value = mon_req.data;
         ->interrupt_timer_start;
      end
      else if (mon_req.address == 32'h1500_0004) begin
         interrupt_timer_mask = mon_req.data;
      end
      else begin
         `uvm_info("VP_VSEQ", $sformatf("Call to virtual peripheral 'interrupt_timer_control':\n%s", mon_req.sprint()), UVM_LOW)
      end
      //slv_rsp.start(p_sequencer.obi_memory_data_sequencer);
      slv_rsp.set_sequencer(p_sequencer.obi_memory_data_sequencer);
      `uvm_send(slv_rsp)
   end
   else begin
      do_mem_operation(mon_req);
   end
   
endtask : vp_interrupt_timer_control


task uvme_cv32e40p_vp_vseq_c::vp_debug_control(ref uvma_obi_memory_mon_trn_c mon_req);
   
   uvma_obi_memory_slv_seq_item_c  slv_rsp;
   uvma_debug_seq_item_c  dbg_req;
   bit                    request_mode        = 0;
   bit                    dbg_req_value       = 0;
   bit                    rand_pulse_duration = 0;
   bit                    rand_start_delay    = 0;
   int unsigned           dbg_pulse_duration  = 0;
   int unsigned           start_delay         = 0;
   
   
   if (mon_req.access_type == UVMA_OBI_MEMORY_ACCESS_WRITE) begin
      `uvm_create  (slv_rsp)
      add_latencies(slv_rsp);
      `uvm_info("VP_VSEQ", $sformatf("Call to virtual peripheral 'vp_debug_control':\n%s", mon_req.sprint()), UVM_LOW)
      
      // Extract fields from write data
      dbg_req_value       = mon_req.data[31];
      request_mode        = mon_req.data[30];
      rand_pulse_duration = mon_req.data[29];
      dbg_pulse_duration  = mon_req.data[28:16];
      rand_start_delay    = mon_req.data[15];
      start_delay         = mon_req.data[14:0];
      
      // Start debug pulse
      fork
         begin
            if (rand_start_delay) begin
               #($urandom_range(0, start_delay) * 1ns);
            end
            else begin
               #(start_delay * 1ns);
            end
            
            if (request_mode) begin
               cntxt.debug_vif.debug_drv = dbg_req_value;
               if (rand_pulse_duration) begin
                  #($urandom_range(0, dbg_pulse_duration) * 1ns);
               end
               else begin
                  #(dbg_pulse_duration * 1ns);
               end
               cntxt.debug_vif.debug_drv = !dbg_req_value;
            end
            else begin
               cntxt.debug_vif.debug_drv = dbg_req_value;
            end
         end
      join_none
      //slv_rsp.start(p_sequencer.obi_memory_data_sequencer);
      slv_rsp.set_sequencer(p_sequencer.obi_memory_data_sequencer);
      `uvm_send(slv_rsp)
   end
   else begin
      do_mem_operation(mon_req);
   end
   
endtask : vp_debug_control


task uvme_cv32e40p_vp_vseq_c::vp_rand_num_gen(ref uvma_obi_memory_mon_trn_c mon_req);

   uvma_obi_memory_slv_seq_item_c  slv_rsp;
   
   `uvm_create  (slv_rsp)
   add_latencies(slv_rsp);
   
   if (mon_req.access_type == UVMA_OBI_MEMORY_ACCESS_READ) begin
      `uvm_info("VP_VSEQ", $sformatf("Call to virtual peripheral 'rand_num_gen':\n%s", mon_req.sprint()), UVM_LOW)
      slv_rsp.rdata = $urandom();
   end
   
   //slv_rsp.start(p_sequencer.obi_memory_data_sequencer);
   slv_rsp.set_sequencer(p_sequencer.obi_memory_data_sequencer);
   `uvm_send(slv_rsp)
   
endtask : vp_rand_num_gen


task uvme_cv32e40p_vp_vseq_c::vp_cycle_counter(ref uvma_obi_memory_mon_trn_c mon_req);

   uvma_obi_memory_slv_seq_item_c  slv_rsp;
   
   `uvm_create  (slv_rsp)
   add_latencies(slv_rsp);
   `uvm_info("VP_VSEQ", $sformatf("Call to virtual peripheral 'cycle_counter':\n%s", mon_req.sprint()), UVM_LOW)
   
   if (mon_req.access_type == UVMA_OBI_MEMORY_ACCESS_READ) begin
      slv_rsp.rdata = cycle_counter;
   end
   else if (mon_req.access_type == UVMA_OBI_MEMORY_ACCESS_WRITE) begin
      cycle_counter = 0;
   end
   
   //slv_rsp.start(p_sequencer.obi_memory_data_sequencer);
   slv_rsp.set_sequencer(p_sequencer.obi_memory_data_sequencer);
   `uvm_send(slv_rsp)
   
endtask : vp_cycle_counter


task uvme_cv32e40p_vp_vseq_c::vp_instr_mem_intf_stall_ctrl(ref uvma_obi_memory_mon_trn_c mon_req);

   uvma_obi_memory_slv_seq_item_c  slv_rsp;
   
   if (mon_req.access_type == UVMA_OBI_MEMORY_ACCESS_WRITE) begin
      `uvm_create  (slv_rsp)
      add_latencies(slv_rsp);
      `uvm_info("VP_VSEQ", $sformatf("Call to virtual peripheral 'mem_intf_stall_ctrl':\n%s", mon_req.sprint()), UVM_LOW)
      cntxt.instr_mem_delay_enabled = 1;
      //slv_rsp.start(p_sequencer.obi_memory_data_sequencer);
      slv_rsp.set_sequencer(p_sequencer.obi_memory_data_sequencer);
      `uvm_send(slv_rsp)
   end
   else begin
      do_mem_operation(mon_req);
   end
   
endtask : vp_instr_mem_intf_stall_ctrl


task uvme_cv32e40p_vp_vseq_c::vp_vp_status_flags(ref uvma_obi_memory_mon_trn_c mon_req);

   uvma_obi_memory_slv_seq_item_c  slv_rsp;
   
   
   if (mon_req.access_type == UVMA_OBI_MEMORY_ACCESS_WRITE) begin
      `uvm_create  (slv_rsp)
      add_latencies(slv_rsp);
      `uvm_info("VP_VSEQ", $sformatf("Call to virtual peripheral 'vp_status_flags':\n%s", mon_req.sprint()), UVM_LOW)
      if (mon_req.address == 32'h2000_0000) begin
         if (mon_req.data == 'd123456789) begin
            `uvm_info("VP_VSEQ", $sformatf("END OF SIM Call to virtual peripheral 'vp_status_flags':\n%s", mon_req.sprint()), UVM_LOW)
            //wait(cntxt.vp_status_vif.clk === 1);
            cntxt.vp_status_vif.tests_passed = 1;
            //wait(cntxt.vp_status_vif.clk === 0);
            //cntxt.vp_status_vif.tests_passed = 0;
         end
         else if (mon_req.data == 'd1) begin
            //wait(cntxt.vp_status_vif.clk === 1);
            cntxt.vp_status_vif.tests_failed = 1;
            //wait(cntxt.vp_status_vif.clk === 0);
            //cntxt.vp_status_vif.tests_failed = 0;
         end
      end
      else if (mon_req.address == 32'h2000_0004) begin
         //wait(cntxt.vp_status_vif.clk === 1);
         cntxt.vp_status_vif.exit_valid = 1;
         cntxt.vp_status_vif.exit_value = mon_req.data;
         //wait(cntxt.vp_status_vif.clk === 0);
         //cntxt.vp_status_vif.exit_valid = 0;
         //cntxt.vp_status_vif.exit_value = 0;
      end
      //slv_rsp.start(p_sequencer.obi_memory_data_sequencer);
      slv_rsp.set_sequencer(p_sequencer.obi_memory_data_sequencer);
      `uvm_send(slv_rsp)
   end
   else begin
      do_mem_operation(mon_req);
   end
   
endtask : vp_vp_status_flags


task uvme_cv32e40p_vp_vseq_c::vp_sig_writer(ref uvma_obi_memory_mon_trn_c mon_req);

   uvma_obi_memory_slv_seq_item_c  slv_rsp;
   string                          sig_file     = "";
   int                             sig_fd       = 0;
   bit                             use_sig_file = 0;
   
   if ($value$plusargs("signature=%s", sig_file)) begin
      sig_fd = $fopen(sig_file, "w");
      if (sig_fd == 0) begin
          `uvm_error("VP_VSEQ", $sformatf("Could not open file %s for writing", sig_file));
          use_sig_file = 0;
      end
      else begin
          use_sig_file = 1;
      end
   end
   
   if (mon_req.access_type == UVMA_OBI_MEMORY_ACCESS_WRITE) begin
      `uvm_create  (slv_rsp)
      add_latencies(slv_rsp);
      `uvm_info("VP_VSEQ", $sformatf("Call to virtual peripheral 'sig_writer':\n%s", mon_req.sprint()), UVM_LOW)
      if (mon_req.address == 32'h2000_0008) begin
         signature_start_address = mon_req.data;
      end
      else if (mon_req.address == 32'h2000_000C) begin
         signature_end_address = mon_req.data;
      end
      else if (mon_req.address == 32'h2000_0010) begin
         for (int unsigned ii=signature_start_address; ii<signature_end_address; ii++) begin
            `uvm_info("VP_VSEQ", "Dumping signature", UVM_NONE)
            if (use_sig_file) begin
               $fdisplay(sig_fd, "%x%x%x%x", cntxt.mem[ii+3], cntxt.mem[ii+2], cntxt.mem[ii+1], cntxt.mem[ii+0]);
            end
            else begin
               `uvm_info("VP_VSEQ", $sformatf("%x%x%x%x", cntxt.mem[ii+3], cntxt.mem[ii+2], cntxt.mem[ii+1], cntxt.mem[ii+0]), UVM_NONE)
            end
         end
      end
      //slv_rsp.start(p_sequencer.obi_memory_data_sequencer);
      slv_rsp.set_sequencer(p_sequencer.obi_memory_data_sequencer);
      `uvm_send(slv_rsp)
   end
   else begin
      do_mem_operation(mon_req);
   end
   
endtask : vp_sig_writer


task uvme_cv32e40p_vp_vseq_c::irq_o();
   
   `uvm_info("VP_VSEQ", "Call to irq_o()", UVM_LOW)
   wait (cntxt.intr_vif.clk === 1);
   //TODO: add control logic to define which interrupts are set/cleared
   cntxt.intr_vif.irq_drv = 32'h0000_0001;
   
endtask : irq_o


function void uvme_cv32e40p_vp_vseq_c::add_latencies(ref uvma_obi_memory_slv_seq_item_c slv_rsp);
   
   if (cntxt.instr_mem_delay_enabled) begin
      slv_rsp.gnt_latency    = $urandom_range(1,max_latency);
      slv_rsp.access_latency = $urandom_range(1,max_latency);
      slv_rsp.hold_duration  = $urandom_range(1,max_latency);
      slv_rsp.tail_length    = $urandom_range(1,max_latency);
   end
   else begin
      slv_rsp.gnt_latency    = 1;
      slv_rsp.access_latency = 1;
      slv_rsp.hold_duration  = 1;
      slv_rsp.tail_length    = 1;
   end
   
endfunction : add_latencies


`endif // __UVME_CV32E40P_VP_VSEQ_SV__
