// Copyright 2020 OpenHW Group
// Copyright 2021 Datum Technology Corporation
// 
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
// Licensed under the Solderpad Hardware License v 2.1 (the "License"); you may not use this file except in compliance
// with the License, or, at your option, the Apache License version 2.0.  You may obtain a copy of the License at
//                                        https://solderpad.org/licenses/SHL-2.1/
// Unless required by applicable law or agreed to in writing, any work distributed under the License is distributed on
// an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.  See the License for the
// specific language governing permissions and limitations under the License.


`ifndef __UVML_HRTBT_MON_SV__
`define __UVML_HRTBT_MON_SV__


/**
 * Component implementing a per-phase timeout that can be reset.  Enables test benches to terminate simulation only once
 * the design has achieved a quiet state, without the use of '#' delays.
 */
class uvml_hrtbt_mon_c extends uvm_component;
   
   // Configuration
   bit           enabled          = 1;
   int unsigned  startup_timeout  = uvml_hrtbt_default_startup_timeout ; ///< Time period by which a heartbeat MUST be observed
   int unsigned  heartbeat_period = uvml_hrtbt_default_heartbeat_period; ///< Timer duration for each component
   int unsigned  refresh_period   = uvml_hrtbt_default_refresh_period  ; ///< Interval between calls to eval_heartbeat()
   
   // State
   uvml_hrtbt_entry_struct  timestamps[int unsigned];
   bit                      observed_heartbeat = 0;
   bit                      phase_heartbeat    = 0;
   
   
   `uvm_component_utils_begin(uvml_hrtbt_mon_c)
      `uvm_field_int(enabled         , UVM_DEFAULT)
      `uvm_field_int(startup_timeout , UVM_DEFAULT)
      `uvm_field_int(heartbeat_period, UVM_DEFAULT)
      `uvm_field_int(refresh_period  , UVM_DEFAULT)
   `uvm_component_utils_end
   
   
   /**
    * Default constructor
    */
   extern function new(string name="uvml_hrtbt_mon", uvm_component parent=null);
   
   /**
    * Prints out configuration and ensures activity within startup_timeout.
    */
   extern virtual task run_phase(uvm_phase phase);
   
   /**
    * Each phase calls phase_loop()
    */
   extern virtual task pre_reset_phase     (uvm_phase phase);
   extern virtual task reset_phase         (uvm_phase phase);
   extern virtual task post_reset_phase    (uvm_phase phase);
   extern virtual task pre_configure_phase (uvm_phase phase);
   extern virtual task configure_phase     (uvm_phase phase);
   extern virtual task post_configure_phase(uvm_phase phase);
   extern virtual task pre_main_phase      (uvm_phase phase);
   extern virtual task main_phase          (uvm_phase phase);
   extern virtual task post_main_phase     (uvm_phase phase);
   extern virtual task pre_shutdown_phase  (uvm_phase phase);
   extern virtual task shutdown_phase      (uvm_phase phase);
   extern virtual task post_shutdown_phase (uvm_phase phase);
   
   /**
    * Holds onto an objection until all registered components' timers elapse.
    */
   extern task phase_loop(uvm_phase phase);
   
   /**
    * Processes heartbeat entries and culls out matured timestamps.
    */
   extern task eval_heartbeat();
   
   /**
    * Adds heartbeat entry for a specific component and ID.
    */
   extern function void heartbeat(uvm_component owner, int unsigned id=0);
   
   /**
    * Returns the monitor to its initialized state. 
    */
   extern function void reset();
   
   /**
    * Prints all the components currently registered with the heartbeat monitor.
    */
   extern function string print_comp_names();
   
endclass : uvml_hrtbt_mon_c


function uvml_hrtbt_mon_c::new(string name="uvml_hrtbt_mon", uvm_component parent=null);
  
  super.new(name, parent);
  
endfunction : new


task uvml_hrtbt_mon_c::run_phase(uvm_phase phase);
   
   super.run_phase(phase);
   
   if (enabled) begin
      `uvm_info("HRTBT", $sformatf("Starting heartbeat monitor with startup_timeout=%0t, heartbeat_period=%0t, refresh_period=%0t",
         startup_timeout,
         heartbeat_period,
         refresh_period
      ), UVM_NONE)
      
      #(startup_timeout * 1ns);
      if (!observed_heartbeat) begin
         `uvm_fatal("HRTBT", $sformatf("Did not observe heartbeat in first %0dns", startup_timeout))
      end
   end
   
endtask : run_phase


task uvml_hrtbt_mon_c::pre_reset_phase(uvm_phase phase);
   
   super.pre_reset_phase(phase);
   phase_loop           (phase);
   
endtask : pre_reset_phase


task uvml_hrtbt_mon_c::reset_phase(uvm_phase phase);
   
   super.reset_phase(phase);
   phase_loop       (phase);
   
endtask : reset_phase


task uvml_hrtbt_mon_c::post_reset_phase(uvm_phase phase);
   
   super.post_reset_phase(phase);
   phase_loop            (phase);
   
endtask : post_reset_phase


task uvml_hrtbt_mon_c::pre_configure_phase(uvm_phase phase);
   
   super.pre_configure_phase(phase);
   phase_loop               (phase);
   
endtask : pre_configure_phase


task uvml_hrtbt_mon_c::configure_phase(uvm_phase phase);
   
   super.configure_phase(phase);
   phase_loop           (phase);
   
endtask : configure_phase


task uvml_hrtbt_mon_c::post_configure_phase(uvm_phase phase);
   
   super.post_configure_phase(phase);
   phase_loop                (phase);
   
endtask : post_configure_phase


task uvml_hrtbt_mon_c::pre_main_phase(uvm_phase phase);
   
   super.pre_main_phase(phase);
   phase_loop          (phase);
   
endtask : pre_main_phase


task uvml_hrtbt_mon_c::main_phase(uvm_phase phase);
   
   super.main_phase(phase);
   phase_loop      (phase);
   
endtask : main_phase


task uvml_hrtbt_mon_c::post_main_phase(uvm_phase phase);
   
   super.post_main_phase(phase);
   phase_loop           (phase);
   
endtask : post_main_phase


task uvml_hrtbt_mon_c::pre_shutdown_phase(uvm_phase phase);
   
   super.pre_shutdown_phase(phase);
   phase_loop              (phase);
   
endtask : pre_shutdown_phase


task uvml_hrtbt_mon_c::shutdown_phase(uvm_phase phase);
   
   super.shutdown_phase(phase);
   phase_loop          (phase);
   
endtask : shutdown_phase


task uvml_hrtbt_mon_c::post_shutdown_phase(uvm_phase phase);
   
   super.post_shutdown_phase(phase);
   phase_loop               (phase);
   
endtask : post_shutdown_phase


task uvml_hrtbt_mon_c::phase_loop(uvm_phase phase);
   
   if (enabled) begin
      reset();
      phase.raise_objection(this);
      eval_heartbeat();
      phase.drop_objection(this);
   end
   
endtask : phase_loop


task uvml_hrtbt_mon_c::eval_heartbeat();
   
   realtime  current_maturity;
   
   forever begin
      // 1. Wait for the refresh period duration
      #(refresh_period * 1ns);
      
      // 2. Process entries, culling those that have matured
      foreach (timestamps[ii]) begin
         current_maturity = (heartbeat_period * 1ns) + timestamps[ii].timestamp;
         if (current_maturity <= $realtime()) begin
            if (timestamps[ii].owner == null) begin
               `uvm_info("HRTBT_MON", $sformatf("Removing component from heartbeat list: id (%0d)", timestamps[ii].id), UVM_DEBUG)
            end
            else begin
               `uvm_info("HRTBT_MON", $sformatf("Removing component from heartbeat list: owner (%s), id (%0d)", timestamps[ii].owner.get_full_name(), timestamps[ii].id), UVM_DEBUG)
            end
            timestamps.delete(ii);
         end
      end
      
      // 3. Exit loop if all entries are gone
      if (timestamps.size() == 0) begin
         if (phase_heartbeat) begin
            `uvm_info("HRTBT_MON", "Heartbeat count is 0. Dropping objection", UVM_NONE)
         end
         else begin
            `uvm_info("HRTBT_MON", "Heartbeat count is 0. Dropping objection", UVM_HIGH)
         end
         break;
      end
   end
   
endtask : eval_heartbeat


function void uvml_hrtbt_mon_c::heartbeat(uvm_component owner, int unsigned id=0);
   
   bit  pick_new_id = 0;
   
   if (enabled) begin
      // Must have a unique id
      if (id == 0) begin
         pick_new_id = 1;
      end
      else if (timestamps.exists(id)) begin
         pick_new_id = 1;
         `uvm_warning("HRTBT_MON", $sformatf("Specified heartbeat ID (%0d) is already in use.  A new random ID will be picked.", id))
      end
      do begin
         id = $urandom(); //@DVT_LINTER_WAIVER "MT20211214_12" disable SVTB.29.1.3.1
      end while (timestamps.exists(id));
      
      // Add entry
      timestamps[id] = '{
         owner    : owner,
         id       : id,
         timestamp: $realtime()
      };
      
      // Allows for non-components to issue heartbeats
      if (owner == null) begin
         `uvm_info("HRTBT_MON", $sformatf("Added/updated to heartbeat list: id (%0d)", id), UVM_DEBUG)
      end
      else begin
         `uvm_info("HRTBT_MON", $sformatf("Added/updated to heartbeat list: owner (%s), id (%0d)", owner.get_full_name(), id), UVM_DEBUG)
      end
      
      // Latch for startup timeout
      observed_heartbeat = 1;
      phase_heartbeat    = 1;
   end
   
endfunction : heartbeat


function void uvml_hrtbt_mon_c::reset();
   
   `uvm_info("HRTBT_MON", "Heartbeat monitor reset", UVM_DEBUG)
   timestamps.delete();
   //observed_heartbeat = 0;
   phase_heartbeat = 0;
   
endfunction : reset


function string uvml_hrtbt_mon_c::print_comp_names();
  
  string         comp_names = "";
  uvm_component  unique_comps[uvm_component];
  
  foreach (timestamps[ii]) begin
     if (timestamps[ii].owner != null) begin
       unique_comps[timestamps[ii].owner] = timestamps[ii].owner;
    end
  end
  
  foreach (unique_comps[comp]) begin
    comp_names = {comp_names, "\n", comp.get_full_name()};
  end
  
  return comp_names;
  
endfunction : print_comp_names


`endif // __UVML_HRTBT_MON_SV__
