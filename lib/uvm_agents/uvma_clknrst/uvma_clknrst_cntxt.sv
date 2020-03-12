// 
// Copyright 2020 OpenHW Group
// Copyright 2020 Datum Technology Corporation
// 
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
// 
//     https://solderpad.org/licenses/
// 
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
// 


`ifndef __UVMA_CLKNRST_CNTXT_SV__
`define __UVMA_CLKNRST_CNTXT_SV__


/**
 * Object encapsulating all state variables for all Clock & Reset agent
 * (uvma_clknrst_agent_c) components.
 */
class uvma_clknrst_cntxt_c extends uvm_object;
   
   // Handle to agent interface
   virtual uvma_clknrst_if  vif;
   
   // Clock Monitoring
   bit           mon_clk_lock       ; ///< Indicates that we have achieved clock lock
   realtime      mon_clk_period     ; ///< Sampled clock period
   logic         mon_clk_last_val   ; ///< Last clock value sampled
   realtime      mon_clk_last_edge  ; ///< Timestamp of last clock edge
   int unsigned  mon_clk_cycle_count; ///< Number of good clock cycles
   
   // Reset Monitoring
   logic    mon_reset_state           ; ///< Last reset edge
   realtime mon_reset_assert_timestamp; ///< Reset assertion edge timestamp
   
   // Events
   uvm_event  sample_cfg_e  ; ///< Event to trigger functional coverage sampling of cfg
   uvm_event  sample_cntxt_e; ///< Event to trigger functional coverage sampling of cntxt
   
   
   `uvm_object_utils_begin(uvma_clknrst_cntxt_c)
      `uvm_field_event(sample_cfg_e  , UVM_DEFAULT)
      `uvm_field_event(sample_cntxt_e, UVM_DEFAULT)
      
      `uvm_field_int (mon_clk_lock       , UVM_DEFAULT          )
      `uvm_field_real(mon_clk_period     , UVM_DEFAULT          )
      `uvm_field_int (mon_clk_last_val   , UVM_DEFAULT          )
      `uvm_field_real(mon_clk_last_edge  , UVM_DEFAULT          )
      `uvm_field_int (mon_clk_cycle_count, UVM_DEFAULT + UVM_DEC)
      
      `uvm_field_int (mon_reset_state           , UVM_DEFAULT)
      `uvm_field_real(mon_reset_assert_timestamp, UVM_DEFAULT)
   `uvm_object_utils_end
   
   
   /**
    * Builds events.
    */
   extern function new(string name="uvma_clknrst_cntxt");
   
   /**
    * Resets integrals to their default values.
    */
   extern function void reset();
   
endclass : uvma_clknrst_cntxt_c


function uvma_clknrst_cntxt_c::new(string name="uvma_clknrst_cntxt");
   
   super.new(name);
   
   sample_cfg_e   = new("sample_cfg_e"  );
   sample_cntxt_e = new("sample_cntxt_e");
   
   reset();
   
endfunction : new


function void uvma_clknrst_cntxt_c::reset();
   
   mon_clk_lock         =  0;
   mon_clk_period       =  0;
   mon_clk_last_val     = 'X;
   mon_clk_last_edge    =  0;
   mon_clk_cycle_count  =  0;
   
   mon_reset_state            = 0;
   mon_reset_assert_timestamp = 0;
   
endfunction : reset


`endif // __UVMA_CLKNRST_CNTXT_SV__
