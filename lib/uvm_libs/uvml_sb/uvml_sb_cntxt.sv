// 
// Copyright 2020 OpenHW Group
// Copyright 2020 Datum Technology Corporation
// 
// Licensed under the Solderpad Hardware License, Version 2.0 (the "License");
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


`ifndef __UVML_SB_CNTXT_SV__
`define __UVML_SB_CNTXT_SV__


/**
 * TODO Describe uvml_sb_cntxt_c
 */
class uvml_sb_cntxt_c#(
   type T_TRN = uvml_trn_mon_trn_c
) extends uvm_object;
   
   // Transaction queues
   T_TRN     act_q     [$];
   T_TRN     exp_q     [$];
   realtime  exp_time_q[$];
   
   // Stats
   int unsigned      act_observed           = 0;
   int unsigned      exp_observed           = 0;
   int unsigned      act_good_observed      = 0;
   int unsigned      exp_good_observed      = 0;
   int unsigned      act_bad_observed       = 0;
   int unsigned      exp_bad_observed       = 0;
   longint unsigned  act_bits_observed      = 0;
   longint unsigned  exp_bits_observed      = 0;
   longint unsigned  act_good_bits_observed = 0;
   longint unsigned  exp_good_bits_observed = 0;
   longint unsigned  act_bad_bits_observed  = 0;
   longint unsigned  exp_bad_bits_observed  = 0;
   int unsigned      match_count            = 0;
   bit               synced                 = 0;
   real              avg_bit_rate           = 0;
   realtime          time_of_first_match    = 0;
   realtime          total_latency          = 0;
   realtime          avg_latency            = 0;
   
   // Events
   uvm_event#(T_TRN)  exp_observed_e;
   uvm_event#(T_TRN)  act_observed_e;
   
   
   `uvm_object_param_utils_begin(uvml_sb_cntxt_c#(T_TRN))
      `uvm_field_int (act_observed          , UVM_DEFAULT + UVM_DEC)
      `uvm_field_int (exp_observed          , UVM_DEFAULT + UVM_DEC)
      `uvm_field_int (act_good_observed     , UVM_DEFAULT + UVM_DEC)
      `uvm_field_int (exp_good_observed     , UVM_DEFAULT + UVM_DEC)
      `uvm_field_int (act_bad_observed      , UVM_DEFAULT + UVM_DEC)
      `uvm_field_int (exp_bad_observed      , UVM_DEFAULT + UVM_DEC)
      `uvm_field_int (act_bits_observed     , UVM_DEFAULT + UVM_DEC)
      `uvm_field_int (exp_bits_observed     , UVM_DEFAULT + UVM_DEC)
      `uvm_field_int (act_good_bits_observed, UVM_DEFAULT + UVM_DEC)
      `uvm_field_int (exp_good_bits_observed, UVM_DEFAULT + UVM_DEC)
      `uvm_field_int (act_bad_bits_observed , UVM_DEFAULT + UVM_DEC)
      `uvm_field_int (exp_bad_bits_observed , UVM_DEFAULT + UVM_DEC)
      `uvm_field_int (match_count           , UVM_DEFAULT + UVM_DEC)
      `uvm_field_int (synced                , UVM_DEFAULT          )
      `uvm_field_real(avg_bit_rate          , UVM_DEFAULT          )
      `uvm_field_real(time_of_first_match   , UVM_DEFAULT          )
      `uvm_field_real(total_latency         , UVM_DEFAULT          )
      `uvm_field_real(avg_latency           , UVM_DEFAULT          )
        
      `uvm_field_event(exp_observed_e, UVM_DEFAULT)
      `uvm_field_event(act_observed_e, UVM_DEFAULT)
   `uvm_object_utils_end
   
   
   /**
    * Default constructor
    */
   extern function new(string name="uvml_sb_cntxt");
   
   /**
    * Sets all state variables to 0's;
    */
   extern function void reset();
   
endclass : uvml_sb_cntxt_c


function uvml_sb_cntxt_c::new(string name="uvml_sb_cntxt");
   
   super.new(name);
   
   exp_observed_e = new("exp_observed_e");
   act_observed_e = new("act_observed_e");
   
endfunction : new


function void uvml_sb_cntxt_c::reset();
   
   act_q     .delete();
   exp_q     .delete();
   exp_time_q.delete();
   
   act_observed           = 0;
   exp_observed           = 0;
   act_good_observed      = 0;
   exp_good_observed      = 0;
   act_bad_observed       = 0;
   exp_bad_observed       = 0;
   act_bits_observed      = 0;
   exp_bits_observed      = 0;
   act_good_bits_observed = 0;
   exp_good_bits_observed = 0;
   act_bad_bits_observed  = 0;
   exp_bad_bits_observed  = 0;
   match_count            = 0;
   synced                 = 0;
   avg_bit_rate           = 0;
   time_of_first_match    = 0;
   total_latency          = 0;
   avg_latency            = 0;
   
endfunction : reset


`endif // __UVML_SB_CNTXT_SV__
