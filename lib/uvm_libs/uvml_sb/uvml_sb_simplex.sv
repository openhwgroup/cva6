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


`ifndef __UVML_SB_SIMPLEX_SV__
`define __UVML_SB_SIMPLEX_SV__


/**
 * Scoreboard comparing expected and actual packet stream to/from DUT.
 */
class uvml_sb_simplex_c#(
   type T_CNTXT = uvml_sb_cntxt_c   ,
   type T_TRN   = uvml_trn_mon_trn_c
) extends uvm_scoreboard;
   
   // Objects
   uvml_sb_cfg_c  cfg;
   T_CNTXT        cntxt;
   
   // TLM
   uvm_analysis_export  #(T_TRN)  act_export;
   uvm_analysis_export  #(T_TRN)  exp_export;
   uvm_tlm_analysis_fifo#(T_TRN)  act_fifo;
   uvm_tlm_analysis_fifo#(T_TRN)  exp_fifo;
   
   
   `uvm_component_param_utils_begin(uvml_sb_simplex_c#(T_TRN, T_CNTXT))
      `uvm_field_object(cfg  , UVM_DEFAULT)
      `uvm_field_object(cntxt, UVM_DEFAULT)
   `uvm_component_utils_end
   
   
   /**
    * Default constructor.
    */
   extern function new(string name="uvml_sb_simplex", uvm_component parent=null);

   /**
    * TODO Describe uvml_sb_simplex_c::build_phase()
    */
   extern virtual function void build_phase(uvm_phase phase);

   /**
    * TODO Describe uvml_sb_simplex_c::connect_phase()
    */
   extern virtual function void connect_phase(uvm_phase phase);

   /**
    * TODO Describe uvml_sb_simplex_c::run_phase()
    */
   extern virtual task run_phase(uvm_phase phase);

   /**
    * TODO Describe uvml_sb_simplex_c::check_phase()
    */
   extern virtual function void check_phase(uvm_phase phase);

   /**
    * TODO Describe uvml_sb_simplex_c::mode_in_order()
    */
   extern task mode_in_order();

   /**
    * TODO Describe uvml_sb_simplex_c::mode_out_of_order()
    */
   extern task mode_out_of_order();
   
   /**
    * TODO Describe uvml_sb_simplex_c::get_act()
    */
   extern task get_act(output T_TRN act_trn);
   
   /**
    * TODO Describe uvml_sb_simplex_c::get_exp()
    */
   extern task get_exp(output T_TRN exp_trn);
   
   /**
    * TODO Describe uvml_sb_simplex_c::calc_act_stats()
    */
   extern function void calc_act_stats(ref T_TRN act_trn);
   
   /**
    * TODO Describe uvml_sb_simplex_c::calc_exp_stats()
    */
   extern function void calc_exp_stats(ref T_TRN exp_trn);
   
   /**
    * TODO Describe uvml_sb_simplex_c::log_new_act()
    */
   extern function void log_new_act(ref T_TRN act_trn);
   
   /**
    * TODO Describe uvml_sb_simplex_c::log_new_exp()
    */
   extern function void log_new_exp(ref T_TRN exp_trn);
   
   /**
    * TODO Describe uvml_sb_simplex_c::log_act_before_exp()
    */
   extern function void log_act_before_exp(ref T_TRN act_trn, exp_trn);
   
   /**
    * TODO Describe uvml_sb_simplex_c::log_match()
    */
   extern function void log_match(ref T_TRN act_trn, exp_trn);
   
   /**
    * TODO Describe uvml_sb_simplex_c::log_mismatch()
    */
   extern function void log_mismatch(ref T_TRN act_trn, exp_trn);
   
   /**
    * TODO Describe uvml_sb_simplex_c::log_drop()
    */
   extern function void log_drop(ref T_TRN act_trn, exp_trn);
   
endclass : uvml_sb_simplex_c


function uvml_sb_simplex_c::new(string name="uvml_sb_simplex", uvm_component parent=null);
   
   super.new(name, parent);
   
endfunction : new


function void uvml_sb_simplex_c::build_phase(uvm_phase phase);
   
   super.build_phase(phase);
   
   void'(uvm_config_db#(uvml_sb_cfg_c)::get(this, "", "cfg", cfg));
   if (cfg == null) begin
      `uvm_fatal("CFG", "Configuration handle is null")
   end
   
   void'(uvm_config_db#(T_CNTXT)::get(this, "", "cntxt", cntxt));
   if (cntxt == null) begin
      `uvm_fatal("CNTXT", "Context handle is null")
   end
   
   // Build TLM objects
   act_export  = new("act_export", this);
   exp_export  = new("exp_export", this);
   act_fifo    = new("act_fifo"  , this);
   exp_fifo    = new("exp_fifo"  , this);
   
endfunction : build_phase


function void uvml_sb_simplex_c::connect_phase(uvm_phase phase);
   
   super.connect_phase(phase);
   
   // Connect TLM objects
   act_export.connect(act_fifo.analysis_export);
   exp_export.connect(exp_fifo.analysis_export);
   
endfunction: connect_phase


task uvml_sb_simplex_c::run_phase(uvm_phase phase);
   
   T_TRN  exp_trn;
   
   super.run_phase(phase);
   
   if (cfg.enabled) begin
      fork
         forever begin
            case (cfg.mode)
               UVML_SB_MODE_IN_ORDER    : mode_in_order    ();
               UVML_SB_MODE_OUT_OF_ORDER: mode_out_of_order();
                
               default: begin
                  `uvm_error("SB", $sformatf("Invalid cfg.mode:%0d", cfg.mode))
               end
            endcase
         end
         
         forever begin
            get_exp       (exp_trn);
            calc_exp_stats(exp_trn);
            log_new_exp   (exp_trn);
         end
      join_none
   end

endtask: run_phase


function void uvml_sb_simplex_c::check_phase(uvm_phase phase);

`ifdef _VCP
   uvml_trn_mon_trn_c vcp_temp;
`endif // end VCP
   if (cfg.enabled) begin
      if (cntxt.exp_q.size() != 0) begin
         `uvm_error("SB", $sformatf("Expected queue is not empty! exp_q.size() = %0d", cntxt.exp_q.size()))
         foreach(cntxt.exp_q[ii]) begin
`ifdef _VCP
            vcp_temp = cntxt.exp_q[ii];
            `uvm_info("SB", $sformatf("exp_q[%0d]: \n%s", ii, temp.sprint()), UVM_MEDIUM)
`else
            `uvm_info("SB", $sformatf("exp_q[%0d]: \n%s", ii, cntxt.exp_q[ii].sprint()), UVM_MEDIUM)
`endif//end _VCP

         end
      end
      
      if (cntxt.match_count == 0) begin
         `uvm_error("SB", "Scoreboard did not see any matches during simulation")
      end
   end
   
endfunction: check_phase


task uvml_sb_simplex_c::mode_in_order();
   
   T_TRN  act_trn, exp_trn;
   bit    found_match = 0;
   
   get_act       (act_trn);
   calc_act_stats(exp_trn);
   log_new_act   (exp_trn);
   
   if (cntxt.exp_q.size() == 0) begin
      log_act_before_exp(act_trn, exp_trn);
   end
   else begin
      exp_trn = cntxt.exp_q.pop_front();
      if (exp_trn.compare(act_trn)) begin
         log_match(act_trn, exp_trn);
         cntxt.synced = 1;
         cntxt.match_count++;
      end
      else begin
         if (exp_trn.may_drop) begin
            log_drop(act_trn, exp_trn);
         end
         else begin
            log_mismatch(act_trn, exp_trn);
         end
      end
   end
   
endtask : mode_in_order


task uvml_sb_simplex_c::mode_out_of_order();
   
   T_TRN         act_trn, exp_trn;
   bit           found_match = 0;
   int unsigned  match_idx   = 0;
`ifdef _VCP
   uvml_trn_mon_trn_c vcp_temp;
`endif //end _VCP
   
   get_act       (act_trn);
   calc_act_stats(exp_trn);
   log_new_act   (exp_trn);
   
   if (cntxt.exp_q.size() == 0) begin
      log_act_before_exp(act_trn, exp_trn);
   end
   else begin
      foreach (cntxt.exp_q[ii]) begin
`ifdef _VCP
        vcp_temp=exp_q[ii];
        if (vcp_temp.compare(act_trn)) begin
`else
        if (cntxt.exp_q[ii].compare(act_trn)) begin
`endif //end VCP
            match_idx = ii;
            found_match = 1;
            cntxt.match_count++;
            break;
         end
      end
      if (found_match) begin
         log_match(act_trn, exp_trn);
         cntxt.exp_q.delete(match_idx);
      end
      else begin
         log_mismatch(act_trn, exp_trn);
      end
   end
   
endtask : mode_out_of_order


task uvml_sb_simplex_c::get_act(output T_TRN act_trn);
   
   act_fifo.get(act_trn);
   `uvml_hrtbt()
   cntxt.act_observed_e.trigger(act_trn);
   
endtask : get_act


task uvml_sb_simplex_c::get_exp(output T_TRN exp_trn);
   
   exp_fifo.get(exp_trn);
   cntxt.exp_observed_e.trigger(exp_trn);
   
endtask : get_exp


function void uvml_sb_simplex_c::calc_act_stats(ref T_TRN act_trn);
   
   bit  packed_trn[];
   
   void'(act_trn.pack_bytes(packed_trn));
   cntxt.act_observed++;
   cntxt.act_bits_observed += packed_trn.size();
   
   if (act_trn.has_error) begin
      cntxt.act_bad_observed++;
      cntxt.act_bad_bits_observed += packed_trn.size();
   end
   else begin
      cntxt.act_good_observed++;
      cntxt.act_good_bits_observed += packed_trn.size();
   end
   
   cntxt.act_q     .push_back(act_trn);
   cntxt.act_time_q.push_back($realtime());
   
endfunction : calc_act_stats


function void uvml_sb_simplex_c::calc_exp_stats(ref T_TRN exp_trn);
   
   bit  packed_trn[];
   
   void'(exp_trn.pack_bytes(packed_trn));
   cntxt.exp_observed++;
   cntxt.exp_bits_observed += packed_trn.size();
   
   if (exp_trn.has_error) begin
      cntxt.exp_bad_observed++;
      cntxt.exp_bad_bits_observed += packed_trn.size();
   end
   else begin
      cntxt.exp_good_observed++;
      cntxt.exp_good_bits_observed += packed_trn.size();
   end
   
   cntxt.exp_q     .push_back(exp_trn);
   cntxt.exp_time_q.push_back($realtime());
   
endfunction : calc_exp_stats


function void uvml_sb_simplex_c::log_new_act(ref T_TRN act_trn);
   
   `uvm_info("SB", $sformatf("New actual transaction from DUT: \n%s", act_trn.sprint()), UVM_HIGH)
   
endfunction : log_new_act


function void uvml_sb_simplex_c::log_new_exp(ref T_TRN exp_trn);
   
   `uvm_info("SB", $sformatf("New expected transaction from predictor: \n%s", exp_trn.sprint()), UVM_HIGH)
   
endfunction : log_new_exp


function void uvml_sb_simplex_c::log_act_before_exp(ref T_TRN act_trn, exp_trn);
   
   `uvm_error("SB", $sformatf("Actual received before expected:\n%s", act_trn.sprint()))
   
endfunction : log_act_before_exp


function void uvml_sb_simplex_c::log_match(ref T_TRN act_trn, exp_trn);
   
   `uvm_info("SB", "Actual and Expected match!", UVM_HIGH)
   
endfunction : log_match


function void uvml_sb_simplex_c::log_mismatch(ref T_TRN act_trn, exp_trn);
   
   `uvm_error("SB", $sformatf("Actual and Expected do not match: \nActual:\n%s \n Expected:\n%s", act_trn.sprint(), exp_trn.sprint()))
   
endfunction : log_mismatch


function void uvml_sb_simplex_c::log_drop(ref T_TRN act_trn, exp_trn);
   
   `uvm_warning("SB", $sformatf("Actual and Expected do not match, may_drop=1: \nActual:\n%s \n Expected:\n%s", act_trn.sprint(), exp_trn.sprint()))
   
endfunction : log_drop


`endif // __UVML_SB_SIMPLEX_SV__
