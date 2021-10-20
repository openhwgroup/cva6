// Copyright 2021 OpenHW Group
//
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
// Licensed under the Solderpad Hardware License v 2.1 (the "License"); you may not use this file except in compliance
// with the License, or, at your option, the Apache License version 2.0.  You may obtain a copy of the License at
//                                        https://solderpad.org/licenses/SHL-2.1/
// Unless required by applicable law or agreed to in writing, any work distributed under the License is distributed on
// an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.  See the License for the
// specific language governing permissions and limitations under the License.


`ifndef __UVMA_PMA_AGENT_SV__
`define __UVMA_PMA_AGENT_SV__


/**
 * Top-level component that encapsulates, builds and connects all others.  Capable of driving/monitoring
 * Memory attribution agent for OpenHW Group CORE-V verification testbenches interface.
 */
class uvma_pma_agent_c#(int ILEN=DEFAULT_ILEN,
                        int XLEN=DEFAULT_XLEN) extends uvm_agent;

   // Objects
   uvma_pma_cfg_c#(ILEN,XLEN)  cfg;
   uvma_pma_cntxt_c            cntxt;

   // Components
   uvma_pma_mon_c#(ILEN,XLEN)  monitor;
   uvma_pma_sb_c               scoreboard;
   uvma_pma_cov_model_c        cov_model;
   uvma_pma_region_cov_model_c region_cov_model[];
   uvma_pma_mon_trn_logger_c   mon_trn_logger;

   // TLM
   uvm_analysis_port#(uvma_pma_mon_trn_c )  mon_ap;


   `uvm_component_utils_begin(uvma_pma_agent_c)
      `uvm_field_object(cfg  , UVM_DEFAULT)
      `uvm_field_object(cntxt, UVM_DEFAULT)
   `uvm_component_utils_end


   /**
    * Default constructor.
    */
   extern function new(string name="uvma_pma_agent", uvm_component parent=null);

   /**
    * 1. Ensures cfg & cntxt handles are not null
    * 2. Builds all components
    */
   extern virtual function void build_phase(uvm_phase phase);

   /**
    * 1. Links agent's analysis ports to sub-components'
    * 2. Connects coverage models and loggers
    */
   extern virtual function void connect_phase(uvm_phase phase);

   /**
    * Uses uvm_config_db to retrieve cfg and hand out to sub-components.
    */
   extern function void get_and_set_cfg();

   /**
    * Uses uvm_config_db to retrieve cntxt and hand out to sub-components.
    */
   extern function void get_and_set_cntxt();

   /**
    * Creates sub-components.
    */
   extern function void create_components();

   /**
    * Connects agent's TLM ports to driver's and monitor's.
    */
   extern function void connect_analysis_ports();

   /**
    * Connects coverage model to monitor and driver's analysis ports.
    */
   extern function void connect_cov_model();

   /**
    * Connects transaction loggers to monitor and driver's analysis ports.
    */
   extern function void connect_trn_loggers();

endclass : uvma_pma_agent_c


function uvma_pma_agent_c::new(string name="uvma_pma_agent", uvm_component parent=null);

   super.new(name, parent);

endfunction : new


function void uvma_pma_agent_c::build_phase(uvm_phase phase);

   super.build_phase(phase);

   get_and_set_cfg  ();
   get_and_set_cntxt();
   create_components();

endfunction : build_phase


function void uvma_pma_agent_c::connect_phase(uvm_phase phase);

   super.connect_phase(phase);

   connect_analysis_ports      ();

   if (cfg.cov_model_enabled) begin
      connect_cov_model();
   end
   if (cfg.trn_log_enabled) begin
      connect_trn_loggers();
   end

endfunction: connect_phase


function void uvma_pma_agent_c::get_and_set_cfg();

   void'(uvm_config_db#(uvma_pma_cfg_c#(ILEN,XLEN))::get(this, "", "cfg", cfg));
   if (!cfg) begin
      `uvm_fatal("CFG", "Configuration handle is null")
   end
   else begin
      `uvm_info("CFG", $sformatf("Found configuration handle:\n%s", cfg.sprint()), UVM_DEBUG)
      uvm_config_db#(uvma_pma_cfg_c#(ILEN,XLEN))::set(this, "*", "cfg", cfg);
   end

endfunction : get_and_set_cfg

function void uvma_pma_agent_c::get_and_set_cntxt();

   void'(uvm_config_db#(uvma_pma_cntxt_c)::get(this, "", "cntxt", cntxt));
   if (!cntxt) begin
      `uvm_info("CNTXT", "Context handle is null; creating.", UVM_DEBUG)
      cntxt = uvma_pma_cntxt_c::type_id::create("cntxt");
   end
   uvm_config_db#(uvma_pma_cntxt_c)::set(this, "*", "cntxt", cntxt);

endfunction : get_and_set_cntxt

function void uvma_pma_agent_c::create_components();

   monitor         = uvma_pma_mon_c#(ILEN,XLEN)           ::type_id::create("monitor"        , this);
   scoreboard      = uvma_pma_sb_c#(ILEN,XLEN)            ::type_id::create("scoreboard"     , this);
   cov_model       = uvma_pma_cov_model_c                 ::type_id::create("cov_model"      , this);
   region_cov_model = new[cfg.regions.size()];
   foreach (region_cov_model[i]) begin
      region_cov_model[i] = uvma_pma_region_cov_model_c   ::type_id::create($sformatf("region_cov_model%0d", i), this);
      region_cov_model[i].region_index = i;
   end
   mon_trn_logger  = uvma_pma_mon_trn_logger_c#(ILEN,XLEN)::type_id::create("mon_trn_logger" , this);

endfunction : create_components


function void uvma_pma_agent_c::connect_analysis_ports();

   mon_ap = monitor.ap;

endfunction : connect_analysis_ports


function void uvma_pma_agent_c::connect_cov_model();

   mon_ap.connect(cov_model.mon_trn_fifo.analysis_export);
   foreach (region_cov_model[i]) begin
      mon_ap.connect(region_cov_model[i].mon_trn_fifo.analysis_export);
   end

endfunction : connect_cov_model


function void uvma_pma_agent_c::connect_trn_loggers();

   mon_ap.connect(mon_trn_logger .analysis_export);

endfunction : connect_trn_loggers


`endif // __UVMA_PMA_AGENT_SV__
