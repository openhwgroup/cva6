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


`ifndef __UVME_OBI_ST_ENV_SV__
`define __UVME_OBI_ST_ENV_SV__


/**
 * Top-level component that encapsulates, builds and connects all other
 * Open Bus Interface environment components.
 */
class uvme_obi_st_env_c extends uvm_env;
   
   // Objects
   uvme_obi_st_cfg_c    cfg;
   uvme_obi_st_cntxt_c  cntxt;
   
   // Agents
   uvma_obi_agent_c  mstr_agent;
   uvma_obi_agent_c  slv_agent ;
   
   // Components
   uvme_obi_st_cov_model_c     cov_model;
   uvme_obi_st_prd_c           predictor;
   uvme_obi_st_sb_simplex_c    sb;
   uvme_obi_st_vsqr_c          vsequencer;
   uvme_obi_st_slv_sb_delay_c  slv_sb_delay;
   
   
   `uvm_component_utils_begin(uvme_obi_st_env_c)
      `uvm_field_object(cfg  , UVM_DEFAULT)
      `uvm_field_object(cntxt, UVM_DEFAULT)
   `uvm_component_utils_end
   
   
   /**
    * Default constructor.
    */
   extern function new(string name="uvme_obi_st_env", uvm_component parent=null);
   
   /**
    * 1. Ensures cfg & cntxt handles are not null
    * 2. Retrieves cntxt.clk_vif from UVM configuration database via retrieve_clk_vif()
    * 3. Assigns cfg and cntxt handles via assign_cfg() & assign_cntxt()
    * 4. Builds all components via create_<x>()
    */
   extern virtual function void build_phase(uvm_phase phase);
   
   /**
    * 1. Connects agents to predictor via connect_predictor()
    * 2. Connects predictor & agents to scoreboard via connect_scoreboard()
    * 3. Assembles virtual sequencer handles via assemble_vsequencer()
    * 4. Connects agents to coverage model via connect_coverage_model()
    */
   extern virtual function void connect_phase(uvm_phase phase);
   
   /**
    * Assigns configuration handles to components using UVM Configuration Database.
    */
   extern function void assign_cfg();
   
   /**
    * Assigns context handles to components using UVM Configuration Database.
    */
   extern function void assign_cntxt();
   
   /**
    * Creates agent components.
    */
   extern function void create_agents();
   
   /**
    * Creates additional (non-agent) environment components (and objects).
    */
   extern function void create_env_components();
   
   /**
    * Creates environment's virtual sequencer.
    */
   extern function void create_vsequencer();
   
   /**
    * Creates environment's coverage model.
    */
   extern function void create_cov_model();
   
   /**
    * Connects agents to predictor.
    */
   extern function void connect_predictor();
   
   /**
    * Connects scoreboards components to agents/predictor.
    */
   extern function void connect_scoreboard();
   
   /**
    * Assembles virtual sequencer from agent sequencers.
    */
   extern function void assemble_vsequencer();
   
   /**
    * Connects environment coverage model to agents/scoreboards/predictor.
    */
   extern function void connect_coverage_model();
   
endclass : uvme_obi_st_env_c


function uvme_obi_st_env_c::new(string name="uvme_obi_st_env", uvm_component parent=null);
   
   super.new(name, parent);
   
endfunction : new


function void uvme_obi_st_env_c::build_phase(uvm_phase phase);
   
   super.build_phase(phase);
   
   void'(uvm_config_db#(uvme_obi_st_cfg_c)::get(this, "", "cfg", cfg));
   if (!cfg) begin
      `uvm_fatal("CFG", "Configuration handle is null")
   end
   else begin
      `uvm_info("CFG", $sformatf("Found configuration handle:\n%s", cfg.sprint()), UVM_DEBUG)
   end
   
   if (cfg.enabled) begin
      void'(uvm_config_db#(uvme_obi_st_cntxt_c)::get(this, "", "cntxt", cntxt));
      if (!cntxt) begin
         `uvm_info("CNTXT", "Context handle is null; creating.", UVM_DEBUG)
         cntxt = uvme_obi_st_cntxt_c::type_id::create("cntxt");
      end
      
      assign_cfg           ();
      assign_cntxt         ();
      create_agents        ();
      create_env_components();
      
      if (cfg.is_active) begin
         create_vsequencer();
      end
      
      if (cfg.cov_model_enabled) begin
         create_cov_model();
      end
   end
   
endfunction : build_phase


function void uvme_obi_st_env_c::connect_phase(uvm_phase phase);
   
   super.connect_phase(phase);
   
   if (cfg.enabled) begin
      if (cfg.scoreboarding_enabled) begin
         connect_predictor ();
         connect_scoreboard();
      end
      
      if (cfg.is_active) begin
         assemble_vsequencer();
      end
      
      if (cfg.cov_model_enabled) begin
         connect_coverage_model();
      end
   end
   
endfunction: connect_phase


function void uvme_obi_st_env_c::assign_cfg();
   
   uvm_config_db#(uvme_obi_st_cfg_c)::set(this, "*"         , "cfg", cfg         );
   uvm_config_db#(uvma_obi_cfg_c   )::set(this, "mstr_agent", "cfg", cfg.mstr_cfg);
   uvm_config_db#(uvma_obi_cfg_c   )::set(this, "slv_agent" , "cfg", cfg.slv_cfg );
   uvm_config_db#(uvml_sb_cfg_c    )::set(this, "sb"        , "cfg", cfg.sb_cfg  );
   
endfunction: assign_cfg


function void uvme_obi_st_env_c::assign_cntxt();
   
   uvm_config_db#(uvme_obi_st_cntxt_c)::set(this, "*"         , "cntxt", cntxt           );
   uvm_config_db#(uvma_obi_cntxt_c   )::set(this, "mstr_agent", "cntxt", cntxt.mstr_cntxt);
   uvm_config_db#(uvma_obi_cntxt_c   )::set(this, "slv_agent" , "cntxt", cntxt.slv_cntxt );
   uvm_config_db#(uvml_sb_cntxt_c    )::set(this, "sb"        , "cntxt", cntxt.sb_cntxt  );
   
endfunction: assign_cntxt


function void uvme_obi_st_env_c::create_agents();
   
   mstr_agent = uvma_obi_agent_c::type_id::create("mstr_agent", this);
   slv_agent  = uvma_obi_agent_c::type_id::create("slv_agent" , this);
   
endfunction: create_agents


function void uvme_obi_st_env_c::create_env_components();
   
   if (cfg.scoreboarding_enabled) begin
      predictor    = uvme_obi_st_prd_c         ::type_id::create("predictor"   , this);
      sb           = uvme_obi_st_sb_simplex_c  ::type_id::create("sb"          , this);
      slv_sb_delay = uvme_obi_st_slv_sb_delay_c::type_id::create("slv_sb_delay", this);
   end
   
endfunction: create_env_components


function void uvme_obi_st_env_c::create_vsequencer();
   
   vsequencer = uvme_obi_st_vsqr_c::type_id::create("vsequencer", this);
   
endfunction: create_vsequencer


function void uvme_obi_st_env_c::create_cov_model();
   
   cov_model = uvme_obi_st_cov_model_c::type_id::create("cov_model", this);
   
endfunction: create_cov_model


function void uvme_obi_st_env_c::connect_predictor();
   
   // Connect agent -> predictor
   mstr_agent.mon_ap.connect(predictor.in_export);
   
endfunction: connect_predictor


function void uvme_obi_st_env_c::connect_scoreboard();
   
   // Connect agent -> scoreboard
   slv_agent   .mon_ap.connect(slv_sb_delay.in_export );
   slv_sb_delay.out_ap.connect(sb          .act_export);
   
   // Connect predictor -> scoreboard
   predictor.out_ap.connect(sb.exp_export);
   
endfunction: connect_scoreboard


function void uvme_obi_st_env_c::assemble_vsequencer();
   
   vsequencer.mstr_sequencer = mstr_agent.sequencer;
   vsequencer.slv_sequencer  = slv_agent .sequencer;
   
endfunction: assemble_vsequencer


function void uvme_obi_st_env_c::connect_coverage_model();
   
   mstr_agent.drv_mstr_ap.connect(cov_model.mstr_seq_item_fifo.analysis_export);
   mstr_agent.mon_ap     .connect(cov_model.mstr_mon_trn_fifo .analysis_export);
   slv_agent .drv_slv_ap .connect(cov_model.slv_mon_trn_fifo  .analysis_export);
   slv_agent .mon_ap     .connect(cov_model.slv_mon_trn_fifo  .analysis_export);
   
endfunction: connect_coverage_model


`endif // __UVME_OBI_ST_ENV_SV__
