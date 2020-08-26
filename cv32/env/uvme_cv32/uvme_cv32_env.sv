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


`ifndef __UVME_CV32_ENV_SV__
`define __UVME_CV32_ENV_SV__


/**
 * Top-level component that encapsulates, builds and connects all other
 * CV32 environment components.
 */
class uvme_cv32_env_c extends uvm_env;
   
   // Objects
   uvme_cv32_cfg_c    cfg;
   uvme_cv32_cntxt_c  cntxt;
   
   // Register Abstraction Layer (RAL)
   uvme_cv32_ral_c           ral;
   //uvma_debug_reg_adapter_c  reg_adapter;
   
   // Components
   uvme_cv32_cov_model_c  cov_model;
   uvme_cv32_prd_c        predictor;
   uvme_cv32_sb_c         sb;
   uvme_cv32_vsqr_c       vsequencer;
   
   // Agents
   uvma_clknrst_agent_c   clknrst_agent;
   uvma_interrupt_agent_c interrupt_agent;
   //uvma_debug_agent_c  debug_agen
   
   

   `uvm_component_utils_begin(uvme_cv32_env_c)
      `uvm_field_object(cfg  , UVM_DEFAULT)
      `uvm_field_object(cntxt, UVM_DEFAULT)
   `uvm_component_utils_end
   
   
   /**
    * Default constructor.
    */
   extern function new(string name="uvme_cv32_env", uvm_component parent=null);
   
   /**
    * 1. Ensures cfg & cntxt handles are not null
    * 2. Assigns cfg and cntxt handles via assign_cfg() & assign_cntxt()
    * 3. Builds all components via create_<x>()
    */
   extern virtual function void build_phase(uvm_phase phase);
   
   /**
    * 1. Connects agents to predictor via connect_predictor()
    * 2. Connects ral to predictor & provisioning agent via connect_ral()
    * 3. Connects predictor & agents to scoreboard via connect_scoreboard()
    * 4. Assembles virtual sequencer handles via assemble_vsequencer()
    * 5. Connects agents to coverage model via connect_coverage_model()
    */
   extern virtual function void connect_phase(uvm_phase phase);
   
   /**
    * Assigns configuration handles to components using UVM Configuration Database.
    */
   extern virtual function void assign_cfg();
   
   /**
    * Assigns context handles to components using UVM Configuration Database.
    */
   extern virtual function void assign_cntxt();
   
   /**
    * Creates agent components.
    */
   extern virtual function void create_agents();
   
   /**
    * Creates ral_adapter which translates to/from ral to debug_agent.
    */
   extern virtual function void create_ral_adapter();
   
   /**
    * Creates additional (non-agent) environment components (and objects).
    */
   extern virtual function void create_env_components();
   
   /**
    * Creates environment's virtual sequencer.
    */
   extern virtual function void create_vsequencer();
   
   /**
    * Creates environment's coverage model.
    */
   extern virtual function void create_cov_model();
   
   /**
    * Connects agents to predictor.
    */
   extern virtual function void connect_predictor();
   
   /**
    * Connects scoreboards components to agents/predictor.
    */
   extern virtual function void connect_scoreboard();
   
   /**
    * Connects RAL to provisioning agent (debug_agent).
    */
   extern virtual function void connect_ral();
   
   /**
    * Connects environment coverage model to agents/scoreboards/predictor.
    */
   extern virtual function void connect_coverage_model();
   
   /**
    * Assembles virtual sequencer from agent sequencers.
    */
   extern virtual function void assemble_vsequencer();
   
endclass : uvme_cv32_env_c


function uvme_cv32_env_c::new(string name="uvme_cv32_env", uvm_component parent=null);
   
   super.new(name, parent);
   
endfunction : new


function void uvme_cv32_env_c::build_phase(uvm_phase phase);
   
   super.build_phase(phase);
   
   void'(uvm_config_db#(uvme_cv32_cfg_c)::get(this, "", "cfg", cfg));
   if (!cfg) begin
      `uvm_fatal("CFG", "Configuration handle is null")
   end
   else begin
      `uvm_info("CFG", $sformatf("Found configuration handle:\n%s", cfg.sprint()), UVM_DEBUG)
   end
   
   if (cfg.enabled) begin
      void'(uvm_config_db#(uvme_cv32_cntxt_c)::get(this, "", "cntxt", cntxt));
      if (!cntxt) begin
         `uvm_info("CNTXT", "Context handle is null; creating.", UVM_DEBUG)
         cntxt = uvme_cv32_cntxt_c::type_id::create("cntxt");
      end
      
      assign_cfg           ();
      assign_cntxt         ();
      create_agents        ();
      create_ral_adapter   ();
      create_env_components();
      
      if (cfg.is_active) begin
         create_vsequencer();
      end
      
      if (cfg.cov_model_enabled) begin
         create_cov_model();
      end
   end
   
endfunction : build_phase


function void uvme_cv32_env_c::connect_phase(uvm_phase phase);
   
   super.connect_phase(phase);
   
   if (cfg.enabled) begin
      if (cfg.scoreboarding_enabled) begin
         connect_predictor ();
         connect_scoreboard();
      end
      
      if (cfg.is_active) begin
         connect_ral();
         assemble_vsequencer();
      end
      
      if (cfg.cov_model_enabled) begin
         connect_coverage_model();
      end
   end
   
endfunction: connect_phase


function void uvme_cv32_env_c::assign_cfg();
   
   uvm_config_db#(uvme_cv32_cfg_c)::set(this, "*", "cfg", cfg);
   uvm_config_db#(uvma_clknrst_cfg_c)::set(this, "*clknrst_agent", "cfg", cfg.clknrst_cfg);
   uvm_config_db#(uvma_interrupt_cfg_c)::set(this, "*interrupt_agent", "cfg", cfg.interrupt_cfg);
   //uvm_config_db#(uvma_debug_cfg_c)::set(this, "debug_agent", "cfg", cfg.debug_cfg);
   
endfunction: assign_cfg


function void uvme_cv32_env_c::assign_cntxt();
   
   uvm_config_db#(uvme_cv32_cntxt_c)::set(this, "*", "cntxt", cntxt);
   uvm_config_db#(uvma_clknrst_cntxt_c)::set(this, "clknrst_agent", "cntxt", cntxt.clknrst_cntxt);
   uvm_config_db#(uvma_interrupt_cntxt_c)::set(this, "interrupt_agent", "cntxt", cntxt.interrupt_cntxt);
   //uvm_config_db#(uvma_debug_cntxt_c)::set(this, "debug_agent", "cntxt", cntxt.debug_cntxt);
   
endfunction: assign_cntxt


function void uvme_cv32_env_c::create_agents();
   
   clknrst_agent = uvma_clknrst_agent_c::type_id::create("clknrst_agent", this);
   interrupt_agent = uvma_interrupt_agent_c::type_id::create("interrupt_agent", this);
   //debug_agent = uvma_debug_agent_c::type_id::create("debug_agent", this);
   
endfunction: create_agents


function void uvme_cv32_env_c::create_env_components();
   
   if (cfg.scoreboarding_enabled) begin
      predictor = uvme_cv32_prd_c::type_id::create("predictor", this);
      sb        = uvme_cv32_sb_c ::type_id::create("sb"       , this);
   end
   
endfunction: create_env_components


function void uvme_cv32_env_c::create_ral_adapter();
   
   //reg_adapter = uvma_debug_reg_adapter_c::type_id::create("reg_adapter");
   ral = cfg.ral;
   
endfunction: create_ral_adapter


function void uvme_cv32_env_c::create_vsequencer();
   
   vsequencer = uvme_cv32_vsqr_c::type_id::create("vsequencer", this);
   
endfunction: create_vsequencer

function void uvme_cv32_env_c::create_cov_model();
   
   cov_model = uvme_cv32_cov_model_c::type_id::create("cov_model", this);
   void'(uvm_config_db#(virtual uvmt_cv32_isa_covg_if)::get(this, "", "isa_covg_vif", cntxt.isa_covg_vif));
   if (cntxt.isa_covg_vif == null) begin
      `uvm_fatal("CNTXT", $sformatf("No uvmt_cv32_isa_covg_if found in config database"))
   end
endfunction: create_cov_model


function void uvme_cv32_env_c::connect_predictor();
   
   //debug_agent.mon_ap.connect(predictor.debug_export);
   //clknrst_agent.mon_ap.connect(predictor.clknrst_export);
   // TODO Connect agents monitor analysis ports to predictor
   
endfunction: connect_predictor


function void uvme_cv32_env_c::connect_scoreboard();
   
   // TODO Connect agents -> scoreboard
   //      Ex: debug_agent.mon_ap.connect(sb.debug_sb.act_export);
   
   // TODO Connect predictor -> scoreboard
   //      Ex: predictor.debug_ap.connect(sb.debug_sb.exp_export);
   
endfunction: connect_scoreboard


function void uvme_cv32_env_c::connect_ral();
   
   //ral.default_map.set_sequencer(debug_agent.sequencer, reg_adapter);
   //ral.default_map.set_auto_predict(1);
   
endfunction: connect_ral


function void uvme_cv32_env_c::connect_coverage_model();
   
   interrupt_agent.monitor.ap.connect(cov_model.interrupt_covg.interrupt_mon_export);      
   
endfunction: connect_coverage_model


function void uvme_cv32_env_c::assemble_vsequencer();
   
   vsequencer.clknrst_sequencer = clknrst_agent.sequencer;
   vsequencer.interrupt_sequencer = interrupt_agent.sequencer;
   //vsequencer.debug_sequencer   = debug_agent.sequencer;
   
endfunction: assemble_vsequencer


`endif // __UVME_CV32_ENV_SV__
