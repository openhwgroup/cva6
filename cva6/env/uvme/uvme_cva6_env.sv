// Copyright 2020 OpenHW Group
// Copyright 2020 Datum Technology Corporation
// Copyright 2020 Silicon Labs, Inc.
// Copyright 2021 Thales DIS Design Services SAS
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
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0


`ifndef __UVME_CVA6_ENV_SV__
`define __UVME_CVA6_ENV_SV__


/**
 * Top-level component that encapsulates, builds and connects all other
 * CVA6 environment components.
 */
class uvme_cva6_env_c extends uvm_env;

   // Objects
   uvme_cva6_cfg_c    cfg;
   uvme_cva6_cntxt_c  cntxt;

   // Components
   uvme_cva6_prd_c        predictor;
   uvme_cva6_sb_c         sb;
   uvme_cva6_vsqr_c       vsequencer;
   uvme_cva6_cov_model_c  cov_model;

   // Agents
   uvma_clknrst_agent_c   clknrst_agent;
   uvma_cvxif_agent_c     cvxif_agent;



   `uvm_component_utils_begin(uvme_cva6_env_c)
      `uvm_field_object(cfg  , UVM_DEFAULT)
      `uvm_field_object(cntxt, UVM_DEFAULT)
   `uvm_component_utils_end


   /**
    * Default constructor.
    */
   extern function new(string name="uvme_cva6_env", uvm_component parent=null);

   /**
    * 1. Ensures cfg & cntxt handles are not null
    * 2. Assigns cfg and cntxt handles via assign_cfg() & assign_cntxt()
    * 3. Builds all components via create_<x>()
    */
   extern virtual function void build_phase(uvm_phase phase);

   /**
    * 1. Connects agents to predictor via connect_predictor()
    * 3. Connects predictor & agents to scoreboard via connect_scoreboard()
    * 4. Assembles virtual sequencer handles via assemble_vsequencer()
    */
   extern virtual function void connect_phase(uvm_phase phase);

   /**
    * Print out final elaboration
    */
   extern virtual function void end_of_elaboration_phase(uvm_phase phase);

   /**
    * Creates and starts the instruction and virtual peripheral sequences in active mode.
    */
   extern virtual task run_phase(uvm_phase phase);

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
    * Creates additional (non-agent) environment components (and objects).
    */
   extern virtual function void create_env_components();

   /**
    * Creates environment's virtual sequencer.
    */
   extern virtual function void create_vsequencer();

   /**
    * Connects agents to predictor.
    */
   extern virtual function void connect_predictor();

   /**
    * Connects scoreboards components to agents/predictor.
    */
   extern virtual function void connect_scoreboard();

   /**
    * Connects environment coverage model to agents/scoreboards/predictor.
    */
   extern virtual function void connect_coverage_model();

   /**
    * Assembles virtual sequencer from agent sequencers.
    */
   extern virtual function void assemble_vsequencer();

endclass : uvme_cva6_env_c


function uvme_cva6_env_c::new(string name="uvme_cva6_env", uvm_component parent=null);

   super.new(name, parent);

endfunction : new


function void uvme_cva6_env_c::build_phase(uvm_phase phase);

   super.build_phase(phase);

   void'(uvm_config_db#(uvme_cva6_cfg_c)::get(this, "", "cfg", cfg));
   if (!cfg) begin
      `uvm_fatal("CFG", "Configuration handle is null")
   end
   else begin
      `uvm_info("CFG", $sformatf("Found configuration handle:\n%s", cfg.sprint()), UVM_DEBUG)
   end

   if (cfg.enabled) begin
      void'(uvm_config_db#(uvme_cva6_cntxt_c)::get(this, "", "cntxt", cntxt));
      if (!cntxt) begin
         `uvm_info("CNTXT", "Context handle is null; creating.", UVM_DEBUG)
         cntxt = uvme_cva6_cntxt_c::type_id::create("cntxt");
      end

      assign_cfg           ();
      assign_cntxt         ();
      create_agents        ();
      create_env_components();

      if (cfg.is_active) begin
         create_vsequencer();
      end
   end

endfunction : build_phase


function void uvme_cva6_env_c::connect_phase(uvm_phase phase);

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


function void uvme_cva6_env_c::end_of_elaboration_phase(uvm_phase phase);
   super.end_of_elaboration_phase(phase);

   `uvm_info("UVMECVA6ENV", $sformatf("Configuration:\n%s", cfg.sprint()), UVM_LOW)

endfunction : end_of_elaboration_phase

function void uvme_cva6_env_c::assign_cfg();

   uvm_config_db#(uvme_cva6_cfg_c)::set(this, "*", "cfg", cfg);

   uvm_config_db#(uvma_clknrst_cfg_c)::set(this, "*clknrst_agent", "cfg", cfg.clknrst_cfg);

   uvm_config_db#(uvma_cvxif_cfg_c)::set(this, "*cvxif_agent", "cfg", cfg.cvxif_cfg);

endfunction: assign_cfg


function void uvme_cva6_env_c::assign_cntxt();

   uvm_config_db#(uvme_cva6_cntxt_c)::set(this, "*", "cntxt", cntxt);
   uvm_config_db#(uvma_clknrst_cntxt_c)::set(this, "clknrst_agent", "cntxt", cntxt.clknrst_cntxt);

endfunction: assign_cntxt


function void uvme_cva6_env_c::create_agents();

   clknrst_agent = uvma_clknrst_agent_c::type_id::create("clknrst_agent", this);
   cvxif_agent   = uvma_cvxif_agent_c::type_id::create("cvxif_agent", this);

endfunction: create_agents


function void uvme_cva6_env_c::create_env_components();

   if (cfg.scoreboarding_enabled) begin
      predictor = uvme_cva6_prd_c::type_id::create("predictor", this);
      sb        = uvme_cva6_sb_c ::type_id::create("sb"       , this);
   end

   if (cfg.cov_model_enabled) begin
      cov_model = uvme_cva6_cov_model_c::type_id::create("cov_model", this);
   end

endfunction: create_env_components


function void uvme_cva6_env_c::create_vsequencer();

   vsequencer = uvme_cva6_vsqr_c::type_id::create("vsequencer", this);

endfunction: create_vsequencer


function void uvme_cva6_env_c::connect_predictor();

   //debug_agent.mon_ap.connect(predictor.debug_export);
   //clknrst_agent.mon_ap.connect(predictor.clknrst_export);
   // TODO Connect agents monitor analysis ports to predictor

endfunction: connect_predictor


function void uvme_cva6_env_c::connect_scoreboard();

   // TODO Connect agents -> scoreboard
   //      Ex: debug_agent.mon_ap.connect(sb.debug_sb.act_export);

   // TODO Connect predictor -> scoreboard
   //      Ex: predictor.debug_ap.connect(sb.debug_sb.exp_export);

endfunction: connect_scoreboard


function void uvme_cva6_env_c::assemble_vsequencer();

   vsequencer.clknrst_sequencer   = clknrst_agent.sequencer;
   vsequencer.cvxif_sequencer     = cvxif_agent.sequencer;

endfunction: assemble_vsequencer


task uvme_cva6_env_c::run_phase(uvm_phase phase);

            uvma_cvxif_seq_c        cvxif_seq;
            cvxif_seq = uvma_cvxif_seq_c::type_id::create("cvxif_seq");
            cvxif_seq.start(cvxif_agent.sequencer);

endtask

function void uvme_cva6_env_c::connect_coverage_model();

   cvxif_agent.monitor.req_ap.connect(cov_model.cvxif_covg.req_item_fifo.analysis_export);

endfunction: connect_coverage_model

`endif // __UVME_CVA6_ENV_SV__
