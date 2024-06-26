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

   uvmc_rvfi_reference_model reference_model;

   // Agents
   uvma_clknrst_agent_c   clknrst_agent;
   uvma_cvxif_agent_c     cvxif_agent;
   uvma_axi_agent_c       axi_agent;
   uvma_cva6_core_cntrl_agent_c core_cntrl_agent;
   uvma_rvfi_agent_c#(ILEN,XLEN)      rvfi_agent;
   uvma_isacov_agent_c#(ILEN,XLEN)    isacov_agent;

   // Handle to agent switch interface
   virtual uvmt_axi_switch_intf  axi_switch_vif;

   //CSR register model
   cva6_csr_reg_block                             csr_reg_block;
   cva6_csr_reg_adapter                           csr_reg_adapter;
   cva6_csr_reg_predictor#(uvma_isacov_mon_trn_c) csr_reg_predictor;

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
    * Get switch vif and set signals values
    */
   extern function void retrieve_vif();

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

   void'(uvm_config_db#(cva6_cfg_t)::get(this, "", "CVA6Cfg", cfg.CVA6Cfg));
   if (!cfg.CVA6Cfg) begin
      `uvm_fatal("CVA6Cfg", "RTL Configuration handle is null")
   end
   else begin
      `uvm_info("CVA6Cfg", $sformatf("Found RTL configuration handle:\n%p", cfg.CVA6Cfg), UVM_DEBUG)
   end

   if (cfg.enabled) begin
      void'(uvm_config_db#(uvme_cva6_cntxt_c)::get(this, "", "cntxt", cntxt));
      if (!cntxt) begin
         `uvm_info("CNTXT", "Context handle is null; creating.", UVM_DEBUG)
         cntxt = uvme_cva6_cntxt_c::type_id::create("cntxt");
      end

      cntxt.axi_cntxt.mem = cntxt.mem;

      if ($test$plusargs("tandem_enabled"))
          $value$plusargs("tandem_enabled=%b",cfg.tandem_enabled);

      retrieve_vif();
      assign_cfg           ();
      assign_cntxt         ();
      create_agents        ();
      create_env_components();

      if (cfg.is_active) begin
         create_vsequencer();
      end
   end

   if (csr_reg_block == null) begin
      uvm_reg::include_coverage("*", UVM_CVR_ALL); //Enable uvm_reg coverage
      csr_reg_block     = cva6_csr_reg_block::type_id::create("csr_reg_block", this);
      csr_reg_predictor = cva6_csr_reg_predictor#(uvma_isacov_mon_trn_c)::type_id::create("csr_reg_predictor", this);
      csr_reg_adapter   = cva6_csr_reg_adapter::type_id::create("csr_reg_adapter",, get_full_name());
      csr_reg_block.build();
    end

endfunction : build_phase


function void uvme_cva6_env_c::connect_phase(uvm_phase phase);

   super.connect_phase(phase);

   if (cfg.enabled) begin
      connect_predictor ();
      connect_scoreboard();

      if (cfg.is_active) begin
         assemble_vsequencer();
      end
     if (cfg.cov_model_enabled) begin
         connect_coverage_model();
      end
   end

   if (csr_reg_block.get_parent() == null) begin
      csr_reg_block.default_map.set_base_addr('h0);
      csr_reg_predictor.map     = csr_reg_block.default_map;
      csr_reg_predictor.adapter = csr_reg_adapter;
      csr_reg_block.default_map.set_auto_predict(0);
      isacov_agent.monitor.ap.connect(csr_reg_predictor.bus_in);
   end

endfunction: connect_phase


function void uvme_cva6_env_c::end_of_elaboration_phase(uvm_phase phase);
   super.end_of_elaboration_phase(phase);

   `uvm_info("UVMECVA6ENV", $sformatf("Configuration:\n%s", cfg.sprint()), UVM_MEDIUM)

endfunction : end_of_elaboration_phase

function void uvme_cva6_env_c::assign_cfg();

   uvm_config_db#(uvme_cva6_cfg_c)::set(this, "*", "cfg", cfg);

   uvm_config_db#(uvma_clknrst_cfg_c)::set(this, "*clknrst_agent", "cfg", cfg.clknrst_cfg);

   uvm_config_db#(uvma_cvxif_cfg_c)::set(this, "*cvxif_agent", "cfg", cfg.cvxif_cfg);

   uvm_config_db#(uvma_axi_cfg_c)::set(this, "*axi_agent", "cfg", cfg.axi_cfg);

   uvm_config_db#(uvma_core_cntrl_cfg_c)::set(this, "core_cntrl_agent", "cfg", cfg);

   uvm_config_db#(uvma_rvfi_cfg_c#(ILEN,XLEN))::set(this, "*rvfi_agent", "cfg", cfg.rvfi_cfg);

   uvm_config_db#(uvma_isacov_cfg_c)::set(this, "*isacov_agent", "cfg", cfg.isacov_cfg);

   uvm_config_db#(uvma_core_cntrl_cfg_c)::set(this, "*rvfi_scoreboard", "cfg", cfg);
   uvm_config_db#(uvma_core_cntrl_cfg_c)::set(this, "reference_model", "cfg", cfg);

endfunction: assign_cfg


function void uvme_cva6_env_c::assign_cntxt();

   uvm_config_db#(uvme_cva6_cntxt_c)::set(this, "*", "cntxt", cntxt);
   uvm_config_db#(uvma_clknrst_cntxt_c)::set(this, "clknrst_agent", "cntxt", cntxt.clknrst_cntxt);
   uvm_config_db#(uvma_axi_cntxt_c)::set(this, "axi_agent", "cntxt", cntxt.axi_cntxt);
   uvm_config_db#(uvma_rvfi_cntxt_c)::set(this, "rvfi_agent", "cntxt", cntxt.rvfi_cntxt);

endfunction: assign_cntxt


function void uvme_cva6_env_c::create_agents();

   clknrst_agent = uvma_clknrst_agent_c::type_id::create("clknrst_agent", this);
   cvxif_agent   = uvma_cvxif_agent_c::type_id::create("cvxif_agent", this);
   axi_agent     = uvma_axi_agent_c::type_id::create("axi_agent", this);
   core_cntrl_agent = uvma_cva6_core_cntrl_agent_c::type_id::create("core_cntrl_agent", this);
   rvfi_agent    = uvma_rvfi_agent_c#(ILEN,XLEN)::type_id::create("rvfi_agent", this);
   isacov_agent  = uvma_isacov_agent_c#(ILEN,XLEN)::type_id::create("isacov_agent", this);

endfunction: create_agents


function void uvme_cva6_env_c::create_env_components();

   if (cfg.tandem_enabled) begin
      reference_model = uvmc_rvfi_reference_model#(ILEN,XLEN)::type_id::create("reference_model", this);
   end

   if (cfg.scoreboard_enabled) begin
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

function void uvme_cva6_env_c::retrieve_vif();

   if (!uvm_config_db#(virtual uvmt_axi_switch_intf)::get(this, "", "axi_switch_vif", axi_switch_vif)) begin
      `uvm_fatal("VIF", $sformatf("Could not find vif handle of type %s in uvm_config_db", $typename(axi_switch_vif)))
   end
   else begin
      `uvm_info("VIF", $sformatf("Found vif handle of type %s in uvm_config_db", $typename(axi_switch_vif)), UVM_DEBUG)
   end

   if(cfg.axi_cfg.is_active == UVM_PASSIVE) begin
      axi_switch_vif.active <= 0;
   end else begin
      axi_switch_vif.active <= 1;
   end

endfunction : retrieve_vif

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
    if (cfg.tandem_enabled) begin
       rvfi_agent.rvfi_core_ap.connect(sb.m_rvfi_scoreboard.m_imp_core);
       rvfi_agent.rvfi_core_ap.connect(reference_model.m_analysis_imp);
       reference_model.m_analysis_port.connect(sb.m_rvfi_scoreboard.m_imp_reference_model);
    end

    if (cfg.scoreboard_enabled) begin
       isacov_agent.monitor.ap.connect(sb.instr_trn_fifo.analysis_export);
    end

endfunction: connect_scoreboard


function void uvme_cva6_env_c::assemble_vsequencer();

   vsequencer.clknrst_sequencer   = clknrst_agent.sequencer;
   vsequencer.cvxif_vsequencer    = cvxif_agent.vsequencer;
   vsequencer.axi_vsequencer      = axi_agent.vsequencer;

endfunction: assemble_vsequencer


task uvme_cva6_env_c::run_phase(uvm_phase phase);

   fork

      begin
            uvme_cvxif_vseq_c        cvxif_vseq;
            cvxif_vseq = uvme_cvxif_vseq_c::type_id::create("cvxif_vseq");
            cvxif_vseq.start(cvxif_agent.vsequencer);
      end

      begin
         if(cfg.axi_cfg.is_active == UVM_ACTIVE) begin
            uvma_axi_vseq_c  axi_vseq;
            axi_vseq = uvma_axi_vseq_c::type_id::create("axi_vseq");
            axi_vseq.start(axi_agent.vsequencer);
         end
      end
   join_none
endtask

function void uvme_cva6_env_c::connect_coverage_model();

   if (cfg.cov_cvxif_model_enabled) begin
      cvxif_agent.monitor.req_ap.connect(cov_model.cvxif_covg.req_item_fifo.analysis_export);
   end
   if (cfg.cov_isa_model_enabled) begin
      isacov_agent.monitor.ap.connect(cov_model.isa_covg.mon_trn_fifo.analysis_export);
      isacov_agent.monitor.ap.connect(cov_model.illegal_covg.mon_trn_fifo.analysis_export);
      isacov_agent.monitor.ap.connect(cov_model.exception_covg.mon_trn_fifo.analysis_export);
   end

   clknrst_agent.mon_ap.connect(cov_model.reset_export);
   rvfi_agent.rvfi_core_ap.connect(isacov_agent.monitor.rvfi_instr_imp);

   if(cfg.axi_cfg.cov_model_enabled) begin
      axi_agent.monitor.m_axi_superset_write_rsp_packets_collected.connect(cov_model.axi_covg.uvme_axi_cov_b_resp_fifo.analysis_export);
      axi_agent.monitor.m_axi_superset_read_rsp_packets_collected .connect(cov_model.axi_covg.uvme_axi_cov_r_resp_fifo.analysis_export);
      axi_agent.monitor.m_axi_superset_read_req_packets_collected .connect(cov_model.axi_covg.uvme_axi_cov_ar_req_fifo.analysis_export);
      axi_agent.monitor.m_axi_superset_write_req_packets_collected.connect(cov_model.axi_covg.uvme_axi_cov_aw_req_fifo.analysis_export);

      axi_agent.monitor.m_axi_superset_write_rsp_packets_collected.connect(cov_model.axi_ext_covg.uvme_axi_cov_b_resp_fifo.analysis_export);
      axi_agent.monitor.m_axi_superset_read_rsp_packets_collected . connect(cov_model.axi_ext_covg.uvme_axi_cov_r_resp_fifo.analysis_export);
      axi_agent.monitor.m_axi_superset_read_req_packets_collected .connect(cov_model.axi_ext_covg.uvme_axi_cov_ar_req_fifo.analysis_export);
      axi_agent.monitor.m_axi_superset_write_req_packets_collected.connect(cov_model.axi_ext_covg.uvme_axi_cov_aw_req_fifo.analysis_export);
   end

endfunction: connect_coverage_model

`endif // __UVME_CVA6_ENV_SV__
