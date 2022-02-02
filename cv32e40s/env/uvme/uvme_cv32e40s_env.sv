// Copyright 2020 OpenHW Group
// Copyright 2020 Datum Technology Corporation
// Copyright 2020 Silicon Labs, Inc.
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


`ifndef __UVME_CV32E40S_ENV_SV__
`define __UVME_CV32E40S_ENV_SV__


/**
 * Top-level component that encapsulates, builds and connects all other
 * CV32E40S environment components.
 */
class uvme_cv32e40s_env_c extends uvm_env;

   // Objects
   uvme_cv32e40s_cfg_c    cfg;
   uvme_cv32e40s_cntxt_c  cntxt;

   // Components
   uvme_cv32e40s_cov_model_c  cov_model;
   uvme_cv32e40s_prd_c        predictor;
   uvme_cv32e40s_sb_c         sb;
   uvme_cv32e40s_core_sb_c    core_sb;
   uvme_cv32e40s_buserr_sb_c  buserr_sb;
   uvme_cv32e40s_vsqr_c       vsequencer;

   // Agents
   uvma_cv32e40s_core_cntrl_agent_c core_cntrl_agent;
   uvma_isacov_agent_c#(ILEN,XLEN)  isacov_agent;
   uvma_clknrst_agent_c             clknrst_agent;
   uvma_interrupt_agent_c           interrupt_agent;
   uvma_debug_agent_c               debug_agent;
   uvma_obi_memory_agent_c          obi_memory_instr_agent;
   uvma_obi_memory_agent_c          obi_memory_data_agent ;
   uvma_rvfi_agent_c#(ILEN,XLEN)    rvfi_agent;
   uvma_rvvi_agent_c#(ILEN,XLEN)    rvvi_agent;
   uvma_fencei_agent_c              fencei_agent;
   uvma_pma_agent_c#(ILEN,XLEN)     pma_agent;

   `uvm_component_utils_begin(uvme_cv32e40s_env_c)
      `uvm_field_object(cfg  , UVM_DEFAULT)
      `uvm_field_object(cntxt, UVM_DEFAULT)
   `uvm_component_utils_end

   /**
    * Default constructor.
    */
   extern function new(string name="uvme_cv32e40s_env", uvm_component parent=null);

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
    * 5. Connects agents to coverage model via connect_coverage_model()
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
    * Get virtual interface handles from UVM Configuration Database.
    */
   extern virtual function void retrieve_vifs();

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
    * Creates environment's coverage model.
    */
   extern virtual function void create_cov_model();

   /**
    * Connects agents to predictor.
    */
   extern virtual function void connect_predictor();

   /**
    * Connects the RVFI to the RVVI for step and compare feedback
    */
   extern virtual function void connect_rvfi_rvvi();

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

   /**
    * Install virtual peripheral sequences to the OBI data slave sequence
    */
   extern virtual function void install_vp_register_seqs(uvma_obi_memory_slv_seq_c data_slv_seq);

endclass : uvme_cv32e40s_env_c


function uvme_cv32e40s_env_c::new(string name="uvme_cv32e40s_env", uvm_component parent=null);

   super.new(name, parent);

endfunction : new


function void uvme_cv32e40s_env_c::build_phase(uvm_phase phase);

   super.build_phase(phase);

   void'(uvm_config_db#(uvme_cv32e40s_cfg_c)::get(this, "", "cfg", cfg));
   if (!cfg) begin
      `uvm_fatal("CFG", "Configuration handle is null")
   end
   else begin
      `uvm_info("CFG", $sformatf("Found configuration handle:\n%s", cfg.sprint()), UVM_DEBUG)
   end

   if (cfg.enabled) begin
      void'(uvm_config_db#(uvme_cv32e40s_cntxt_c)::get(this, "", "cntxt", cntxt));
      if (!cntxt) begin
         `uvm_info("CNTXT", "Context handle is null; creating.", UVM_DEBUG)
         cntxt = uvme_cv32e40s_cntxt_c::type_id::create("cntxt");
      end

      cntxt.obi_memory_instr_cntxt.mem = cntxt.mem;
      cntxt.obi_memory_data_cntxt.mem  = cntxt.mem;

      retrieve_vifs        ();
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

function void uvme_cv32e40s_env_c::connect_phase(uvm_phase phase);

   super.connect_phase(phase);

   if (cfg.enabled) begin
      if (cfg.rvvi_cfg.is_active == UVM_ACTIVE) begin
         uvma_rvvi_ovpsim_agent_c rvvi_ovpsim_agent;

         connect_rvfi_rvvi();
         if (!$cast(rvvi_ovpsim_agent, rvvi_agent)) begin
            `uvm_fatal("UVMECV32E40SENV", "Could not cast agent to rvvi_ovpsim_agent");
         end
         rvvi_ovpsim_agent.set_clknrst_sequencer(clknrst_agent.sequencer);
      end

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


function void uvme_cv32e40s_env_c::end_of_elaboration_phase(uvm_phase phase);

   super.end_of_elaboration_phase(phase);

endfunction : end_of_elaboration_phase

task uvme_cv32e40s_env_c::run_phase(uvm_phase phase);

   uvma_obi_memory_fw_preload_seq_c fw_preload_seq;
   uvma_obi_memory_slv_seq_c        instr_slv_seq;
   uvma_obi_memory_slv_seq_c        data_slv_seq;

   if (cfg.is_active) begin
      fork
         begin : spawn_obi_instr_fw_preload_thread
            fw_preload_seq = uvma_obi_memory_fw_preload_seq_c::type_id::create("fw_preload_seq");
            void'(fw_preload_seq.randomize());
            fw_preload_seq.start(obi_memory_instr_agent.sequencer);
         end

         begin : obi_instr_slv_thread
            instr_slv_seq = uvma_obi_memory_slv_seq_c::type_id::create("instr_slv_seq");
            void'(instr_slv_seq.randomize());
            instr_slv_seq.start(obi_memory_instr_agent.sequencer);
         end

         begin : obi_data_slv_thread
            data_slv_seq = uvma_obi_memory_slv_seq_c::type_id::create("data_slv_seq");

            install_vp_register_seqs(data_slv_seq);

            void'(data_slv_seq.randomize());
            data_slv_seq.start(obi_memory_data_agent.sequencer);
         end
      join_none
   end

endtask : run_phase


function void uvme_cv32e40s_env_c::retrieve_vifs();

   if (!uvm_config_db#(virtual uvmt_cv32e40s_vp_status_if)::get(this, "", "vp_status_vif", cntxt.vp_status_vif)) begin
      `uvm_fatal("VIF", $sformatf("Could not find vp_status_vif handle of type %s in uvm_config_db", $typename(cntxt.vp_status_vif)))
   end
   else begin
      `uvm_info("VIF", $sformatf("Found vp_status_vif handle of type %s in uvm_config_db", $typename(cntxt.vp_status_vif)), UVM_DEBUG)
   end

   if (!uvm_config_db#(virtual uvma_interrupt_if)::get(this, "", "intr_vif", cntxt.intr_vif)) begin
      `uvm_fatal("VIF", $sformatf("Could not find intr_vif handle of type %s in uvm_config_db", $typename(cntxt.intr_vif)))
   end
   else begin
      `uvm_info("VIF", $sformatf("Found intr_vif handle of type %s in uvm_config_db", $typename(cntxt.intr_vif)), UVM_DEBUG)
   end

   if (!uvm_config_db#(virtual uvma_debug_if)::get(this, "", "debug_vif", cntxt.debug_vif)) begin
      `uvm_fatal("VIF", $sformatf("Could not find debug_vif handle of type %s in uvm_config_db", $typename(cntxt.debug_vif)))
   end
   else begin
      `uvm_info("VIF", $sformatf("Found debug_vif handle of type %s in uvm_config_db", $typename(cntxt.debug_vif)), UVM_DEBUG)
   end

   void'(uvm_config_db#(virtual uvmt_cv32e40s_debug_cov_assert_if)::get(this, "", "debug_cov_vif", cntxt.debug_cov_vif));
   if (cntxt.debug_cov_vif == null) begin
      `uvm_fatal("CNTXT", $sformatf("No uvmt_cv32e40s_debug_cov_assert_if found in config database"))
   end

endfunction: retrieve_vifs

function void uvme_cv32e40s_env_c::assign_cfg();

   uvm_config_db#(uvme_cv32e40s_cfg_c)::set(this, "*", "cfg", cfg);

   uvm_config_db#(uvma_clknrst_cfg_c)::set(this, "*clknrst_agent", "cfg", cfg.clknrst_cfg);
   uvm_config_db#(uvma_core_cntrl_cfg_c)::set(this, "*core_cntrl_agent", "cfg", cfg);
   uvm_config_db#(uvma_debug_cfg_c)::set(this, "debug_agent", "cfg", cfg.debug_cfg);
   uvm_config_db#(uvma_fencei_cfg_c)::set(this, "fencei_agent", "cfg", cfg.fencei_cfg);
   uvm_config_db#(uvma_interrupt_cfg_c)::set(this, "*interrupt_agent", "cfg", cfg.interrupt_cfg);
   uvm_config_db#(uvma_isacov_cfg_c)::set(this, "*isacov_agent", "cfg", cfg.isacov_cfg);
   uvm_config_db#(uvma_obi_memory_cfg_c)::set(this, "obi_memory_data_agent",  "cfg", cfg.obi_memory_data_cfg);
   uvm_config_db#(uvma_obi_memory_cfg_c)::set(this, "obi_memory_instr_agent", "cfg", cfg.obi_memory_instr_cfg);
   uvm_config_db#(uvma_pma_cfg_c)::set(this, "pma_agent", "cfg", cfg.pma_cfg);
   uvm_config_db#(uvma_rvfi_cfg_c#(ILEN,XLEN))::set(this, "rvfi_agent", "cfg", cfg.rvfi_cfg);
   uvm_config_db#(uvma_rvvi_cfg_c#(ILEN,XLEN))::set(this, "rvvi_agent", "cfg", cfg.rvvi_cfg);

endfunction: assign_cfg


function void uvme_cv32e40s_env_c::assign_cntxt();

   uvm_config_db#(uvme_cv32e40s_cntxt_c)::set(this, "*", "cntxt", cntxt);

   uvm_config_db#(uvma_clknrst_cntxt_c)::set(this, "clknrst_agent", "cntxt", cntxt.clknrst_cntxt);
   //TODO core_cntrl_cntxt?
   uvm_config_db#(uvma_debug_cntxt_c)::set(this, "debug_agent", "cntxt", cntxt.debug_cntxt);
   uvm_config_db#(uvma_fencei_cntxt_c)::set(this, "fencei_agent", "cntxt", cntxt.fencei_cntxt);
   uvm_config_db#(uvma_interrupt_cntxt_c)::set(this, "interrupt_agent", "cntxt", cntxt.interrupt_cntxt);
   uvm_config_db#(uvma_obi_memory_cntxt_c)::set(this, "obi_memory_data_agent",  "cntxt", cntxt.obi_memory_data_cntxt);
   uvm_config_db#(uvma_obi_memory_cntxt_c)::set(this, "obi_memory_instr_agent", "cntxt", cntxt.obi_memory_instr_cntxt);
   uvm_config_db#(uvma_rvfi_cntxt_c#(ILEN,XLEN))::set(this, "rvfi_agent", "cntxt", cntxt.rvfi_cntxt);
   uvm_config_db#(uvma_rvvi_cntxt_c#(ILEN,XLEN))::set(this, "rvvi_agent", "cntxt", cntxt.rvvi_cntxt);

endfunction: assign_cntxt


function void uvme_cv32e40s_env_c::create_agents();

   core_cntrl_agent = uvma_cv32e40s_core_cntrl_agent_c::type_id::create("core_cntrl_agent", this);
   isacov_agent = uvma_isacov_agent_c#(ILEN,XLEN)::type_id::create("isacov_agent", this);
   clknrst_agent = uvma_clknrst_agent_c::type_id::create("clknrst_agent", this);
   interrupt_agent = uvma_interrupt_agent_c::type_id::create("interrupt_agent", this);
   debug_agent = uvma_debug_agent_c::type_id::create("debug_agent", this);
   obi_memory_instr_agent = uvma_obi_memory_agent_c::type_id::create("obi_memory_instr_agent", this);
   obi_memory_data_agent  = uvma_obi_memory_agent_c::type_id::create("obi_memory_data_agent",  this);
   rvfi_agent = uvma_rvfi_agent_c#(ILEN,XLEN)::type_id::create("rvfi_agent", this);
   rvvi_agent = uvma_rvvi_ovpsim_agent_c#(ILEN,XLEN)::type_id::create("rvvi_agent", this);
   fencei_agent = uvma_fencei_agent_c::type_id::create("fencei_agent", this);
   pma_agent = uvma_pma_agent_c#(ILEN,XLEN)::type_id::create("pma_agent", this);

endfunction: create_agents


function void uvme_cv32e40s_env_c::create_env_components();

   if (cfg.scoreboarding_enabled) begin
      predictor = uvme_cv32e40s_prd_c::type_id::create("predictor", this);
      sb        = uvme_cv32e40s_sb_c::type_id::create("sb"       , this);
      core_sb   = uvme_cv32e40s_core_sb_c::type_id::create("core_sb", this);
   end

   if (cfg.buserr_scoreboarding_enabled) begin
      buserr_sb = uvme_cv32e40s_buserr_sb_c::type_id::create("buserr_sb", this);
   end

endfunction: create_env_components


function void uvme_cv32e40s_env_c::create_vsequencer();

   vsequencer = uvme_cv32e40s_vsqr_c::type_id::create("vsequencer", this);

endfunction: create_vsequencer

function void uvme_cv32e40s_env_c::create_cov_model();

   cov_model = uvme_cv32e40s_cov_model_c::type_id::create("cov_model", this);

endfunction: create_cov_model


function void uvme_cv32e40s_env_c::connect_predictor();

endfunction: connect_predictor

function void uvme_cv32e40s_env_c::connect_rvfi_rvvi();

   foreach (rvfi_agent.instr_mon_ap[i]) begin
      rvfi_agent.instr_mon_ap[i].connect(rvvi_agent.sequencer.rvfi_instr_export);
   end

endfunction : connect_rvfi_rvvi

function void uvme_cv32e40s_env_c::connect_scoreboard();

   // Connect the CORE Scoreboard (but only if the ISS is running)
   if (cfg.use_iss) begin
      rvvi_agent.state_mon_ap.connect(core_sb.rvvi_state_export);
      foreach (rvfi_agent.instr_mon_ap[i]) begin
         rvfi_agent.instr_mon_ap[i].connect(core_sb.rvfi_instr_export);
      end
   end

   // Connect the bus error scoreboard
   if (cfg.buserr_scoreboarding_enabled) begin
      obi_memory_data_agent.mon_ap.connect(buserr_sb.obid);
      obi_memory_instr_agent.mon_ap.connect(buserr_sb.obii);
      foreach (rvfi_agent.instr_mon_ap[i]) begin
         rvfi_agent.instr_mon_ap[i].connect(buserr_sb.rvfi);
      end
   end

   // Connect the PMA scoreboard
   foreach (rvfi_agent.instr_mon_ap[i]) begin
      rvfi_agent.instr_mon_ap[i].connect(pma_agent.scoreboard.rvfi_instr_export);
   end
   obi_memory_instr_agent.mon_ap.connect(pma_agent.scoreboard.obi_i_export);
   obi_memory_data_agent.mon_ap.connect(pma_agent.scoreboard.obi_d_export);

endfunction: connect_scoreboard


function void uvme_cv32e40s_env_c::connect_coverage_model();

   isacov_agent.monitor.ap.connect(cov_model.exceptions_covg.isacov_mon_export);
   isacov_agent.monitor.ap.connect(cov_model.counters_covg.isacov_mon_export);

   obi_memory_data_agent.mon_ap.connect(pma_agent.monitor.obi_d_export);
   foreach (rvfi_agent.instr_mon_ap[i]) begin
      rvfi_agent.instr_mon_ap[i].connect(isacov_agent.monitor.rvfi_instr_export);
      rvfi_agent.instr_mon_ap[i].connect(cov_model.interrupt_covg.interrupt_mon_export);
      rvfi_agent.instr_mon_ap[i].connect(pma_agent.monitor.rvfi_instr_export);
   end

endfunction: connect_coverage_model


function void uvme_cv32e40s_env_c::assemble_vsequencer();

   vsequencer.clknrst_sequencer   = clknrst_agent.sequencer;
   vsequencer.interrupt_sequencer = interrupt_agent.sequencer;
   vsequencer.debug_sequencer     = debug_agent.sequencer;
   vsequencer.obi_memory_instr_sequencer = obi_memory_instr_agent.sequencer;
   vsequencer.obi_memory_data_sequencer  = obi_memory_data_agent .sequencer;

endfunction: assemble_vsequencer


function void uvme_cv32e40s_env_c::install_vp_register_seqs(uvma_obi_memory_slv_seq_c data_slv_seq);

   void'(data_slv_seq.register_vp_vseq("vp_virtual_printer", CV_VP_VIRTUAL_PRINTER_BASE, uvma_obi_memory_vp_virtual_printer_seq_c::get_type()));

   void'(data_slv_seq.register_vp_vseq("vp_rand_num", CV_VP_RANDOM_NUM_BASE,  uvma_obi_memory_vp_rand_num_seq_c::get_type()));

   void'(data_slv_seq.register_vp_vseq("vp_cycle_counter", CV_VP_CYCLE_COUNTER_BASE, uvma_obi_memory_vp_cycle_counter_seq_c::get_type()));

   begin
      uvma_obi_memory_vp_directed_slv_resp_seq_c#(2) vp_seq;
      if (!$cast(vp_seq, data_slv_seq.register_vp_vseq("vp_directed_slv_resp", CV_VP_OBI_SLV_RESP_BASE, uvma_obi_memory_vp_directed_slv_resp_seq_c#(2)::get_type()))) begin
         `uvm_fatal("CV32E40SVPSEQ", $sformatf("Could not cast vp_directed_slv_resp correctly"));
      end
      vp_seq.obi_cfg[0] = cfg.obi_memory_instr_cfg;
      vp_seq.obi_cfg[1] = cfg.obi_memory_data_cfg;
   end

   begin
      uvme_cv32e40s_vp_sig_writer_seq_c vp_seq;
      if (!$cast(vp_seq, data_slv_seq.register_vp_vseq("vp_sig_writer", CV_VP_SIG_WRITER_BASE, uvme_cv32e40s_vp_sig_writer_seq_c::get_type()))) begin
         `uvm_fatal("CV32E40SVPSEQ", $sformatf("Could not cast vp_sig_writes correctly"));
      end
      vp_seq.cv32e40s_cntxt = cntxt;
   end

   begin
      uvme_cv32e40s_vp_status_flags_seq_c vp_seq;
      if (!$cast(vp_seq, data_slv_seq.register_vp_vseq("vp_status_flags", CV_VP_STATUS_FLAGS_BASE, uvme_cv32e40s_vp_status_flags_seq_c::get_type()))) begin
         `uvm_fatal("CV32E40SVPSEQ", $sformatf("Could not cast vp_status_flags correctly"));
      end
      vp_seq.cv32e40s_cntxt = cntxt;
   end

   begin
      uvme_cv32e40s_vp_interrupt_timer_seq_c vp_seq;
      if (!$cast(vp_seq, data_slv_seq.register_vp_vseq("vp_interrupt_timer", CV_VP_INTR_TIMER_BASE, uvme_cv32e40s_vp_interrupt_timer_seq_c::get_type()))) begin
         `uvm_fatal("CV32E40SVPSEQ", $sformatf("Could not cast vp_interrupt_timer correctly"));
      end
      vp_seq.cv32e40s_cntxt = cntxt;
   end

   begin
      uvme_cv32e40s_vp_debug_control_seq_c vp_seq;
      if (!$cast(vp_seq, data_slv_seq.register_vp_vseq("vp_debug_control", CV_VP_DEBUG_CONTROL_BASE, uvme_cv32e40s_vp_debug_control_seq_c::get_type()))) begin
         `uvm_fatal("CV32E40SVPSEQ", $sformatf("Could not cast vp_debug_control correctly"));
      end
      vp_seq.cv32e40s_cntxt = cntxt;
   end

   begin
      uvme_cv32e40s_vp_fencei_tamper_seq_c vp_seq;
      if (!$cast(vp_seq, data_slv_seq.register_vp_vseq("vp_fencei_tamper", CV_VP_FENCEI_TAMPER_BASE, uvme_cv32e40s_vp_fencei_tamper_seq_c::get_type()))) begin
         `uvm_fatal("CV32E40SVPSEQ", $sformatf("Could not cast vp_fencei_tamper correctly"));
      end
      vp_seq.cv32e40s_cntxt = cntxt;
   end

endfunction : install_vp_register_seqs

`endif // __UVME_CV32E40S_ENV_SV__
