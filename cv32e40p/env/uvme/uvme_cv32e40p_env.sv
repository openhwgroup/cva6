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


`ifndef __UVME_CV32E40P_ENV_SV__
`define __UVME_CV32E40P_ENV_SV__

// Forward decls
typedef class uvme_cv32e40p_vp_debug_control_seq_c;
typedef class uvme_cv32e40p_vp_interrupt_timer_seq_c;
typedef class uvme_cv32e40p_vp_sig_writer_seq_c;
typedef class uvme_cv32e40p_vp_status_flags_seq_c;
typedef class uvme_cv32e40p_vp_rand_num_seq_c;

/**
 * Top-level component that encapsulates, builds and connects all other
 * CV32E40P environment components.
 */
class uvme_cv32e40p_env_c extends uvm_env;

   // Objects
   uvme_cv32e40p_cfg_c    cfg;
   uvme_cv32e40p_cntxt_c  cntxt;

   // Components
   uvme_cv32e40p_cov_model_c  cov_model;
   uvme_cv32e40p_prd_c        predictor;
   uvme_cv32e40p_sb_c         sb;
   uvme_cv32e40p_vsqr_c       vsequencer;

   // Agents
   uvma_clknrst_agent_c     clknrst_agent;
   uvma_interrupt_agent_c   interrupt_agent;
   uvma_debug_agent_c       debug_agent;
   uvma_obi_memory_agent_c  obi_memory_instr_agent;
   uvma_obi_memory_agent_c  obi_memory_data_agent ;



   `uvm_component_utils_begin(uvme_cv32e40p_env_c)
      `uvm_field_object(cfg  , UVM_DEFAULT)
      `uvm_field_object(cntxt, UVM_DEFAULT)
   `uvm_component_utils_end


   /**
    * Default constructor.
    */
   extern function new(string name="uvme_cv32e40p_env", uvm_component parent=null);

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

endclass : uvme_cv32e40p_env_c


function uvme_cv32e40p_env_c::new(string name="uvme_cv32e40p_env", uvm_component parent=null);

   super.new(name, parent);

endfunction : new


function void uvme_cv32e40p_env_c::build_phase(uvm_phase phase);

   super.build_phase(phase);

   void'(uvm_config_db#(uvme_cv32e40p_cfg_c)::get(this, "", "cfg", cfg));
   if (cfg == null) begin
      `uvm_fatal("UVME_CV32E40P_ENV", "Configuration handle is null")
   end
   else begin
      `uvm_info("UVME_CV32E40P_ENV", $sformatf("Found configuration handle:\n%s", cfg.sprint()), UVM_DEBUG)
   end

   if (cfg.enabled) begin
      void'(uvm_config_db#(uvme_cv32e40p_cntxt_c)::get(this, "", "cntxt", cntxt));
      if (cntxt == null) begin
         `uvm_info("UVME_CV32E40P_ENV", "Context handle is null; creating.", UVM_DEBUG)
         cntxt = uvme_cv32e40p_cntxt_c::type_id::create("cntxt");
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


function void uvme_cv32e40p_env_c::connect_phase(uvm_phase phase);

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


task uvme_cv32e40p_env_c::run_phase(uvm_phase phase);

   uvma_obi_memory_fw_preload_seq_c fw_preload_seq;
   uvma_obi_memory_slv_seq_c        instr_slv_seq;
   uvma_obi_memory_slv_seq_c        data_slv_seq;

   if (cfg.is_active) begin
      fork
         begin : spawn_obi_instr_fw_preload_thread
            fw_preload_seq = uvma_obi_memory_fw_preload_seq_c::type_id::create("fw_preload_seq");
            if (!fw_preload_seq.randomize()) begin
               `uvm_fatal("FWPRELOAD", "Randomize failed");
            end
            fw_preload_seq.start(obi_memory_instr_agent.sequencer);
         end

         begin : obi_instr_slv_thread
            instr_slv_seq = uvma_obi_memory_slv_seq_c::type_id::create("instr_slv_seq");
            if (!instr_slv_seq.randomize()) begin
               `uvm_fatal("INSTRSLVSEQ", "Randomize failed");
            end
            instr_slv_seq.start(obi_memory_instr_agent.sequencer);
         end

         begin : obi_data_slv_thread
            data_slv_seq = uvma_obi_memory_slv_seq_c::type_id::create("data_slv_seq");

            // Install the virtual peripheral registers
            void'(data_slv_seq.register_vp_vseq("vp_virtual_printer", 32'h1000_0000, uvma_obi_memory_vp_virtual_printer_seq_c::get_type()));
            void'(data_slv_seq.register_vp_vseq("vp_cycle_counter", 32'h1500_1004, uvma_obi_memory_vp_cycle_counter_seq_c::get_type()));

            // FIXME:strichmo:When RVVI/RVFI ported, the core-specific random number sequence is no longer needed
            // Use this one instead:
            //void'(data_slv_seq.register_vp_vseq("vp_rand_num", 32'h1500_1000, 1, uvma_obi_memory_vp_rand_num_seq_c::get_type()));
            begin
               uvme_cv32e40p_vp_rand_num_seq_c vp_seq;
               if (!$cast(vp_seq, data_slv_seq.register_vp_vseq("vp_rand_num", 32'h1500_1000, uvme_cv32e40p_vp_rand_num_seq_c::get_type()))) begin
                  `uvm_fatal("CV32E40PVPSEQ", $sformatf("Could not cast vp_rand_num correctly"));
               end
               vp_seq.cv32e40p_cntxt = cntxt;
            end

            begin
               uvme_cv32e40p_vp_sig_writer_seq_c vp_seq;
               if (!$cast(vp_seq, data_slv_seq.register_vp_vseq("vp_sig_writer", 32'h2000_0008, uvme_cv32e40p_vp_sig_writer_seq_c::get_type()))) begin
                  `uvm_fatal("CV32E40PVPSEQ", $sformatf("Could not cast vp_sig_writes correctly"));
               end
               vp_seq.cv32e40p_cntxt = cntxt;
            end

            begin
               uvme_cv32e40p_vp_status_flags_seq_c vp_seq;
               if (!$cast(vp_seq, data_slv_seq.register_vp_vseq("vp_status_flags", 32'h2000_0000, uvme_cv32e40p_vp_status_flags_seq_c::get_type()))) begin
                  `uvm_fatal("CV32E40PVPSEQ", $sformatf("Could not cast vp_status_flags correctly"));
               end
               vp_seq.cv32e40p_cntxt = cntxt;
            end

            begin
               uvme_cv32e40p_vp_interrupt_timer_seq_c vp_seq;
               if (!$cast(vp_seq, data_slv_seq.register_vp_vseq("vp_interrupt_timer", 32'h1500_0000, uvme_cv32e40p_vp_interrupt_timer_seq_c::get_type()))) begin
                  `uvm_fatal("CV32E40PVPSEQ", $sformatf("Could not cast vp_interrupt_timer correctly"));
               end
               vp_seq.cv32e40p_cntxt = cntxt;
            end

            begin
               uvme_cv32e40p_vp_debug_control_seq_c vp_seq;
               if (!$cast(vp_seq, data_slv_seq.register_vp_vseq("vp_debug_control", 32'h1500_0008, uvme_cv32e40p_vp_debug_control_seq_c::get_type()))) begin
                  `uvm_fatal("CV32E40PVPSEQ", $sformatf("Could not cast vp_debug_control correctly"));
               end
               vp_seq.cv32e40p_cntxt = cntxt;
            end

            if (!data_slv_seq.randomize()) begin
               `uvm_fatal("DATASLVSEQ", "Randomize failed");
            end
            data_slv_seq.start(obi_memory_data_agent.sequencer);
         end
      join_none
   end

endtask : run_phase


function void uvme_cv32e40p_env_c::end_of_elaboration_phase(uvm_phase phase);
   super.end_of_elaboration_phase(phase);

   `uvm_info("UVME_CV32E40P_ENV", $sformatf("Top-level environment configuration:\n%s", cfg.sprint()), UVM_LOW)

endfunction : end_of_elaboration_phase


function void uvme_cv32e40p_env_c::retrieve_vifs();

   if (!uvm_config_db#(virtual uvmt_cv32e40p_vp_status_if)::get(this, "", "vp_status_vif", cntxt.vp_status_vif)) begin
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

   void'(uvm_config_db#(virtual uvmt_cv32e40p_isa_covg_if)::get(this, "", "isa_covg_vif", cntxt.isa_covg_vif));
   if (cntxt.isa_covg_vif == null) begin
      `uvm_fatal("UVME_CV32E40P_ENV", $sformatf("No uvmt_cv32e40p_isa_covg_if found in config database"))
   end

   void'(uvm_config_db#(virtual uvmt_cv32e40p_debug_cov_assert_if)::get(this, "", "debug_cov_vif", cntxt.debug_cov_vif));
   if (cntxt.debug_cov_vif == null) begin
      `uvm_fatal("UVME_CV32E40P_ENV", $sformatf("No uvmt_cv32e40p_debug_cov_assert_if found in config database"))
   end

   // fixme:strichmo:This is a hack, that can be removed when RVFI/RVVI is enabled
   // This enables the vp_rnd_num_seq to backdoor update memories when a "volatile" register is read
   if (!uvm_config_db#(virtual RVVI_memory)::get(this, "", "rvvi_memory_vif", cntxt.rvvi_memory_vif)) begin
      `uvm_fatal("VIF", $sformatf("Could not find rvvi_memory_vif handle of type %s in uvm_config_db", $typename(cntxt.rvvi_memory_vif)))
   end
   else begin
      `uvm_info("VIF", $sformatf("Found rvvi_memory_vifhandle of type %s in uvm_config_db", $typename(cntxt.rvvi_memory_vif)), UVM_DEBUG)
   end

endfunction: retrieve_vifs


function void uvme_cv32e40p_env_c::assign_cfg();

   uvm_config_db#(uvme_cv32e40p_cfg_c)  ::set(this, "*",                      "cfg", cfg);
   uvm_config_db#(uvma_clknrst_cfg_c)   ::set(this, "*clknrst_agent",         "cfg", cfg.clknrst_cfg);
   uvm_config_db#(uvma_interrupt_cfg_c) ::set(this, "*interrupt_agent",       "cfg", cfg.interrupt_cfg);
   uvm_config_db#(uvma_debug_cfg_c)     ::set(this, "debug_agent",            "cfg", cfg.debug_cfg);
   uvm_config_db#(uvma_obi_memory_cfg_c)::set(this, "obi_memory_instr_agent", "cfg", cfg.obi_memory_instr_cfg);
   uvm_config_db#(uvma_obi_memory_cfg_c)::set(this, "obi_memory_data_agent",  "cfg", cfg.obi_memory_data_cfg);

endfunction: assign_cfg


function void uvme_cv32e40p_env_c::assign_cntxt();

   uvm_config_db#(uvme_cv32e40p_cntxt_c)  ::set(this, "*",                      "cntxt", cntxt);
   uvm_config_db#(uvma_clknrst_cntxt_c)   ::set(this, "clknrst_agent",          "cntxt", cntxt.clknrst_cntxt);
   uvm_config_db#(uvma_interrupt_cntxt_c) ::set(this, "interrupt_agent",        "cntxt", cntxt.interrupt_cntxt);
   uvm_config_db#(uvma_debug_cntxt_c)     ::set(this, "debug_agent",            "cntxt", cntxt.debug_cntxt);
   uvm_config_db#(uvma_obi_memory_cntxt_c)::set(this, "obi_memory_instr_agent", "cntxt", cntxt.obi_memory_instr_cntxt);
   uvm_config_db#(uvma_obi_memory_cntxt_c)::set(this, "obi_memory_data_agent",  "cntxt", cntxt.obi_memory_data_cntxt);

endfunction: assign_cntxt


function void uvme_cv32e40p_env_c::create_agents();

   clknrst_agent           = uvma_clknrst_agent_c   ::type_id::create("clknrst_agent",          this);
   interrupt_agent         = uvma_interrupt_agent_c ::type_id::create("interrupt_agent",        this);
   debug_agent             = uvma_debug_agent_c     ::type_id::create("debug_agent",            this);
   obi_memory_instr_agent  = uvma_obi_memory_agent_c::type_id::create("obi_memory_instr_agent", this);
   obi_memory_data_agent   = uvma_obi_memory_agent_c::type_id::create("obi_memory_data_agent",  this);

endfunction: create_agents


function void uvme_cv32e40p_env_c::create_env_components();

   if (cfg.scoreboarding_enabled) begin
      predictor = uvme_cv32e40p_prd_c::type_id::create("predictor", this);
      sb        = uvme_cv32e40p_sb_c ::type_id::create("sb"       , this);
   end

endfunction: create_env_components


function void uvme_cv32e40p_env_c::create_vsequencer();

   vsequencer = uvme_cv32e40p_vsqr_c::type_id::create("vsequencer", this);

endfunction: create_vsequencer


function void uvme_cv32e40p_env_c::create_cov_model();

   cov_model = uvme_cv32e40p_cov_model_c::type_id::create("cov_model", this);

endfunction: create_cov_model


function void uvme_cv32e40p_env_c::connect_predictor();

   //debug_agent.mon_ap.connect(predictor.debug_export);
   //clknrst_agent.mon_ap.connect(predictor.clknrst_export);
   // TODO Connect agents monitor analysis ports to predictor

endfunction: connect_predictor


function void uvme_cv32e40p_env_c::connect_scoreboard();

   // TODO Connect agents -> scoreboard
   //      Ex: debug_agent.mon_ap.connect(sb.debug_sb.act_export);

   // TODO Connect predictor -> scoreboard
   //      Ex: predictor.debug_ap.connect(sb.debug_sb.exp_export);

endfunction: connect_scoreboard


function void uvme_cv32e40p_env_c::connect_coverage_model();

   interrupt_agent.monitor.ap_iss.connect(cov_model.interrupt_covg.interrupt_mon_export);

endfunction: connect_coverage_model


function void uvme_cv32e40p_env_c::assemble_vsequencer();

   vsequencer.clknrst_sequencer          = clknrst_agent         .sequencer;
   vsequencer.interrupt_sequencer        = interrupt_agent       .sequencer;
   vsequencer.debug_sequencer            = debug_agent           .sequencer;
   vsequencer.obi_memory_instr_sequencer = obi_memory_instr_agent.sequencer;
   vsequencer.obi_memory_data_sequencer  = obi_memory_data_agent .sequencer;

endfunction: assemble_vsequencer


`endif // __UVME_CV32E40P_ENV_SV__

