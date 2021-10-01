// Copyright 2021 OpenHW Group
// Copyright 2021 Datum Technology Corporation
// Copyright 2021 Silicon Labs
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
// Licensed under the Solderpad Hardware License v 2.1 (the "License"); you may not use this file except in compliance
// with the License, or, at your option, the Apache License version 2.0.  You may obtain a copy of the License at
//                                        https://solderpad.org/licenses/SHL-2.1/
// Unless required by applicable law or agreed to in writing, any work distributed under the License is distributed on
// an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.  See the License for the
// specific language governing permissions and limitations under the License.
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////


`ifndef __UVMA_OBI_AGENT_SV__
`define __UVMA_OBI_AGENT_SV__


/**
 * Top-level component that encapsulates, builds and connects all others.  Capable of driving/monitoring the Open Bus
 * Interface.
 */
class uvma_obi_agent_c extends uvm_agent;
   
   // Objects
   uvma_obi_cfg_c    cfg  ; ///< Agent configuration handle
   uvma_obi_cntxt_c  cntxt; ///< Agent context handle
   
   // Components
   uvma_obi_drv_c        driver    ; ///< TODO Describe uvma_obi_agent_c::driver
   uvma_obi_mon_c        monitor   ; ///< TODO Describe uvma_obi_agent_c::monitor
   uvma_obi_vsqr_c       vsequencer; ///< TODO Describe uvma_obi_agent_c::vsequencer
   uvma_obi_logger_c     logger    ; ///< TODO Describe uvma_obi_agent_c::logger
   uvma_obi_cov_model_c  cov_model ; ///< TODO Describe uvma_obi_agent_c::cov_model
   
   // TLM
   uvm_analysis_port#(uvma_obi_mon_trn_c        )  mon_trn_ap   ; ///< TODO Describe uvma_obi_agent_c::mon_trn_ap
   uvm_analysis_port#(uvma_obi_seq_item_c       )  seq_item_ap  ; ///< TODO Describe uvma_obi_agent_c::seq_item_ap
   uvm_analysis_port#(uvma_obi_mstr_a_seq_item_c)  drv_mstr_a_ap; ///< TODO Describe uvma_obi_agent_c::drv_mstr_a_ap
   uvm_analysis_port#(uvma_obi_mstr_r_seq_item_c)  drv_mstr_r_ap; ///< TODO Describe uvma_obi_agent_c::drv_mstr_r_ap
   uvm_analysis_port#(uvma_obi_slv_a_seq_item_c )  drv_slv_a_ap ; ///< TODO Describe uvma_obi_agent_c::drv_slv_a_ap
   uvm_analysis_port#(uvma_obi_slv_r_seq_item_c )  drv_slv_r_ap ; ///< TODO Describe uvma_obi_agent_c::drv_slv_r_ap
   uvm_analysis_port#(uvma_obi_mstr_a_mon_trn_c )  mon_mstr_a_ap; ///< TODO Describe uvma_obi_agent_c::mon_mstr_a_ap
   uvm_analysis_port#(uvma_obi_mstr_r_mon_trn_c )  mon_mstr_r_ap; ///< TODO Describe uvma_obi_agent_c::mon_mstr_r_ap
   uvm_analysis_port#(uvma_obi_slv_a_mon_trn_c  )  mon_slv_a_ap ; ///< TODO Describe uvma_obi_agent_c::mon_slv_a_ap
   uvm_analysis_port#(uvma_obi_slv_r_mon_trn_c  )  mon_slv_r_ap ; ///< TODO Describe uvma_obi_agent_c::mon_slv_r_ap
   
   
   `uvm_component_utils_begin(uvma_obi_agent_c)
      `uvm_field_object(cfg  , UVM_DEFAULT)
      `uvm_field_object(cntxt, UVM_DEFAULT)
   `uvm_component_utils_end
   
   
   /**
    * Default constructor.
    */
   extern function new(string name="uvma_obi_agent", uvm_component parent=null);
   
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
    * TODO Describe uvma_obi_agent_c::run_phase()
    */
   extern virtual task run_phase(uvm_phase phase);
   
   /**
    * Uses uvm_config_db to retrieve cfg and hand out to sub-components.
    */
   extern function void get_and_set_cfg();
   
   /**
    * Uses uvm_config_db to retrieve cntxt and hand out to sub-components.
    */
   extern function void get_and_set_cntxt();
   
   /**
    * Uses uvm_config_db to retrieve the Virtual Interface (vif) associated with this agent.
    */
   extern function void retrieve_vif();
   
   /**
    * Creates sub-components.
    */
   extern function void create_components();
   
   /**
    * Connects sequencer to monitor and driver's TLM ports.
    */
   extern function void connect_sequencer;
   
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
   extern function void connect_trn_logger();
   
   /**
    * TODO Describe uvma_obi_agent_c::start_mon_vseq()
    */
   extern task start_mon_vseq();
   
   /**
    * TODO Describe uvma_obi_agent_c::start_idle_vseq()
    */
   extern task start_idle_vseq();
   
   /**
    * TODO Describe uvma_obi_agent_c::start_mstr_vseq()
    */
   extern task start_mstr_vseq();
   
   /**
    * TODO Describe uvma_obi_agent_c::start_slv_vseq()
    */
   extern task start_slv_vseq();
   
endclass : uvma_obi_agent_c


function uvma_obi_agent_c::new(string name="uvma_obi_agent", uvm_component parent=null);
   
   super.new(name, parent);
   
endfunction : new


function void uvma_obi_agent_c::build_phase(uvm_phase phase);
   
   super.build_phase(phase);
   
   get_and_set_cfg  ();
   get_and_set_cntxt();
   retrieve_vif     ();
   create_components();
   
endfunction : build_phase


function void uvma_obi_agent_c::connect_phase(uvm_phase phase);
   
   super.connect_phase(phase);
   
   connect_sequencer     ();
   connect_analysis_ports();
   
   if (cfg.cov_model_enabled) begin
      connect_cov_model();
   end
   if (cfg.trn_log_enabled) begin
      connect_trn_logger();
   end
   
endfunction: connect_phase


task uvma_obi_agent_c::run_phase(uvm_phase phase);
   
   super.run_phase(phase);
   
   if (cfg.enabled) begin
      start_mon_vseq();
      
      if (cfg.is_active) begin
         start_idle_vseq();
         
         case (cfg.drv_mode)
            UVMA_OBI_DRV_MODE_MSTR: start_mstr_vseq();
            UVMA_OBI_DRV_MODE_SLV : start_slv_vseq ();
            
            default: begin
               `uvm_fatal("OBI_AGENT", $sformatf("Invalid cfg.drv_mode: %s", cfg.drv_mode.name()))
            end
         endcase
      end
   end
   
endtask : run_phase


function void uvma_obi_agent_c::get_and_set_cfg();
   
   void'(uvm_config_db#(uvma_obi_cfg_c)::get(this, "", "cfg", cfg));
   if (!cfg) begin
      `uvm_fatal("CFG", "Configuration handle is null")
   end
   else begin
      `uvm_info("CFG", $sformatf("Found configuration handle:\n%s", cfg.sprint()), UVM_DEBUG)
      uvm_config_db#(uvma_obi_cfg_c)::set(this, "*", "cfg", cfg);
   end
   
endfunction : get_and_set_cfg


function void uvma_obi_agent_c::get_and_set_cntxt();
   
   void'(uvm_config_db#(uvma_obi_cntxt_c)::get(this, "", "cntxt", cntxt));
   if (!cntxt) begin
      `uvm_info("CNTXT", "Context handle is null; creating.", UVM_DEBUG)
      cntxt = uvma_obi_cntxt_c::type_id::create("cntxt");
   end
   uvm_config_db#(uvma_obi_cntxt_c)::set(this, "*", "cntxt", cntxt);
   
endfunction : get_and_set_cntxt


function void uvma_obi_agent_c::retrieve_vif();
   
   if (!uvm_config_db#(virtual uvma_obi_if)::get(this, "", "vif", cntxt.vif)) begin
      `uvm_fatal("VIF", $sformatf("Could not find vif handle of type %s in uvm_config_db", $typename(cntxt.vif)))
   end
   else begin
      `uvm_info("VIF", $sformatf("Found vif handle of type %s in uvm_config_db", $typename(cntxt.vif)), UVM_DEBUG)
   end
   
endfunction : retrieve_vif


function void uvma_obi_agent_c::create_components();
   
   monitor    = uvma_obi_mon_c      ::type_id::create("monitor"   , this);
   vsequencer = uvma_obi_vsqr_c     ::type_id::create("vsequencer", this);
   driver     = uvma_obi_drv_c      ::type_id::create("driver"    , this);
   cov_model  = uvma_obi_cov_model_c::type_id::create("cov_model" , this);
   logger     = uvma_obi_logger_c   ::type_id::create("logger"    , this);
   
endfunction : create_components


function void uvma_obi_agent_c::connect_sequencer();
   
   sequencer.set_arbitration(cfg.sqr_arb_mode);
   driver.mstr_a_driver.seq_item_port.connect(vsequencer.mstr_a_sequencer.seq_item_export);
   driver.mstr_r_driver.seq_item_port.connect(vsequencer.mstr_r_sequencer.seq_item_export);
   driver.slv_a_driver .seq_item_port.connect(vsequencer.slv_a_sequencer .seq_item_export);
   driver.slv_r_driver .seq_item_port.connect(vsequencer.slv_r_sequencer .seq_item_export);
   monitor.mon_mstr_a_ap.connect(vsequencer.mstr_a_mon_trn_export);
   monitor.mon_mstr_r_ap.connect(vsequencer.mstr_r_mon_trn_export);
   monitor.mon_slv_a_ap .connect(vsequencer.slv_a_mon_trn_export );
   monitor.mon_slv_r_ap .connect(vsequencer.slv_r_mon_trn_export );
   
endfunction : connect_sequencer


function void uvma_obi_agent_c::connect_analysis_ports();
   
   mon_trn_ap    = vsequencer.mon_trn_ap  ;
   seq_item_ap   = vsequencer.seq_item_ap ;
   drv_mstr_a_ap = driver.mstr_a_driver.ap;
   drv_mstr_r_ap = driver.mstr_r_driver.ap;
   drv_slv_a_ap  = driver.slv_a_driver .ap;
   drv_slv_r_ap  = driver.slv_r_driver .ap;
   mon_mstr_a_ap = monitor.mon_mstr_a_ap  ;
   mon_mstr_r_ap = monitor.mon_mstr_r_ap  ;
   mon_slv_a_ap  = monitor.mon_slv_a_ap   ;
   mon_slv_r_ap  = monitor.mon_slv_r_ap   ;
   
endfunction : connect_analysis_ports


function void uvma_obi_agent_c::connect_cov_model();
   
   seq_item_ap.connect(cov_model.seq_item_fifo.analysis_export);
   mon_trn_ap .connect(cov_model.mon_trn_fifo .analysis_export);
   
endfunction : connect_cov_model


function void uvma_obi_agent_c::connect_logger();
   
   seq_item_ap.connect(logger.seq_item_logger.analysis_export);
   mon_trn_ap .connect(logger.mon_trn_logger .analysis_export);
   
endfunction : connect_logger


task uvma_obi_agent_c::start_mon_vseq();
   
   uvm_sequence  mon_vseq;
   uvm_object    temp_obj;
   temp_obj = cfg.monitor_vseq_type.create_object("mon_vseq");
   if (!$cast(mon_vseq, temp_obj)) begin
      `uvm_fatal("OBI_AGENT", $sformatf("Could not cast 'temp_obj' (%s) to 'mon_vseq' (%s)", $typename(temp_obj), $typename(mon_vseq)))
   end
   
   if (!mon_vseq.randomize()) begin
      `uvm_fatal("OBI_AGENT", "Failed to randomize mon_vseq")
   end
   
   fork
      mon_vseq.start(vsequencer);
   join_none
   
endtask : start_mon_vseq


task uvma_obi_agent_c::start_idle_vseq();
   
   uvm_sequence  idle_vseq;
   uvm_object    temp_obj;
   
   temp_obj = cfg.idle_vseq_type.create_object("idle_vseq");
   if (!$cast(idle_vseq, temp_obj)) begin
      `uvm_fatal("OBI_AGENT", $sformatf("Could not cast 'temp_obj' (%s) to 'idle_vseq' (%s)", $typename(temp_obj), $typename(idle_vseq)))
   end
   
   if (!idle_vseq.randomize()) begin
      `uvm_fatal("OBI_AGENT", "Failed to randomize idle_vseq")
   end
   
   fork
      idle_vseq.start(vsequencer);
   join_none
   
endtask : start_idle_vseq


task uvma_obi_agent_c::start_mstr_vseq();
   
   uvm_sequence  mstr_vseq;
   uvm_object    temp_obj;
   
   temp_obj = cfg.mstr_vseq_type.create_object("mstr_vseq");
   if (!$cast(mstr_vseq, temp_obj)) begin
      `uvm_fatal("OBI_AGENT", $sformatf("Could not cast 'temp_obj' (%s) to 'mstr_vseq' (%s)", $typename(temp_obj), $typename(mstr_vseq)))
   end
   
   if (!mstr_vseq.randomize()) begin
      `uvm_fatal("OBI_AGENT", "Failed to randomize mstr_vseq")
   end
   
   fork
      mstr_vseq.start(vsequencer);
   join_none
   
endtask : start_mstr_vseq


task uvma_obi_agent_c::start_slv_vseq();
   
   uvm_sequence  slv_vseq;
   uvm_object    temp_obj;
   
   temp_obj = cfg.slv_vseq_type.create_object("slv_vseq");
   if (!$cast(slv_vseq, temp_obj)) begin
      `uvm_fatal("OBI_AGENT", $sformatf("Could not cast 'temp_obj' (%s) to 'slv_vseq' (%s)", $typename(temp_obj), $typename(slv_vseq)))
   end
   
   if (!slv_vseq.randomize()) begin
      `uvm_fatal("OBI_AGENT", "Failed to randomize slv_vseq")
   end
   
   fork
      slv_vseq.start(vsequencer);
   join_none
   
endtask : start_slv_vseq


`endif // __UVMA_OBI_AGENT_SV__
