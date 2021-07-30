// Copyright 2021 OpenHW Group
// Copyright 2021 Silicon Labs, Inc.
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

class uvma_isacov_agent_c#(int ILEN=DEFAULT_ILEN,
                           int XLEN=DEFAULT_XLEN) extends uvm_agent;

  `uvm_component_param_utils(uvma_isacov_agent_c);

  // Objects
  uvma_isacov_cfg_c                          cfg;
  uvma_isacov_cntxt_c                        cntxt;

  // Components
  uvma_isacov_mon_c#(ILEN,XLEN)              monitor;
  uvma_isacov_cov_model_c                    cov_model;
  uvma_isacov_mon_trn_logger_c               mon_trn_logger;

  // TLM
  uvm_analysis_port #(uvma_isacov_mon_trn_c) mon_ap;

  // Methods
  extern function new(string name = "uvma_isacov_agent", uvm_component parent = null);
  extern virtual function void build_phase(uvm_phase phase);
  extern virtual function void connect_phase(uvm_phase phase);
  extern function void get_and_set_cfg();
  extern function void get_and_set_cntxt();
  extern function void retrieve_vif();
  extern function void create_components();

endclass : uvma_isacov_agent_c


function uvma_isacov_agent_c::new(string name = "uvma_isacov_agent", uvm_component parent = null);

  super.new(name, parent);

endfunction : new

function void uvma_isacov_agent_c::build_phase(uvm_phase phase);

  super.build_phase(phase);

  get_and_set_cfg();
  get_and_set_cntxt();
  retrieve_vif();
  create_components();

endfunction : build_phase


function void uvma_isacov_agent_c::connect_phase(uvm_phase phase);

  super.connect_phase(phase);

  // TODO if cov_model_enabled and if trn_log_enabled
  mon_ap = monitor.ap;
  mon_ap.connect(cov_model.mon_trn_fifo.analysis_export);  //TODO if cfg...enabled
  mon_ap.connect(mon_trn_logger.analysis_export);  // TODO if cfg...enabled

endfunction : connect_phase


function void uvma_isacov_agent_c::get_and_set_cfg();

  void'(uvm_config_db#(uvma_isacov_cfg_c)::get(this, "", "cfg", cfg));
  if (!cfg) begin
    `uvm_fatal("CFG", "Configuration handle is null")
  end else begin
    `uvm_info("CFG", $sformatf("Found configuration handle:\n%s", cfg.sprint()), UVM_DEBUG)
    uvm_config_db#(uvma_isacov_cfg_c)::set(this, "*", "cfg", cfg);
  end

endfunction : get_and_set_cfg


function void uvma_isacov_agent_c::get_and_set_cntxt();

  void'(uvm_config_db#(uvma_isacov_cntxt_c)::get(this, "", "cntxt", cntxt));
  if (!cntxt) begin
    `uvm_info("CNTXT", "Context handle is null; creating.", UVM_DEBUG)
    cntxt = uvma_isacov_cntxt_c::type_id::create("cntxt");
  end
  uvm_config_db#(uvma_isacov_cntxt_c)::set(this, "*", "cntxt", cntxt);

endfunction : get_and_set_cntxt


function void uvma_isacov_agent_c::retrieve_vif();

  if (!uvm_config_db#(virtual uvma_isacov_if)::get(this, "", "vif", cntxt.vif)) begin
    `uvm_fatal("VIF", $sformatf(
               "Could not find vif handle of type %s in uvm_config_db", $typename(cntxt.vif)))
  end else begin
    `uvm_info("VIF", $sformatf("Found vif handle of type %s in uvm_config_db", $typename(cntxt.vif)
              ), UVM_DEBUG)
  end

endfunction : retrieve_vif


function void uvma_isacov_agent_c::create_components();

  monitor        = uvma_isacov_mon_c#(ILEN,XLEN)::type_id::create("monitor", this);
  cov_model      = uvma_isacov_cov_model_c::type_id::create("cov_model", this);
  mon_trn_logger = uvma_isacov_mon_trn_logger_c::type_id::create("mon_trn_logger", this);

endfunction : create_components
