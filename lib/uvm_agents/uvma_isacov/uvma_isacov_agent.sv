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

  //TLM RVFI
  uvm_analysis_export#(uvma_rvfi_instr_seq_item_c#(ILEN,XLEN)) rvfi_instr_export;

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
  rvfi_instr_export = new("rvfi_instr_export");

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

  if (cfg.enabled) begin
    rvfi_instr_export.connect(monitor.rvfi_instr_imp);
    if (cfg.cov_model_enabled) begin
      monitor.ap.connect(cov_model.mon_trn_fifo.analysis_export);
    end
    if (cfg.trn_log_enabled) begin
      monitor.ap.connect(mon_trn_logger.analysis_export);
    end
  end

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

endfunction : retrieve_vif


function void uvma_isacov_agent_c::create_components();

  if (cfg.enabled) begin
    monitor        = uvma_isacov_mon_c#(ILEN,XLEN)::type_id::create("monitor", this);
    if (cfg.cov_model_enabled) begin
      cov_model      = uvma_isacov_cov_model_c::type_id::create("cov_model", this);
    end
    if (cfg.trn_log_enabled) begin
      mon_trn_logger = uvma_isacov_mon_trn_logger_c::type_id::create("mon_trn_logger", this);
    end
    if (cfg.is_active==UVM_ACTIVE) begin
      `uvm_error("CFG", "Misconfiguration error: this agent should not be configured as an active agent")
    end
  end

endfunction : create_components
