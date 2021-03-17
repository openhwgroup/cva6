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


class uvma_isa_cov_model_c extends uvm_component;

  `uvm_component_utils(uvma_isa_cov_model_c)

  // Objects
  uvma_isa_cfg_c cfg;

  // TLM
  uvm_tlm_analysis_fifo #(uvma_isa_mon_trn_c) mon_trn_fifo;

  extern function new(string name = "uvma_isa_cov_model", uvm_component parent = null);
  extern virtual function void build_phase(uvm_phase phase);
  extern virtual task run_phase(uvm_phase phase);

endclass : uvma_isa_cov_model_c


function uvma_isa_cov_model_c::new(string name = "uvma_isa_cov_model", uvm_component parent = null);

  super.new(name, parent);

endfunction : new


function void uvma_isa_cov_model_c::build_phase(uvm_phase phase);

  super.build_phase(phase);

  void'(uvm_config_db#(uvma_isa_cfg_c)::get(this, "", "cfg", cfg));
  if (!cfg) begin
    `uvm_fatal("CFG", "Configuration handle is null")
  end

  if (cfg.enabled && cfg.cov_model_enabled) begin
    //TODO instr_cg = new();
  end

  mon_trn_fifo = new("mon_trn_fifo", this);

endfunction : build_phase


task uvma_isa_cov_model_c::run_phase(uvm_phase phase);

  super.run_phase(phase);

  if (cfg.enabled && cfg.cov_model_enabled) begin
    fork
      forever begin
        uvma_isa_mon_trn_c mon_trn;

        mon_trn_fifo.get(mon_trn);
        $display("TODO sample_mon_trn()");
        $display("TODO rs1 = %0d", mon_trn.instr.rs1);
      end
    join_none
  end

endtask : run_phase
