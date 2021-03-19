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


covergroup cg_rtype(string name) with function sample (instr_c instr);
  option.per_instance = 1;
  option.name = name;

  cp_rs1: coverpoint instr.rs1;
  cp_rs2: coverpoint instr.rs2;
  cp_rd: coverpoint instr.rd;
endgroup : cg_rtype


covergroup cg_itype(string name) with function sample (instr_c instr);
  option.per_instance = 1;
  option.name = name;

  cp_rs1: coverpoint instr.rs1;
  cp_rd: coverpoint instr.rd;
  cp_immi: coverpoint instr.immi;
endgroup : cg_itype


covergroup cg_stype(string name) with function sample (instr_c instr);
  option.per_instance = 1;
  option.name = name;

  cp_rs1: coverpoint instr.rs1;
  cp_rs2: coverpoint instr.rs2;
  cp_imms: coverpoint instr.imms;
endgroup : cg_stype


covergroup cg_utype(string name) with function sample (instr_c instr);
  option.per_instance = 1;
  option.name = name;

  cp_rd: coverpoint instr.rd;
  cp_immu: coverpoint instr.immu;
endgroup : cg_utype


class uvma_isa_cov_model_c extends uvm_component;

  `uvm_component_utils(uvma_isa_cov_model_c)

  // Objects
  uvma_isa_cfg_c cfg;

  // Covergroups
  cg_itype addi_cg;  // TODO only if feature flag?
  cg_itype ori_cg;
  cg_utype auipc_cg;
  cg_stype sw_cg;
  cg_rtype xor_cg;
  cg_rtype mulh_cg;
  cg_rtype divu_cg;

  // TLM
  uvm_tlm_analysis_fifo #(uvma_isa_mon_trn_c) mon_trn_fifo;

  extern function new(string name = "uvma_isa_cov_model", uvm_component parent = null);
  extern virtual function void build_phase(uvm_phase phase);
  extern virtual task run_phase(uvm_phase phase);
  extern function void sample (instr_c instr);

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
    addi_cg = new("addi_cg");
    ori_cg  = new("ori_cg");
    auipc_cg = new("auipc_cg");
    sw_cg = new("sw_cg");
    xor_cg = new("xor_cg");
    mulh_cg = new("mulh_cg");
    divu_cg = new("divu_cg");
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
        sample (mon_trn.instr);
      end
    join_none
  end

endtask : run_phase


function void uvma_isa_cov_model_c::sample (instr_c instr);

  case (instr.name)
    ADDI: addi_cg.sample(instr);
    ORI:  ori_cg.sample(instr);
    AUIPC: auipc_cg.sample(instr);
    SW: sw_cg.sample(instr);
    XOR: xor_cg.sample(instr);
    MULH: mulh_cg.sample(instr);
    DIVU: divu_cg.sample(instr);
    // TODO default
  endcase

endfunction
