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


covergroup cg_btype(string name) with function sample (instr_c instr);
  option.per_instance = 1;
  option.name = name;

  cp_rs1: coverpoint instr.rs1;
  cp_rs2: coverpoint instr.rs2;
  cp_immb: coverpoint instr.immb;
endgroup : cg_btype


covergroup cg_utype(string name) with function sample (instr_c instr);
  option.per_instance = 1;
  option.name = name;

  cp_rd: coverpoint instr.rd;
  cp_immu: coverpoint instr.immu;
endgroup : cg_utype


covergroup cg_jtype(string name) with function sample (instr_c instr);
  option.per_instance = 1;
  option.name = name;

  cp_rd: coverpoint instr.rd;
  cp_immj: coverpoint instr.immj;
endgroup : cg_jtype


covergroup cg_cj(string name) with function sample (instr_c instr);
  option.per_instance = 1;
  option.name = name;

  cp_c_immj: coverpoint instr.c_immj;
endgroup : cg_cj


class uvma_isa_cov_model_c extends uvm_component;

  `uvm_component_utils(uvma_isa_cov_model_c)

  // Objects
  uvma_isa_cfg_c cfg;

  // Covergroups
  //32I:
  cg_rtype slli_cg;  // TODO own cg?
  cg_rtype srli_cg;  // TODO own cg?
  cg_rtype srai_cg;  // TODO own cg?
  cg_rtype add_cg;
  cg_rtype sub_cg;
  cg_rtype sll_cg;
  cg_rtype slt_cg;
  cg_rtype sltu_cg;
  cg_rtype xor_cg;
  cg_rtype srl_cg;
  cg_rtype sra_cg;
  cg_rtype or_cg;
  cg_rtype and_cg;
  cg_itype jalr_cg;
  cg_itype lb_cg;
  cg_itype lh_cg;
  cg_itype lw_cg;
  cg_itype lbu_cg;
  cg_itype lhu_cg;
  cg_itype addi_cg;
  cg_itype slti_cg;
  cg_itype sltiu_cg;
  cg_itype xori_cg;
  cg_itype ori_cg;
  cg_itype andi_cg;
  cg_itype fence_cg;  // TODO own cg?
  cg_itype ecall_cg;  // TODO own cg?
  cg_itype ebreak_cg;  // TODO own cg?
  cg_stype sb_cg;
  cg_stype sh_cg;
  cg_stype sw_cg;
  cg_btype beq_cg;
  cg_btype bne_cg;
  cg_btype blt_cg;
  cg_btype bge_cg;
  cg_btype bltu_cg;
  cg_btype bgeu_cg;
  cg_utype lui_cg;
  cg_utype auipc_cg;
  cg_jtype jal_cg;
  //32M:
  cg_rtype mul_cg;
  cg_rtype mulh_cg;
  cg_rtype mulhsu_cg;
  cg_rtype mulhu_cg;
  cg_rtype div_cg;
  cg_rtype divu_cg;
  cg_rtype rem_cg;
  cg_rtype remu_cg;
  //32C:
  cg_cj c_j_cg;
  cg_cj c_jal_cg;
  //Zicsr:
  cg_itype csrrw_cg;  // TODO define csr "imm" type
  //Zifence_i:
  cg_itype fence_i_cg;  // TODO own cg? (not itype)

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
    if (cfg.ext_i_enabled) begin
      lui_cg = new("lui_cg");
      auipc_cg = new("auipc_cg");
      jal_cg = new("jal_cg");
      jalr_cg = new("jalr_cg");

      beq_cg = new("beq_cg");
      bne_cg = new("bne_cg");
      blt_cg = new("blt_cg");
      bge_cg = new("bge_cg");
      bltu_cg = new("bltu_cg");
      bgeu_cg = new("bgeu_cg");

      lb_cg = new("lb_cg");
      lh_cg = new("lh_cg");
      lw_cg = new("lw_cg");
      lbu_cg = new("lbu_cg");
      lhu_cg = new("lhu_cg");
      sb_cg = new("sb_cg");
      sh_cg = new("sh_cg");
      sw_cg = new("sw_cg");

      addi_cg = new("addi_cg");
      slti_cg = new("slti_cg");
      sltiu_cg = new("sltiu_cg");
      xori_cg = new("xori_cg");
      ori_cg = new("ori_cg");
      andi_cg = new("andi_cg");
      slli_cg = new("slli_cg");
      srli_cg = new("srli_cg");
      srai_cg = new("srai_cg");

      add_cg = new("add_cg");
      sub_cg = new("sub_cg");
      sll_cg = new("sll_cg");
      slt_cg = new("slt_cg");
      sltu_cg = new("sltu_cg");
      xor_cg = new("xor_cg");
      srl_cg = new("srl_cg");
      sra_cg = new("sra_cg");
      or_cg = new("or_cg");
      and_cg = new("and_cg");

      fence_cg = new("fence_cg");
      ecall_cg = new("ecall_cg");
      ebreak_cg = new("ebreak_cg");
    end
    if (cfg.ext_m_enabled) begin
      mul_cg = new("mul_cg");
      mulh_cg = new("mulh_cg");
      mulhsu_cg = new("mulhsu_cg");
      mulhu_cg = new("mulhu_cg");
      div_cg = new("div_cg");
      divu_cg = new("divu_cg");
      rem_cg = new("rem_cg");
      remu_cg = new("remu_cg");
    end
    if (cfg.ext_c_enabled) begin
      c_j_cg   = new("c_j_cg");
      c_jal_cg = new("c_jal_cg");
    end
    if (cfg.ext_zicsr_enabled) begin
      csrrw_cg = new("csrrw_cg");
    end
    if (cfg.ext_zifencei_enabled) begin
      fence_i_cg = new("fence_i_cg");
    end
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

  logic have_sampled = 0;

  if (!have_sampled && cfg.ext_i_enabled) begin
    have_sampled = 1;
    case (instr.name)
      LUI:   lui_cg.sample(instr);
      AUIPC: auipc_cg.sample(instr);
      JAL:   jal_cg.sample(instr);
      JALR:  jalr_cg.sample(instr);

      BEQ:  beq_cg.sample(instr);
      BNE:  bne_cg.sample(instr);
      BLT:  blt_cg.sample(instr);
      BGE:  bge_cg.sample(instr);
      BLTU: bltu_cg.sample(instr);
      BGEU: bgeu_cg.sample(instr);

      LB:  lb_cg.sample(instr);
      LH:  lh_cg.sample(instr);
      LW:  lw_cg.sample(instr);
      LBU: lbu_cg.sample(instr);
      LHU: lhu_cg.sample(instr);
      SB:  sb_cg.sample(instr);
      SH:  sh_cg.sample(instr);
      SW:  sw_cg.sample(instr);

      ADDI:  addi_cg.sample(instr);
      SLTI:  slti_cg.sample(instr);
      SLTIU: sltiu_cg.sample(instr);
      XORI:  xori_cg.sample(instr);
      ORI:   ori_cg.sample(instr);
      ANDI:  andi_cg.sample(instr);
      SLLI:  slli_cg.sample(instr);
      SRLI:  srli_cg.sample(instr);
      SRAI:  srai_cg.sample(instr);

      ADD:  add_cg.sample(instr);
      SUB:  sub_cg.sample(instr);
      SLL:  sll_cg.sample(instr);
      SLT:  slt_cg.sample(instr);
      SLTU: sltu_cg.sample(instr);
      XOR:  xor_cg.sample(instr);
      SRL:  srl_cg.sample(instr);
      SRA:  sra_cg.sample(instr);
      OR:   or_cg.sample(instr);
      AND:  and_cg.sample(instr);

      FENCE:  fence_cg.sample(instr);
      ECALL:  ecall_cg.sample(instr);
      EBREAK: ebreak_cg.sample(instr);

      default: have_sampled = 0;
    endcase
  end

  if (!have_sampled && cfg.ext_m_enabled) begin
    have_sampled = 1;
    case (instr.name)
      MUL: mul_cg.sample(instr);
      MULH: mulh_cg.sample(instr);
      MULHSU: mulhsu_cg.sample(instr);
      MULHU: mulhu_cg.sample(instr);
      DIV: div_cg.sample(instr);
      DIVU: divu_cg.sample(instr);
      REM: rem_cg.sample(instr);
      REMU: remu_cg.sample(instr);
      default: have_sampled = 0;
    endcase
  end

  if (!have_sampled && cfg.ext_c_enabled) begin
    have_sampled = 1;
    case (instr.name)
      C_J: c_j_cg.sample(instr);
      C_JAL: c_jal_cg.sample(instr);
      // TODO rest of C
      default: have_sampled = 0;
    endcase
  end

  if (!have_sampled && cfg.ext_zicsr_enabled) begin
    have_sampled = 1;
    case (instr.name)
      CSRRW:   csrrw_cg.sample(instr);
      // TODO rest of Zicsr
      default: have_sampled = 0;
    endcase
  end

  if (!have_sampled && cfg.ext_zifencei_enabled) begin
    have_sampled = 1;
    case (instr.name)
      FENCE_I: fence_i_cg.sample(instr);
      default: have_sampled = 0;
    endcase
  end

  if (!have_sampled) begin
    $display("TODO error if no match found");
  end

endfunction
