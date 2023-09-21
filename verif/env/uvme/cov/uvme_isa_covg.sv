//
// Copyright 2023 OpenHW Group
// Copyright 2023 Thales
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

covergroup cg_rtype(
    string name,
    bit reg_crosses_enabled,
    bit reg_hazards_enabled,
    bit rs1_is_signed,
    bit rs2_is_signed,
    bit rd_is_signed
) with function sample (
    uvma_isacov_instr_c instr
);
  option.per_instance = 1;
  option.name = name;

  cp_rs1: coverpoint instr.rvfi.rs1_addr;
  cp_rs2: coverpoint instr.rvfi.rs2_addr;
  cp_rd: coverpoint instr.rvfi.rd1_addr;

  cp_rd_rs1_hazard: coverpoint instr.rvfi.rd1_addr {
    ignore_bins IGN_RS1_HAZARD_OFF = {[0:$]} `WITH (!reg_hazards_enabled);
    bins RD[] = {[0:31]} iff (instr.rvfi.rd1_addr == instr.rvfi.rs1_addr);
  }

  cp_rd_rs2_hazard: coverpoint instr.rvfi.rd1_addr {
    ignore_bins IGN_RS2_HAZARD_OFF = {[0:$]} `WITH (!reg_hazards_enabled);
    bins RD[] = {[0:31]} iff (instr.rvfi.rd1_addr == instr.rvfi.rs2_addr);
  }

  cross_rd_rs1_rs2: cross cp_rd, cp_rs1, cp_rs2 {
    ignore_bins IGN_OFF = cross_rd_rs1_rs2 `WITH (!reg_crosses_enabled);
  }

  cp_rs1_value: coverpoint instr.get_instr_value_type(instr.rvfi.rs1_rdata, $bits(instr.rvfi.rs1_rdata), 1) {
    ignore_bins POS_OFF = {POSITIVE} `WITH (!rs1_is_signed);
    ignore_bins NEG_OFF = {NEGATIVE} `WITH (!rs1_is_signed);
    ignore_bins NON_ZERO_OFF = {NON_ZERO} `WITH (rs1_is_signed);
  }

  cp_rs2_value: coverpoint instr.get_instr_value_type(instr.rvfi.rs2_rdata, $bits(instr.rvfi.rs2_rdata), 1) {
    ignore_bins POS_OFF = {POSITIVE} `WITH (!rs2_is_signed);
    ignore_bins NEG_OFF = {NEGATIVE} `WITH (!rs2_is_signed);
    ignore_bins NON_ZERO_OFF = {NON_ZERO} `WITH (rs2_is_signed);
  }

  cross_rs1_rs2_value: cross cp_rs1_value, cp_rs2_value;

  cp_rd_value: coverpoint instr.get_instr_value_type(instr.rvfi.rd1_wdata, $bits(instr.rvfi.rd1_wdata), 1) {
    ignore_bins POS_OFF = {POSITIVE} `WITH (!rd_is_signed);
    ignore_bins NEG_OFF = {NEGATIVE} `WITH (!rd_is_signed);
    ignore_bins NON_ZERO_OFF = {NON_ZERO} `WITH (rd_is_signed);
  }

  `ISACOV_CP_BITWISE(cp_rs1_toggle, instr.rvfi.rs1_rdata, 1)
  `ISACOV_CP_BITWISE(cp_rs2_toggle, instr.rvfi.rs2_rdata, 1)
  `ISACOV_CP_BITWISE(cp_rd_toggle,  instr.rvfi.rd1_wdata,  1)

endgroup : cg_rtype

class uvme_isa_cov_model_c extends uvm_component;

    /*
    * Class members
    */
   // Objects
   uvme_cva6_cfg_c         cfg      ;
   uvme_cva6_cntxt_c       cntxt    ;

   // TLM
   uvm_tlm_analysis_fifo#(uvma_isacov_mon_trn_c)  mon_trn_fifo;

   uvma_isacov_mon_trn_c mon_trn;

  `uvm_component_utils(uvme_isa_cov_model_c)

   //Zicond
   cg_rtype rv32zicond_czero_eqz_cg;
   cg_rtype rv32zicond_czero_nez_cg;

   extern function new(string name = "isa_cov_model", uvm_component parent = null);
   extern function void build_phase(uvm_phase phase);
   extern task run_phase(uvm_phase phase);

   extern task sample_isa(uvma_isacov_instr_c instr);

endclass : uvme_isa_cov_model_c

function uvme_isa_cov_model_c::new(string name = "isa_cov_model", uvm_component parent = null);

   super.new(name, parent);

endfunction : new

function void uvme_isa_cov_model_c::build_phase(uvm_phase phase);

   super.build_phase(phase);

   void'(uvm_config_db#(uvme_cva6_cfg_c)::get(this, "", "cfg", cfg));
   if (!cfg) begin
      `uvm_fatal("CFG", "Configuration handle is null")
   end

   if (cfg.ext_zicond_supported) begin
      rv32zicond_czero_eqz_cg    = new("rv32zicond_czero_eqz_cg",
                                       .reg_crosses_enabled(cfg.isacov_cfg.reg_crosses_enabled),
                                       .reg_hazards_enabled(cfg.isacov_cfg.reg_hazards_enabled),
                                       .rs1_is_signed(1),
                                       .rs2_is_signed(1),
                                       .rd_is_signed(1));

      rv32zicond_czero_nez_cg    = new("rv32zicond_czero_nez_cg",
                                       .reg_crosses_enabled(cfg.isacov_cfg.reg_crosses_enabled),
                                       .reg_hazards_enabled(cfg.isacov_cfg.reg_hazards_enabled),
                                       .rs1_is_signed(1),
                                       .rs2_is_signed(1),
                                       .rd_is_signed(1));
   end

   mon_trn_fifo   = new("mon_trn_fifo" , this);

endfunction : build_phase

task uvme_isa_cov_model_c::run_phase(uvm_phase phase);

  super.run_phase(phase);

   `uvm_info("ISACOVG", "The isa env coverage model is running", UVM_LOW);

  forever begin
      mon_trn_fifo.get(mon_trn);
      sample_isa(mon_trn.instr);
    end

endtask : run_phase

task uvme_isa_cov_model_c::sample_isa (uvma_isacov_instr_c instr);

  string instr_name;
  logic have_sampled = 0;

  logic is_ecall_or_ebreak =
    ( instr.rvfi.trap[ 8:3] ==  8)                              ||  // Ecall U-mode
    ( instr.rvfi.trap[ 8:3] == 11)                              ||  // Ecall M-mode
    ((instr.rvfi.trap[ 8:3] ==  3) && (instr.rvfi.trap[13:12] == 0)) ||  // Ebreak (ebreakm==0)
    ( instr.rvfi.trap[11:9] ==  1);                                 // Ebreak to* or in D-mode (* ebreakm==1)
  logic is_normal_instr =
    (instr.rvfi.trap[0] == 0) ||                              // No rvfi_trap
    ((instr.rvfi.trap[11:9] == 4) && (instr.rvfi.trap[1] == 0));   // Single-step, without any exception

   bit [63:0] instr_isa = $signed(instr.rvfi.insn);

   bit [6:0] opcode    = instr_isa [6:0];
   bit [6:0] func7     = instr_isa [31:25];
   bit [2:0] func3     = instr_isa [14:12];

  if (opcode == 7'b0110011) begin
     if (func7 == 7'b0000111) begin
       if (func3 == 3'b101) begin
          instr_name = "CZERO_EQZ";
       end
       else if (func3 == 3'b111) begin
          instr_name = "CZERO_NEZ";
       end
     end
  end

  if (!have_sampled && is_normal_instr && cfg.ext_zicond_supported) begin
    have_sampled = 1;
    case (instr_name)
      "CZERO_EQZ":   rv32zicond_czero_eqz_cg.sample(instr);
      "CZERO_NEZ":   rv32zicond_czero_nez_cg.sample(instr);
      default: have_sampled = 0;
    endcase
  end

endtask : sample_isa

