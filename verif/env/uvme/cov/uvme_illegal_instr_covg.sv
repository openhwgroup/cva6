//
// Copyright 2024 OpenHW Group
// Copyright 2024 Thales
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

// Original Author: Ayoub JALALI (ayoub.jalali@external.thalesgroup.com)

covergroup cg_illegal_i(
    string name
) with function sample (
    uvma_isacov_instr_c instr
);
  option.per_instance = 1;
  option.name = name;

  cp_illegal_opcode: coverpoint instr.rvfi.insn[6:0] {
    bins ILLEGAL_OPCODE[3] = {[0:$]} with (!(item inside {legal_i_opcode}));
  }

  cp_illegal_funct3: coverpoint instr.rvfi.insn[14:12] { // if the instruction has funct3
    bins ILLEGAL_FUNCT3[3] = {[0:$]} iff (instr.rvfi.insn[6:0] inside {legal_i_opcode}); //with the right opcode
    bins ILLEGAL_NOPCODE_FUNCT3[3] = {[0:$]} iff (!(instr.rvfi.insn[6:0] inside {legal_i_opcode})); //with the wrong opcode
  }

  cp_illegal_funct7: coverpoint instr.rvfi.insn[31:25] { // if the instruction has funct7
    bins ILLEGAL_FUNCT7[3] = {[0:$]} with (!(item inside {legal_i_funct7})) iff (instr.rvfi.insn[6:0] inside {legal_i_opcode}); //with the right opcode
    bins ILLEGAL_NOPCODE_FUNCT7[3] = {[0:$]} with (!(item inside {legal_i_funct7})) iff (!(instr.rvfi.insn[6:0] inside {legal_i_opcode})); //with the wrong opcode
  }

  cp_is_illegal: coverpoint instr.cause {
    bins ILLEGAL_INSTR = {2};
  }

   cross_exc_illegal_0 : cross cp_illegal_opcode, cp_is_illegal;
   cross_exc_illegal_1 : cross cp_illegal_funct3, cp_is_illegal;
   cross_exc_illegal_2 : cross cp_illegal_funct7, cp_is_illegal;

endgroup : cg_illegal_i

covergroup cg_illegal_m(
    string name
) with function sample (
    uvma_isacov_instr_c instr
);
  option.per_instance = 1;
  option.name = name;

  cp_illegal_opcode: coverpoint instr.rvfi.insn[6:0] {
    bins ILLEGAL_OPCODE[2] = {[0:$]} with (item != 7'b0110011);
  }

  cp_illegal_funct3: coverpoint instr.rvfi.insn[14:12] { // if the instruction has funct3
    bins ILLEGAL_FUNCT3[3] = {[0:$]} iff (!(instr.rvfi.insn[6:0] == 7'b0110011 &
                                            instr.rvfi.insn[31:25] == 7'b0000001)); //with the wrong opcode or the wrong funct7
  }

  cp_illegal_funct7: coverpoint instr.rvfi.insn[31:25] { // if the instruction has funct7
    bins ILLEGAL_FUNCT7[3] = {[0:$]} with (item != 7'b0000001) iff (instr.rvfi.insn[6:0] == 7'b0110011); //with the right opcode
    bins ILLEGAL_NOPCODE_FUNCT7[3] = {[0:$]} with (item != 7'b0000001) iff (instr.rvfi.insn[6:0] != 7'b0110011); //with the wrong opcode
  }

  cp_is_illegal: coverpoint instr.cause {
    bins ILLEGAL_INSTR = {2};
  }

   cross_exc_illegal_0 : cross cp_illegal_opcode, cp_is_illegal;
   cross_exc_illegal_1 : cross cp_illegal_funct3, cp_is_illegal;
   cross_exc_illegal_2 : cross cp_illegal_funct7, cp_is_illegal;

endgroup : cg_illegal_m

covergroup cg_illegal_zicsr(
    string name
) with function sample (
    uvma_isacov_instr_c instr
);
  option.per_instance = 1;
  option.name = name;

  cp_illegal_opcode: coverpoint instr.rvfi.insn[6:0] {
    bins ILLEGAL_OPCODE[2] = {[0:$]} with (item != 7'b1110011);
  }

  cp_illegal_funct3: coverpoint instr.rvfi.insn[14:12] { // if the instruction has funct3
    bins ILLEGAL_FUNCT3 = {0,4} iff (instr.rvfi.insn[6:0] == 7'b1110011); //with the right opcode
    bins ILLEGAL_NOPCODE_FUNCT3 = {0,4} iff (instr.rvfi.insn[6:0] != 7'b1110011); //with the wrong opcode
  }

  cp_is_illegal: coverpoint instr.cause {
    bins ILLEGAL_INSTR = {2};
  }

   cross_exc_illegal_0 : cross cp_illegal_opcode, cp_is_illegal;
   cross_exc_illegal_1 : cross cp_illegal_funct3, cp_is_illegal;

endgroup : cg_illegal_zicsr

covergroup cg_illegal_zifencei(
    string name
) with function sample (
    uvma_isacov_instr_c instr
);
  option.per_instance = 1;
  option.name = name;

  cp_illegal_opcode: coverpoint instr.rvfi.insn[6:0] {
    bins ILLEGAL_OPCODE[2] = {[0:$]} with (item != 7'b0001111);
  }

  cp_illegal_funct3: coverpoint instr.rvfi.insn[14:12] { // if the instruction has funct3
    bins ILLEGAL_FUNCT3[3] = {[0:$]} with (item != 7'b001) iff (instr.rvfi.insn[6:0] == 7'b0001111); //with the right opcode
    bins ILLEGAL_NOPCODE_FUNCT3[3] = {[0:$]} with (item != 7'b001) iff (instr.rvfi.insn[6:0] != 7'b0001111); //with the wrong opcode
  }

  cp_is_illegal: coverpoint instr.cause {
    bins ILLEGAL_INSTR = {2};
  }

   cross_exc_illegal_0 : cross cp_illegal_opcode, cp_is_illegal;
   cross_exc_illegal_1 : cross cp_illegal_funct3, cp_is_illegal;

endgroup : cg_illegal_zifencei

class uvme_illegal_instr_cov_model_c extends uvm_component;

    /*
    * Class members
    */
   // Objects
   uvme_cva6_cfg_c         cfg      ;
   uvme_cva6_cntxt_c       cntxt    ;

   // TLM
   uvm_tlm_analysis_fifo#(uvma_isacov_mon_trn_c)  mon_trn_fifo;

   uvma_isacov_mon_trn_c mon_trn;

  `uvm_component_utils(uvme_illegal_instr_cov_model_c)

   //Covergroup of Illegal instrcution
   cg_illegal_i          illegal_i_cg;
   cg_illegal_m          illegal_m_cg;
   cg_illegal_zicsr      illegal_zicsr_cg;
   cg_illegal_zifencei   illegal_zifencei_cg;

   extern function new(string name = "illegal_cov_model", uvm_component parent = null);
   extern function void build_phase(uvm_phase phase);
   extern task run_phase(uvm_phase phase);

   extern task sample_isa(uvma_isacov_instr_c instr);

endclass : uvme_illegal_instr_cov_model_c

function uvme_illegal_instr_cov_model_c::new(string name = "illegal_cov_model", uvm_component parent = null);

   super.new(name, parent);

endfunction : new

function void uvme_illegal_instr_cov_model_c::build_phase(uvm_phase phase);

   super.build_phase(phase);

   void'(uvm_config_db#(uvme_cva6_cfg_c)::get(this, "", "cfg", cfg));
   if (!cfg) begin
      `uvm_fatal("CFG", "Configuration handle is null")
   end

   if (cfg.ext_i_supported) begin
      illegal_i_cg         = new("illegal_i_cg");
   end

   if (cfg.ext_m_supported) begin
      illegal_m_cg         = new("illegal_m_cg");
   end

   if (cfg.ext_zicsr_supported) begin
      illegal_zicsr_cg     = new("illegal_zicsr_cg");
   end

   if (cfg.ext_zifencei_supported) begin
      illegal_zifencei_cg  = new("illegal_zifencei_cg");
   end

   mon_trn_fifo   = new("mon_trn_fifo" , this);

endfunction : build_phase

task uvme_illegal_instr_cov_model_c::run_phase(uvm_phase phase);

  super.run_phase(phase);

   `uvm_info("ILLEGAL_INSTR_COVG", "The illegal instruction env coverage model is running", UVM_LOW);

  forever begin
      mon_trn_fifo.get(mon_trn);
      sample_isa(mon_trn.instr);
    end

endtask : run_phase

task uvme_illegal_instr_cov_model_c::sample_isa (uvma_isacov_instr_c instr);

  string instr_name;
  logic have_sampled = 0;

  logic is_illegal_instr = (instr.cause == 2);

  if (is_illegal_instr && cfg.ext_i_supported) begin
    illegal_i_cg.sample(instr);
    have_sampled = 1;
  end
  if (is_illegal_instr && cfg.ext_m_supported) begin
    illegal_m_cg.sample(instr);
    have_sampled = 1;
  end
  if (is_illegal_instr && cfg.ext_zicsr_supported) begin
    illegal_zicsr_cg.sample(instr);
    have_sampled = 1;
  end
  if (is_illegal_instr && cfg.ext_zifencei_supported) begin
    illegal_zifencei_cg.sample(instr);
    have_sampled = 1;
  end
  if (!have_sampled && is_illegal_instr) begin
    `uvm_error("ILLEGAL_INSTR", $sformatf("Could not sample instruction: %h", instr.rvfi.insn));
  end

endtask : sample_isa

