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


class uvma_isacov_mon_c extends uvm_monitor;

  `uvm_component_utils(uvma_isacov_mon_c);

  uvma_isacov_cntxt_c                        cntxt;
  uvm_analysis_port #(uvma_isacov_mon_trn_c) ap;

  extern function new(string name = "uvma_isacov_mon", uvm_component parent = null);
  extern virtual function void build_phase(uvm_phase phase);
  extern virtual task run_phase(uvm_phase phase);

endclass : uvma_isacov_mon_c


function uvma_isacov_mon_c::new(string name = "uvma_isacov_mon", uvm_component parent = null);

  super.new(name, parent);

endfunction : new


function void uvma_isacov_mon_c::build_phase(uvm_phase phase);

  super.build_phase(phase);

  void'(uvm_config_db#(uvma_isacov_cntxt_c)::get(this, "", "cntxt", cntxt));
  if (!cntxt) begin
    `uvm_fatal("CNTXT", "Context handle is null")
  end

  ap = new("ap", this);

  `ifdef COV
    dasm_set_config(32, "rv32imc", 0);
  `endif

endfunction : build_phase


task uvma_isacov_mon_c::run_phase(uvm_phase phase);

  super.run_phase(phase);

`ifdef COV
  // TODO if cfg.enabled, while 1, wait cntxt.vif.reset, ...
  fork
    begin
      forever begin
        uvma_isacov_mon_trn_c mon_trn;

        @(cntxt.vif.retire);

        mon_trn = new();
        mon_trn.instr = new();
$display("TODO got instr: ", dasm_name(cntxt.vif.insn), " at ", $time);
        mon_trn.instr.name =
          (cntxt.vif.insn[6:0] == 7'b00_100_11) ? // OP-IMM
            (cntxt.vif.insn[14:12] == 3'b000) ?
              ADDI :
            (cntxt.vif.insn[14:12] == 3'b110) ?
              ORI :
            UNKNOWN :
          (cntxt.vif.insn[6:0] == 7'b00_101_11) ? // AUIPC
            AUIPC :
          (cntxt.vif.insn[6:0] == 7'b11_011_11) ? // JAL
            JAL :
          (cntxt.vif.insn[6:0] == 7'b01_000_11) ? // STORE
            (cntxt.vif.insn[14:12] == 3'b010) ?
              SW :
            UNKNOWN :
          (cntxt.vif.insn[6:0] == 7'b01_100_11) ? // OP
            ((cntxt.vif.insn[14:12] == 3'b100) && (cntxt.vif.insn[31:25] == 7'b0)) ?
              XOR :
            ((cntxt.vif.insn[14:12] == 3'b001) && (cntxt.vif.insn[31:25] == 7'b0000001)) ?
              MULH :
            ((cntxt.vif.insn[14:12] == 3'b101) && (cntxt.vif.insn[31:25] == 7'b0000001)) ?
              DIVU :
            UNKNOWN :
          (cntxt.vif.insn[6:0] == 7'b11_100_11) ? // SYSTEM
            (cntxt.vif.insn[14:12] == 3'b001) ?
              CSRRW :
            UNKNOWN :
          (cntxt.vif.insn[6:0] == 7'b00_011_11) ? // MISC-MEM
            (cntxt.vif.insn[14:12] == 3'b001) ?
              FENCE_I :
            UNKNOWN :
          (cntxt.vif.insn[6:0] == 7'b00_000_11) ? // LOAD
            (cntxt.vif.insn[14:12] == 3'b010) ?
              LW :
            UNKNOWN :
          UNKNOWN;  // TODO use disassembler
        mon_trn.instr.name =
          cntxt.vif.is_compressed ?
            (mon_trn.instr.name == JAL) ?
              (cntxt.vif.insn[11:7] == 5'b00000) ?
                C_J :
              (cntxt.vif.insn[11:7] == 5'b00001) ?
                C_JAL :
              UNKNOWN :
            (mon_trn.instr.name == LW) ?
              C_LW :
            UNKNOWN :
          mon_trn.instr.name;  // TODO get proper binary input
        mon_trn.instr.rs1 = dasm_rs1(cntxt.vif.insn);
        mon_trn.instr.rs2 = dasm_rs2(cntxt.vif.insn);
        mon_trn.instr.rd = dasm_rd(cntxt.vif.insn);
        mon_trn.instr.immi = dasm_i_imm(cntxt.vif.insn);
        mon_trn.instr.immu = dasm_u_imm(cntxt.vif.insn);
        mon_trn.instr.c_immj = dasm_rvc_j_imm(cntxt.vif.insn);
        mon_trn.instr.c_rs1p = cntxt.vif.insn[9:7];  // TODO use disassembler
        mon_trn.instr.c_rdp = cntxt.vif.insn[4:2];  // TODO use disassembler

        ap.write(mon_trn);
      end
    end
  join_none
`endif
// TODO refactor out the big lifting to separate task/function

endtask : run_phase
