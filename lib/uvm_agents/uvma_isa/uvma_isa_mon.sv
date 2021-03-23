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


class uvma_isa_mon_c extends uvm_monitor;

  `uvm_component_utils(uvma_isa_mon_c);

  uvma_isa_cntxt_c                        cntxt;
  uvm_analysis_port #(uvma_isa_mon_trn_c) ap;

  extern function new(string name = "uvma_isa_mon", uvm_component parent = null);
  extern virtual function void build_phase(uvm_phase phase);
  extern virtual task run_phase(uvm_phase phase);

endclass : uvma_isa_mon_c


function uvma_isa_mon_c::new(string name = "uvma_isa_mon", uvm_component parent = null);

  super.new(name, parent);

endfunction : new


function void uvma_isa_mon_c::build_phase(uvm_phase phase);

  super.build_phase(phase);

  void'(uvm_config_db#(uvma_isa_cntxt_c)::get(this, "", "cntxt", cntxt));
  if (!cntxt) begin
    `uvm_fatal("CNTXT", "Context handle is null")
  end

  ap = new("ap", this);

endfunction : build_phase


task uvma_isa_mon_c::run_phase(uvm_phase phase);

  super.run_phase(phase);

  // TODO if cfg.enabled, while 1, wait cntxt.vif.reset, ...
  fork
    begin
      forever begin
        uvma_isa_mon_trn_c mon_trn;

        @(cntxt.vif.retire);

        mon_trn = new();
        mon_trn.instr = new();
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
          UNKNOWN;  // TODO use disassembler
        mon_trn.instr.name =
          cntxt.vif.is_compressed ?
            (mon_trn.instr.name == JAL) ?
              (cntxt.vif.insn[11:7] == 5'b00000) ?
                C_J :
              (cntxt.vif.insn[11:7] == 5'b00001) ?
                C_JAL :
              mon_trn.instr.name :
            mon_trn.instr.name :
          mon_trn.instr.name;  // TODO get proper binary input
if (mon_trn.instr.name == C_JAL) $display("TODO got C_JAL");
        mon_trn.instr.rs1 = cntxt.vif.insn[19:15];  // TODO use disassembler
        mon_trn.instr.rs2 = cntxt.vif.insn[24:20];  // TODO use disassembler
        mon_trn.instr.rd = cntxt.vif.insn[11:7];  // TODO use disassembler
        mon_trn.instr.immi = cntxt.vif.insn[31:25];  // TODO use disassembler
        mon_trn.instr.immu = cntxt.vif.insn[31:12];  // TODO use disassembler
        mon_trn.instr.c_immj = cntxt.vif.insn[12:2];  // TODO use disassembler

        ap.write(mon_trn);
      end
    end
  join_none

endtask : run_phase
