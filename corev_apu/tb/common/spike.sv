// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Author: Florian Zaruba, ETH Zurich
// Date: 3/11/2018
// Description: Wrapped Spike Model for Tandem Verification

import ariane_pkg::*;
import rvfi_pkg::*;

module spike #(
  parameter config_pkg::cva6_cfg_t CVA6Cfg = cva6_config_pkg::cva6_cfg,
  parameter type rvfi_instr_t = struct packed {
    logic [config_pkg::NRET-1:0]                  valid;
    logic [config_pkg::NRET*64-1:0]               order;
    logic [config_pkg::NRET*config_pkg::ILEN-1:0] insn;
    logic [config_pkg::NRET-1:0]                  trap;
    logic [config_pkg::NRET*riscv::XLEN-1:0]      cause;
    logic [config_pkg::NRET-1:0]                  halt;
    logic [config_pkg::NRET-1:0]                  intr;
    logic [config_pkg::NRET*2-1:0]                mode;
    logic [config_pkg::NRET*2-1:0]                ixl;
    logic [config_pkg::NRET*5-1:0]                rs1_addr;
    logic [config_pkg::NRET*5-1:0]                rs2_addr;
    logic [config_pkg::NRET*riscv::XLEN-1:0]      rs1_rdata;
    logic [config_pkg::NRET*riscv::XLEN-1:0]      rs2_rdata;
    logic [config_pkg::NRET*5-1:0]                rd_addr;
    logic [config_pkg::NRET*riscv::XLEN-1:0]      rd_wdata;
    logic [config_pkg::NRET*riscv::XLEN-1:0]      pc_rdata;
    logic [config_pkg::NRET*riscv::XLEN-1:0]      pc_wdata;
    logic [config_pkg::NRET*riscv::VLEN-1:0]      mem_addr;
    logic [config_pkg::NRET*riscv::PLEN-1:0]      mem_paddr;
    logic [config_pkg::NRET*(riscv::XLEN/8)-1:0]  mem_rmask;
    logic [config_pkg::NRET*(riscv::XLEN/8)-1:0]  mem_wmask;
    logic [config_pkg::NRET*riscv::XLEN-1:0]      mem_rdata;
    logic [config_pkg::NRET*riscv::XLEN-1:0]      mem_wdata;
  },
  parameter longint unsigned DramBase = 'h8000_0000,
  parameter int unsigned     Size     = 64 * 1024 * 1024 // 64 Mega Byte
)(
    input logic                                     clk_i,
    input logic                                     rst_ni,
    input logic                                     clint_tick_i,
    input rvfi_instr_t[CVA6Cfg.NrCommitPorts-1:0]   rvfi_i
);
    string binary = "";
    string rtl_isa = "";

    initial begin
        rvfi_initialize_spike('h1);
    end

    st_rvfi s_core, s_reference_model;
    logic [63:0] pc64;
    logic [31:0] rtl_instr;
    logic [31:0] spike_instr;
    string       cause;
    string instr;

    always_ff @(posedge clk_i) begin
        if (rst_ni) begin
            for (int i = 0; i < CVA6Cfg.NrCommitPorts; i++) begin

                if (rvfi_i[i].valid || rvfi_i[i].trap) begin
                    s_core.order = rvfi_i[i].order;
                    s_core.insn  = rvfi_i[i].insn;
                    s_core.trap  = rvfi_i[i].trap;
                    s_core.cause = rvfi_i[i].cause;
                    s_core.halt  = rvfi_i[i].halt;
                    s_core.intr  = rvfi_i[i].intr;
                    s_core.mode  = rvfi_i[i].mode;
                    s_core.ixl   = rvfi_i[i].ixl;
                    s_core.rs1_addr  = rvfi_i[i].rs1_addr;
                    s_core.rs2_addr  = rvfi_i[i].rs2_addr;
                    s_core.rs1_rdata = rvfi_i[i].rs1_rdata;
                    s_core.rs2_rdata = rvfi_i[i].rs2_rdata;
                    s_core.rd1_addr   = rvfi_i[i].rd_addr;
                    s_core.rd1_wdata  = rvfi_i[i].rd_wdata;
                    s_core.pc_rdata  = rvfi_i[i].pc_rdata;
                    s_core.pc_wdata  = rvfi_i[i].pc_wdata;
                    s_core.mem_addr  = rvfi_i[i].mem_addr;
                    s_core.mem_rmask = rvfi_i[i].mem_rmask;
                    s_core.mem_wmask = rvfi_i[i].mem_wmask;
                    s_core.mem_rdata = rvfi_i[i].mem_rdata;
                    s_core.mem_wdata = rvfi_i[i].mem_wdata;

                    rvfi_spike_step(s_core, s_reference_model);
                    rvfi_compare(s_core, s_reference_model);
                end
            end
        end
    end
endmodule
