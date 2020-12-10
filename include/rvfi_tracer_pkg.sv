//#############################################################################
//#
//# Copyright 2020 Thales DIS design services SAS
//#
//# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
//# you may not use this file except in compliance with the License.
//# You may obtain a copy of the License at
//#
//#     https://solderpad.org/licenses/
//#
//# Unless required by applicable law or agreed to in writing, software
//# distributed under the License is distributed on an "AS IS" BASIS,
//# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
//# See the License for the specific language governing permissions and
//# limitations under the License.
//#
//#############################################################################
//#
//# Original Author: Jean-Roch COULON (jean-roch.coulon@invia.fr)
//#
//#############################################################################

package rvfi_tracer_pkg;

  localparam NRET = 1;
  localparam ILEN = 32;

  typedef struct packed {
    logic [NRET-1:0]                 rvfi_valid;
    logic [NRET*63:0]                rvfi_order;
    logic [NRET*ILEN-1:0]            rvfi_insn;
    logic [NRET-1:0]                 rvfi_trap;
    logic [NRET-1:0]                 rvfi_halt;
    logic [NRET-1:0]                 rvfi_intr;
    logic [NRET*2-1:0]               rvfi_mode;
    logic [NRET*2-1:0]               rvfi_ixl;
    logic [NRET*5-1:0]               rvfi_rs1_addr;
    logic [NRET*5-1:0]               rvfi_rs2_addr;
    logic [NRET*riscv::XLEN-1:0]     rvfi_rs1_rdata;
    logic [NRET*riscv::XLEN-1:0]     rvfi_rs2_rdata;
    logic [NRET*5-1:0]               rvfi_rd_addr;
    logic [NRET*riscv::XLEN-1:0]     rvfi_rd_wdata;

    logic [NRET*riscv::XLEN-1:0]     rvfi_pc_rdata;
    logic [NRET*riscv::XLEN-1:0]     rvfi_pc_wdata;

    logic [NRET*riscv::XLEN-1:0]     rvfi_mem_addr;
    logic [NRET*(riscv::XLEN/8)-1:0] rvfi_mem_rmask;
    logic [NRET*(riscv::XLEN/8)-1:0] rvfi_mem_wmask;
    logic [NRET*riscv::XLEN-1:0]     rvfi_mem_rdata;
    logic [NRET*riscv::XLEN-1:0]     rvfi_mem_wdata;
  } rvfi_instr_t;

  typedef rvfi_instr_t [ariane_pkg::NR_COMMIT_PORTS-1:0] rvfi_port_t;

endpackage
