// Copyright 2020 OpenHW Group
// Copyright 2020 Datum Technology Corporation
// Copyright 2020 Silicon Labs, Inc.
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


`ifndef __UVMA_RVFI_INSTR_IF_SV__
`define __UVMA_RVFI_INSTR_IF_SV__

/**
 * Encapsulates all signals and clocking of RVFI Instruction interface. Used by
 * monitor,
 */
interface uvma_rvfi_instr_if
  import uvma_rvfi_pkg::*;
  #(int ILEN=DEFAULT_ILEN,
    int XLEN=DEFAULT_XLEN)
  //import uvma_rvfi_pkg::*;
  (
    input                      clk,
    input                      reset_n,

    input                      rvfi_valid,
    input [ORDER_WL-1:0]       rvfi_order,
    input [ILEN-1:0]           rvfi_insn,
    input [TRAP_WL-1:0]        rvfi_trap,
    input                      rvfi_halt,
    input [RVFI_DBG_WL-1:0]    rvfi_dbg,
    input                      rvfi_dbg_mode,
    input [RVFI_NMIP_WL-1:0]   rvfi_nmip,
    input                      rvfi_intr,
    input [MODE_WL-1:0]        rvfi_mode,
    input [IXL_WL-1:0]         rvfi_ixl,
    input [XLEN-1:0]           rvfi_pc_rdata,
    input [XLEN-1:0]           rvfi_pc_wdata,

    input [GPR_ADDR_WL-1:0]    rvfi_rs1_addr,
    input [XLEN-1:0]           rvfi_rs1_rdata,

    input [GPR_ADDR_WL-1:0]    rvfi_rs2_addr,
    input [XLEN-1:0]           rvfi_rs2_rdata,

    input [GPR_ADDR_WL-1:0]    rvfi_rs3_addr,
    input [XLEN-1:0]           rvfi_rs3_rdata,

    input [GPR_ADDR_WL-1:0]    rvfi_rd1_addr,
    input [XLEN-1:0]           rvfi_rd1_wdata,

    input [GPR_ADDR_WL-1:0]    rvfi_rd2_addr,
    input [XLEN-1:0]           rvfi_rd2_wdata,

    input [XLEN-1:0]           rvfi_mem_addr,
    input [XLEN-1:0]           rvfi_mem_rdata,
    input [XLEN/8-1:0]         rvfi_mem_rmask,
    input [XLEN-1:0]           rvfi_mem_wdata,
    input [XLEN/8-1:0]         rvfi_mem_wmask

  );

  // -------------------------------------------------------------------
  // Local variables
  // -------------------------------------------------------------------
  bit [CYCLE_CNT_WL-1:0] cycle_cnt = 0;

  // -------------------------------------------------------------------
  // Begin module code
  // -------------------------------------------------------------------

  always @(posedge clk) begin
    cycle_cnt <= cycle_cnt + 1;
  end

  /**
      * Used by target DUT.
  */
  clocking dut_cb @(posedge clk or reset_n);
  endclocking : dut_cb

  /**
      * Used by uvma_rvfi_instr_mon_c.
  */
  clocking mon_cb @(posedge clk or reset_n);
      input #1step
        cycle_cnt,
        rvfi_valid,
        rvfi_order,
        rvfi_insn,
        rvfi_trap,
        rvfi_halt,
        rvfi_dbg,
        rvfi_dbg_mode,
        rvfi_nmip,
        rvfi_intr,
        rvfi_mode,
        rvfi_ixl,
        rvfi_pc_rdata,
        rvfi_pc_wdata,
        rvfi_rs1_addr,
        rvfi_rs1_rdata,
        rvfi_rs2_addr,
        rvfi_rs2_rdata,
        rvfi_rs3_addr,
        rvfi_rs3_rdata,
        rvfi_rd1_addr,
        rvfi_rd1_wdata,
        rvfi_rd2_addr,
        rvfi_rd2_wdata,
        rvfi_mem_addr,
        rvfi_mem_rdata,
        rvfi_mem_rmask,
        rvfi_mem_wdata,
        rvfi_mem_wmask;
  endclocking : mon_cb

  modport passive_mp    (clocking mon_cb);

endinterface : uvma_rvfi_instr_if


`endif // __UVMA_RVFI_INSTR_IF_SV__

