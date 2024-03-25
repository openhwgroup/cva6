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

// Pre-processor macros
`ifdef VERILATOR
`include "custom_uvm_macros.svh"
`else
`include "uvm_macros.svh"
`endif

import ariane_pkg::*;
import riscv::*;
import uvma_rvfi_pkg::*;
import uvma_core_cntrl_pkg::*;
import uvmc_rvfi_reference_model_pkg::*;
import uvmc_rvfi_scoreboard_pkg::*;
import uvma_cva6pkg_utils_pkg::*;

module spike #(
  parameter config_pkg::cva6_cfg_t CVA6Cfg = cva6_config_pkg::cva6_cfg,
  parameter type rvfi_instr_t = logic,
  parameter type rvfi_csr_t = logic,
  parameter longint unsigned DramBase = 'h8000_0000,
  parameter int unsigned     Size     = 64 * 1024 * 1024 // 64 Mega Byte
)(
    input logic                                     clk_i,
    input logic                                     rst_ni,
    input logic                                     clint_tick_i,
    input rvfi_instr_t[CVA6Cfg.NrCommitPorts-1:0]   rvfi_i,
    input rvfi_csr_t                                rvfi_csr_i
);
    string binary = "";
    string rtl_isa = "";

    st_core_cntrl_cfg st;

    initial begin
        st = cva6pkg_to_core_cntrl_cfg(st);
        st.boot_addr_valid = 1'b1;
        st.boot_addr = 64'h0x10000;

        rvfi_initialize(st);
        rvfi_initialize_spike("cva6", st);

    end

    // There is a need of delayed rvfi as the 'csr'_q signal does not have the
    // written value
    st_rvfi s_core, s_reference_model;
    logic [63:0] pc64;
    logic [31:0] rtl_instr;
    logic [31:0] spike_instr;
    string       cause;
    string instr;

    always_ff @(posedge clk_i) begin
        if (rst_ni) begin

            for (int i = 0; i < CVA6Cfg.NrCommitPorts; i++) begin
                longint unsigned index = 0;

                if (rvfi_i[i].valid || rvfi_i[i].trap) begin
                    s_core.order = rvfi_i[i].order;
                    s_core.insn  = rvfi_i[i].insn;
                    s_core.trap  = rvfi_i[i].trap;
                    s_core.trap  |= (rvfi_i[i].cause << 1);
                    s_core.halt  = rvfi_i[i].halt;
                    s_core.intr  = rvfi_i[i].intr;
                    s_core.mode  = rvfi_i[i].mode;
                    s_core.ixl   = rvfi_i[i].ixl;
                    s_core.rs1_addr   = rvfi_i[i].rs1_addr;
                    s_core.rs2_addr   = rvfi_i[i].rs2_addr;
                    s_core.rs1_rdata  = rvfi_i[i].rs1_rdata;
                    s_core.rs2_rdata  = rvfi_i[i].rs2_rdata;
                    s_core.rd1_addr   = rvfi_i[i].rd_addr;
                    s_core.rd1_wdata  = rvfi_i[i].rd_wdata;
                    s_core.pc_rdata   = rvfi_i[i].pc_rdata;
                    s_core.pc_wdata   = rvfi_i[i].pc_wdata;
                    s_core.mem_addr   = rvfi_i[i].mem_addr;
                    s_core.mem_rmask  = rvfi_i[i].mem_rmask;
                    s_core.mem_wmask  = rvfi_i[i].mem_wmask;
                    s_core.mem_rdata  = rvfi_i[i].mem_rdata;
                    s_core.mem_wdata  = rvfi_i[i].mem_wdata;

                    `define GET_RVFI_CSR(CSR_ADDR, CSR_NAME, CSR_INDEX) \
                        s_core.csr_valid[CSR_INDEX] = 1; \
                        s_core.csr_addr [CSR_INDEX] = CSR_ADDR;\
                        s_core.csr_rdata[CSR_INDEX] = rvfi_csr_i.``CSR_NAME``.rdata;\
                        s_core.csr_rmask[CSR_INDEX] = rvfi_csr_i.``CSR_NAME``.rmask;\
                        s_core.csr_wdata[CSR_INDEX] = rvfi_csr_i.``CSR_NAME``.wdata;\
                        s_core.csr_wmask[CSR_INDEX] = rvfi_csr_i.``CSR_NAME``.wmask;

                    `GET_RVFI_CSR (CSR_MSTATUS  , mstatus     ,  0)
                    `GET_RVFI_CSR (CSR_MCAUSE   , mcause      ,  1)
                    `GET_RVFI_CSR (CSR_MEPC     , mepc        ,  2)
                    `GET_RVFI_CSR (CSR_MTVEC    , mtvec       ,  3)
                    `GET_RVFI_CSR (CSR_MISA     , misa        ,  4)
                    `GET_RVFI_CSR (CSR_MTVAL    , mtval       ,  5)
                    `GET_RVFI_CSR (CSR_MIDELEG  , mideleg     ,  6)
                    `GET_RVFI_CSR (CSR_MEDELEG  , medeleg     ,  7)
                    `GET_RVFI_CSR (CSR_SATP     , satp        ,  8)
                    `GET_RVFI_CSR (CSR_MIE      , mie         ,  9)
                    `GET_RVFI_CSR (CSR_STVEC    , stvec       , 10)
                    `GET_RVFI_CSR (CSR_SSCRATCH , sscratch    , 11)
                    `GET_RVFI_CSR (CSR_SEPC     , sepc        , 12)
                    `GET_RVFI_CSR (CSR_MSCRATCH , mscratch    , 13)
                    `GET_RVFI_CSR (CSR_STVAL    , stval       , 14)
                    `GET_RVFI_CSR (CSR_SCAUSE   , scause      , 15)
                    `GET_RVFI_CSR (CSR_PMPADDR0 , pmpaddr[0]  , 16)
                    `GET_RVFI_CSR (CSR_PMPCFG0  , pmpcfg0     , 17)

                    rvfi_spike_step(s_core, s_reference_model);
                    rvfi_compare(s_core, s_reference_model);
                end
            end
        end
    end
endmodule
