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
`ifndef VERILATOR
import uvm_pkg::*;
`endif
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
    input rvfi_csr_t                                rvfi_csr_i,
    output logic[31:0]                              end_of_test_o
);
    string binary = "";
    string rtl_isa = "";

    st_core_cntrl_cfg st;
    bit sim_finished;

    initial begin
        string core_name = "cva6";
        st = cva6pkg_to_core_cntrl_cfg(st);
        st.boot_addr_valid = 1'b1;
        st.boot_addr = 64'h0x10000;

        if ($test$plusargs("core_name")) begin
          $value$plusargs("core_name=%s", core_name);
        end

        rvfi_initialize(st);
        rvfi_initialize_spike(core_name, st);

    end

    // There is a need of delayed rvfi as the 'csr'_q signal does not have the
    // written value
    logic [63:0] pc64;
    logic [31:0] rtl_instr;
    logic [31:0] spike_instr;
    string       cause;
    string instr;
    st_rvfi s_core [CVA6Cfg.NrCommitPorts-1:0];
    bit core_valid [CVA6Cfg.NrCommitPorts-1:0];

    `define GET_RVFI_CSR(CSR_ADDR, CSR_NAME) \
        s_core[i].csr_valid[CSR_ADDR] <= 1; \
        s_core[i].csr_addr [CSR_ADDR] <= CSR_ADDR;\
        s_core[i].csr_rdata[CSR_ADDR] <= rvfi_csr_i.``CSR_NAME``.rdata;\
        s_core[i].csr_rmask[CSR_ADDR] <= rvfi_csr_i.``CSR_NAME``.rmask;\
        s_core[i].csr_wdata[CSR_ADDR] <= rvfi_csr_i.``CSR_NAME``.wdata;\
        s_core[i].csr_wmask[CSR_ADDR] <= rvfi_csr_i.``CSR_NAME``.wmask;

    always_ff @(posedge clk_i) begin
        if (rst_ni) begin

            for (int i = 0; i < CVA6Cfg.NrCommitPorts; i++) begin

                if (rvfi_i[i].valid || rvfi_i[i].trap) begin
                    core_valid[i] <= 1;
                    s_core[i].order <= rvfi_i[i].order;
                    s_core[i].insn  <= rvfi_i[i].insn;
                    s_core[i].trap  <= rvfi_i[i].trap;
                    s_core[i].trap <= (rvfi_i[i].cause << 1) | rvfi_i[i].trap[0];
                    s_core[i].halt  <= rvfi_i[i].halt;
                    s_core[i].intr  <= rvfi_i[i].intr;
                    s_core[i].mode  <= rvfi_i[i].mode;
                    s_core[i].ixl   <= rvfi_i[i].ixl;
                    s_core[i].rs1_addr   <= rvfi_i[i].rs1_addr;
                    s_core[i].rs2_addr   <= rvfi_i[i].rs2_addr;
                    s_core[i].rs1_rdata  <= rvfi_i[i].rs1_rdata;
                    s_core[i].rs2_rdata  <= rvfi_i[i].rs2_rdata;
                    s_core[i].rd1_addr   <= rvfi_i[i].rd_addr;
                    s_core[i].rd1_wdata  <= rvfi_i[i].rd_wdata;
                    s_core[i].pc_rdata   <= rvfi_i[i].pc_rdata;
                    s_core[i].pc_wdata   <= rvfi_i[i].pc_wdata;
                    s_core[i].mem_addr   <= rvfi_i[i].mem_addr;
                    s_core[i].mem_rmask  <= rvfi_i[i].mem_rmask;
                    s_core[i].mem_wmask  <= rvfi_i[i].mem_wmask;
                    s_core[i].mem_rdata  <= rvfi_i[i].mem_rdata;
                    s_core[i].mem_wdata  <= rvfi_i[i].mem_wdata;


                    `GET_RVFI_CSR (CSR_MSTATUS      , mstatus     )
                    `GET_RVFI_CSR (CSR_MCAUSE       , mcause      )
                    `GET_RVFI_CSR (CSR_MEPC         , mepc        )
                    `GET_RVFI_CSR (CSR_MTVEC        , mtvec       )
                    `GET_RVFI_CSR (CSR_MISA         , misa        )
                    `GET_RVFI_CSR (CSR_MTVAL        , mtval       )
                    `GET_RVFI_CSR (CSR_MIDELEG      , mideleg     )
                    `GET_RVFI_CSR (CSR_MEDELEG      , medeleg     )
                    `GET_RVFI_CSR (CSR_SATP         , satp        )
                    `GET_RVFI_CSR (CSR_MIE          , mie         )
                    `GET_RVFI_CSR (CSR_STVEC        , stvec       )
                    `GET_RVFI_CSR (CSR_SSCRATCH     , sscratch    )
                    `GET_RVFI_CSR (CSR_SEPC         , sepc        )
                    `GET_RVFI_CSR (CSR_MSCRATCH     , mscratch    )
                    `GET_RVFI_CSR (CSR_STVAL        , stval       )
                    `GET_RVFI_CSR (CSR_SCAUSE       , scause      )
                    `GET_RVFI_CSR (CSR_PMPCFG0      , pmpcfg0     )
                    `GET_RVFI_CSR (CSR_PMPCFG1      , pmpcfg1     )
                    `GET_RVFI_CSR (CSR_PMPCFG2      , pmpcfg2     )
                    `GET_RVFI_CSR (CSR_PMPCFG3      , pmpcfg3     )
                    for (int j = 0; j < 16; j++) begin
                        `GET_RVFI_CSR (CSR_PMPADDR0 + j  , pmpaddr[j])
                    end
                    `GET_RVFI_CSR (CSR_MINSTRET     , instret     )
                    `GET_RVFI_CSR (CSR_MINSTRETH    , instreth    )
                    `GET_RVFI_CSR (CSR_MSTATUSH     , mstatush    )
                    `GET_RVFI_CSR (CSR_MIP          , mip         )
                    `GET_RVFI_CSR (CSR_MCYCLE       , mcycle      )
                end
                else begin
                    core_valid[i] <= 0;
                end

                if (core_valid[i] && !sim_finished) begin
                    st_rvfi core, reference_model;
                    core = s_core[i];

                    rvfi_spike_step(core, reference_model);
                    rvfi_compare(core, reference_model);

                    end_of_test_o = reference_model.halt;
                    sim_finished = reference_model.halt[0];
                end
            end
        end
    end
endmodule
