// Copyright 2018-2019 ETH Zurich and University of Bologna.
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
// Date: 06.10.2017
// Description: Performance counters

import ariane_pkg::*;

module perf_counters (
  input  logic                                    clk_i,
  input  logic                                    rst_ni,
  input  logic                                    debug_mode_i, // debug mode
  // SRAM like interface
  input  logic [4:0]                              addr_i,   // read/write address (up to 29 aux counters possible in riscv encoding.h)
  input  logic                                    we_i,     // write enable
  input  logic [63:0]                             data_i,   // data to write
  output logic [63:0]                             data_o,   // data to read
  // from commit stage
  input  scoreboard_entry_t [NR_COMMIT_PORTS-1:0] commit_instr_i,     // the instruction we want to commit
  input  logic [NR_COMMIT_PORTS-1:0]              commit_ack_i,       // acknowledge that we are indeed committing

  // from L1 caches
  input  logic                                    l1_icache_miss_i,
  input  logic                                    l1_dcache_miss_i,
  // from MMU
  input  logic                                    itlb_miss_i,
  input  logic                                    dtlb_miss_i,
  // from issue stage
  input  logic                                    sb_full_i,
  // from frontend
  input  logic                                    if_empty_i,
  // from PC Gen
  input  exception_t                              ex_i,
  input  logic                                    eret_i,
  input  bp_resolve_t                             resolved_branch_i
);
  localparam logic [6:0] RegOffset = riscv::CSR_MCYCLE >> 5;

  logic [riscv::CSR_MIF_EMPTY : riscv::CSR_MCYCLE][63:0] perf_counter_d, perf_counter_q;

  always_comb begin : perf_counters
    perf_counter_d = perf_counter_q;
    data_o = 'b0;

    // don't increment counters in debug mode
    if (!debug_mode_i) begin
      perf_counter_d[riscv::CSR_MCYCLE] = perf_counter_q[riscv::CSR_MCYCLE] + 1'b1;
      // ------------------------------
      // Update Performance Counters
      // ------------------------------
      // increase instruction retired counter
      if (l1_icache_miss_i) perf_counter_d[riscv::CSR_ML1_ICACHE_MISS]++;
      if (l1_dcache_miss_i)  perf_counter_d[riscv::CSR_ML1_DCACHE_MISS]++;
      if (itlb_miss_i) perf_counter_d[riscv::CSR_MITLB_MISS]++;
      if (dtlb_miss_i) perf_counter_d[riscv::CSR_MDTLB_MISS]++;
      // instruction related perf counters
      for (int unsigned i = 0; i < NR_COMMIT_PORTS; i++) begin
        if (commit_ack_i[i]) begin
          perf_counter_d[riscv::CSR_MINSTRET]++;
          if (commit_instr_i[i].fu == LOAD) perf_counter_d[riscv::CSR_MLOAD]++;
          if (commit_instr_i[i].fu == STORE) perf_counter_d[riscv::CSR_MSTORE]++;
          if (commit_instr_i[i].fu == CTRL_FLOW) perf_counter_d[riscv::CSR_MBRANCH_JUMP]++;
          // The standard software calling convention uses register x1 to hold the return
          // address on a call the unconditional jump is decoded as ADD op
          if (commit_instr_i[i].fu == CTRL_FLOW && commit_instr_i[i].op == '0
                && (commit_instr_i[i].rd == 'd1 || commit_instr_i[i].rd == 'd1)) begin
            perf_counter_d[riscv::CSR_MCALL]++;
          end
          // Return from call
          if (commit_instr_i[i].op == JALR
                && (commit_instr_i[i].rd == 'd1 || commit_instr_i[i].rd == 'd1)) begin
            perf_counter_d[riscv::CSR_MRET]++;
          end
        end
      end

      if (ex_i.valid) perf_counter_d[riscv::CSR_MEXCEPTION]++;
      if (eret_i) perf_counter_d[riscv::CSR_MEXCEPTION_RET]++;
      if (resolved_branch_i.valid && resolved_branch_i.is_mispredict) begin
        perf_counter_d[riscv::CSR_MMIS_PREDICT]++;
      end
      if (sb_full_i) perf_counter_d[riscv::CSR_MSB_FULL]++;
      if (if_empty_i) perf_counter_d[riscv::CSR_MIF_EMPTY]++;
    end
    // write after read
    data_o = perf_counter_q[{RegOffset, addr_i}];
    if (we_i) begin
      perf_counter_d[{RegOffset,addr_i}] = data_i;
    end
  end
  // ----------------
  // Registers
  // ----------------
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      perf_counter_q <= '0;
    end else begin
      perf_counter_q <= perf_counter_d;
    end
  end
endmodule
