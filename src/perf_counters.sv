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
// Date: 06.10.2017
// Description: Performance counters

import ariane_pkg::*;

module perf_counters #(
  parameter int CounterWidth = 64
) (
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
  localparam logic [6:0] RegOffset = riscv::CSR_ML1_ICACHE_MISS >> 5;

  logic [riscv::CSR_MIF_EMPTY : riscv::CSR_ML1_ICACHE_MISS][63:0] perf_counter;
  logic [riscv::CSR_MIF_EMPTY : riscv::CSR_ML1_ICACHE_MISS]       perf_counter_we;
  logic [riscv::CSR_MIF_EMPTY : riscv::CSR_ML1_ICACHE_MISS]       perf_counter_inc;

  for (genvar i=riscv::CSR_ML1_ICACHE_MISS; i<=riscv::CSR_MIF_EMPTY; i++) begin : gen_perf_counter
    cva6_counter #(
      .CounterWidth ( CounterWidth )
    ) perf_counter_i (
      .clk_i         ( clk_i               ),
      .rst_ni        ( rst_ni              ),
      .counter_inc_i ( perf_counter_inc[i] ),
      .counter_we_i  ( perf_counter_we[i]  ),
      .counter_val_i ( data_i              ),
      .counter_val_o ( perf_counter[i]     )
    );
  end

  // counter increment
  always_comb begin
    perf_counter_inc = '0;
    perf_counter_we  = '0;
    data_o           = '0;

    // don't increment counters in debug mode
    if (!debug_mode_i) begin

      perf_counter_inc[riscv::CSR_ML1_ICACHE_MISS] = l1_icache_miss_i;
      perf_counter_inc[riscv::CSR_ML1_DCACHE_MISS] = l1_dcache_miss_i;
      perf_counter_inc[riscv::CSR_MITLB_MISS]      = itlb_miss_i;
      perf_counter_inc[riscv::CSR_MDTLB_MISS]      = dtlb_miss_i;

      // instruction related perf counters
      for (int unsigned i = 0; i < NR_COMMIT_PORTS-1; i++) begin
        if (commit_ack_i[i]) begin
          perf_counter_inc[riscv::CSR_MLOAD]        = (commit_instr_i[i].fu == LOAD);
          perf_counter_inc[riscv::CSR_MSTORE]       = (commit_instr_i[i].fu == STORE);
          perf_counter_inc[riscv::CSR_MBRANCH_JUMP] = (commit_instr_i[i].fu == CTRL_FLOW);

          // The standard software calling convention uses register x1 to hold the return address
          // on a call.
          // The unconditional jump is decoded as ADD op
          perf_counter_inc[riscv::CSR_MCALL] =
              (commit_instr_i[i].fu == CTRL_FLOW && commit_instr_i[i].op == '0

          // Return from call
          perf_counter_inc[riscv::CSR_MRET] =
              (commit_instr_i[i].op == JALR && commit_instr_i[i].rd == 'd1);
        end
      end
      perf_counter_inc[riscv::CSR_MEXCEPTION]     = ex_i.valid;
      perf_counter_inc[riscv::CSR_MEXCEPTION_RET] = eret_i;
      perf_counter_inc[riscv::CSR_MMIS_PREDICT]   =
          (resolved_branch_i.valid && resolved_branch_i.is_mispredict);
      perf_counter_inc[riscv::CSR_MSB_FULL]       = sb_full_i;
      perf_counter_inc[riscv::CSR_MIF_EMPTY]      = if_empty_i;
    end

    // read
    data_o = perf_counter[{RegOffset,addr_i}];

    // write
    perf_counter_we[{RegOffset, addr_i}] = 1'b1;
  end

endmodule
