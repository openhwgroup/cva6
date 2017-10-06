// Author: Florian Zaruba, ETH Zurich
// Date: 06.10.2017
// Description: Performance counters
//
//
// Copyright (C) 2017 ETH Zurich, University of Bologna
// All rights reserved.
//
// This code is under development and not yet released to the public.
// Until it is released, the code is under the copyright of ETH Zurich and
// the University of Bologna, and may contain confidential and/or unpublished
// work. Any reuse/redistribution is strictly forbidden without written
// permission from ETH Zurich.
//
// Bug fixes and contributions will eventually be released under the
// SolderPad open hardware license in the context of the PULP platform
// (http://www.pulp-platform.org), under the copyright of ETH Zurich and the
// University of Bologna.
//
import ariane_pkg::*;

module perf_counters #(
    int unsigned NR_EXTERNAL_COUNTERS = 1
)(
    input  logic           clk_i,    // Clock
    input  logic           rst_ni,   // Asynchronous reset active low
    // SRAM like interface
    input  logic [11:0]    addr_i,   // read/write address
    input  logic           we_i,     // write enable
    input  logic [63:0]    data_i,   // data to write
    output logic [63:0]    data_o,   // data to read
    // from commit stage
    input  scoreboar_entry commit_instr_i,
    input  logic           commit_ack_o,

    // from L1 caches
    input  logic           l1_icache_miss_i,
    input  logic           l1_dcache_miss_i,
    // from MMU
    input  logic           itlb_miss_i,
    input  logic           dtlb_miss_i,
    // from PC Gen
    input  exception       ex_i,
    input  logic           eret_i,
    input  branchpredict   resolved_branch_i
);

    logic [4:0][63:0] perf_counter_n, perf_counter_q;

    always_comb begin : perf_counters
        perf_counter_n = perf_counter_q;

        // ------------------------------
        // Update Performance Counters
        // ------------------------------
        if (l1_icache_miss_i)
            perf_counter_n[L1_ICACHE_MISS] = perf_counter_q[L1_ICACHE_MISS] + 1'b1;

        if (l1_dcache_miss_i)
            perf_counter_n[L1_DCACHE_MISS] = perf_counter_q[L1_DCACHE_MISS] + 1'b1;

        if (itlb_miss_i)
            perf_counter_n[ITLB_MISS] = perf_counter_q[ITLB_MISS] + 1'b1;

        if (dtlb_miss_i)
            perf_counter_n[DTLB_MISS] = perf_counter_q[DTLB_MISS] + 1'b1;

        if (commit_ack_o) begin
            if (commit_instr_i.fu == LOAD)
                perf_counter_n[LOAD] = perf_counter_q[LOAD] + 1'b1;

            if (commit_instr_i.fu == STORE)
                perf_counter_n[STORE] = perf_counter_q[STORE] + 1'b1;

            // The standard software calling convention uses register x1 to hold the return address on a call
            if (commit_instr_i.op == JALR && commit_instr_i.rd == 'b1)
                perf_counter_n[CALL] = perf_counter_q[CALL] + 1'b1;

            // Return from call
            if (commit_instr_i.op == JALR && commit_instr_i.rs1 == 'b1)

            if (commit_instr_i.fu = CTRL_FLOW)
                perf_counter_n[RET] = perf_counter_q[RET] + 1'b1;

        end

        if (ex_i.valid)
            perf_counter_n[EXCEPTION] = perf_counter_q[EXCEPTION] + 1'b1;

        if (eret_i)
            perf_counter_n[EXCEPTION_RET] = perf_counter_q[EXCEPTION_RET] + 1'b1;

        if (resolved_branch_i.valid && resolved_branch_i.is_mispredict)
            perf_counter_n[MIS_PREDICT] = perf_counter_q[MIS_PREDICT] + 1'b1;

    end

    // ----------------
    // Registers
    // ----------------
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if(~rst_ni) begin
           perf_counter_q <= {default: '0};
        end else begin
           perf_counter_q <= perf_counter_n;
        end
    end

endmodule
