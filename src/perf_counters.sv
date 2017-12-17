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
    input  logic                                    clk_i,    // Clock
    input  logic                                    rst_ni,   // Asynchronous reset active low
    // SRAM like interface
    input  logic [11:0]                             addr_i,   // read/write address
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
    // from PC Gen
    input  exception_t                              ex_i,
    input  logic                                    eret_i,
    input  branchpredict_t                          resolved_branch_i
);

    logic [11:0][63:0] perf_counter_d, perf_counter_q;

    always_comb begin : perf_counters
        perf_counter_d = perf_counter_q;
        data_o = 'b0;

        // ------------------------------
        // Update Performance Counters
        // ------------------------------
        if (l1_icache_miss_i)
            perf_counter_d[PERF_L1_ICACHE_MISS] = perf_counter_q[PERF_L1_ICACHE_MISS] + 1'b1;

        if (l1_dcache_miss_i)
            perf_counter_d[PERF_L1_DCACHE_MISS] = perf_counter_q[PERF_L1_DCACHE_MISS] + 1'b1;

        if (itlb_miss_i)
            perf_counter_d[PERF_ITLB_MISS] = perf_counter_q[PERF_ITLB_MISS] + 1'b1;

        if (dtlb_miss_i)
            perf_counter_d[PERF_DTLB_MISS] = perf_counter_q[PERF_DTLB_MISS] + 1'b1;

        // instruction related perf counters
        for (int unsigned i = 0; i < NR_COMMIT_PORTS-1; i++) begin
            if (commit_ack_i[i]) begin
                if (commit_instr_i[i].fu == LOAD)
                    perf_counter_d[PERF_LOAD] = perf_counter_q[PERF_LOAD] + 1'b1;

                if (commit_instr_i[i].fu == STORE)
                    perf_counter_d[PERF_STORE] = perf_counter_q[PERF_STORE] + 1'b1;

                if (commit_instr_i[i].fu == CTRL_FLOW)
                    perf_counter_d[PERF_BRANCH_JUMP] = perf_counter_q[PERF_BRANCH_JUMP] + 1'b1;

                // The standard software calling convention uses register x1 to hold the return address on a call
                // the unconditional jump is decoded as ADD op
                if (commit_instr_i[i].fu == CTRL_FLOW && commit_instr_i[i].op == '0 && commit_instr_i[i].rd == 'b1)
                    perf_counter_d[PERF_CALL] = perf_counter_q[PERF_CALL] + 1'b1;

                // Return from call
                if (commit_instr_i[i].op == JALR && commit_instr_i[i].rs1 == 'b1)
                    perf_counter_d[PERF_RET] = perf_counter_q[PERF_RET] + 1'b1;
            end
        end

        if (ex_i.valid)
            perf_counter_d[PERF_EXCEPTION] = perf_counter_q[PERF_EXCEPTION] + 1'b1;

        if (eret_i)
            perf_counter_d[PERF_EXCEPTION_RET] = perf_counter_q[PERF_EXCEPTION_RET] + 1'b1;

        if (resolved_branch_i.valid && resolved_branch_i.is_mispredict)
            perf_counter_d[PERF_MIS_PREDICT] = perf_counter_q[PERF_MIS_PREDICT] + 1'b1;

        // Read Port
        if (!we_i) begin
            data_o = perf_counter_q[addr_i[2:0]];
        // write port
        end else begin
            // on a write also output the current value
            data_o = perf_counter_q[addr_i[2:0]];
            perf_counter_d[addr_i[2:0]] = data_i;
        end
    end

    // ----------------
    // Registers
    // ----------------
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (~rst_ni) begin
           perf_counter_q <= '0;
        end else begin
           perf_counter_q <= perf_counter_d;
        end
    end

endmodule
