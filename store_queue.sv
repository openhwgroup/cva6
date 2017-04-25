// Author: Florian Zaruba, ETH Zurich
// Date: 25.04.2017
// Description: Store queue persists store requests and pushes them to memory
//              if they are no longer speculative
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

module store_queue (
    input logic          clk_i,    // Clock
    input logic          rst_ni,   // Asynchronous reset active low
    input logic          flush_i,  // if we flush we need to pause the transactions on the memory
                                   // otherwise we will run in a deadlock with the memory arbiter

    output logic [63:0]  paddr_o,   // physical address of the valid store
    output logic [63:0]  data_o,    // data at the given address
    output logic         valid_o,   // committed data is valid
    output logic [7:0]   be_o,      // byte enable set

    input  logic         commit_i, // commit the instruction which was placed there most recently

    output logic         ready_o,  // the store queue is ready to accept a new request
                                   // it is only ready if it can unconditionally commit the instruction, e.g.:
                                   // the commit buffer needs to be empty
                                   // it is easier to have an unconditional commit
    input  logic         valid_i,  // this is a valid store
    input  logic [63:0]  paddr_i,  // physical address of store which needs to be placed in the queue
    input  logic [63:0]  data_i,   // data which is placed in the queue
    input  logic [7:0]   be_i,     // byte enable in

    // D$ interface
    output logic [63:0]  address_o,
    output logic [63:0]  data_wdata_o,
    output logic         data_req_o,
    output logic         data_we_o,
    output logic [7:0]   data_be_o,
    input  logic         data_gnt_i,
    input  logic         data_rvalid_i,
    input  logic [63:0]  data_rdata_i
);
    // the store queue has two parts:
    // 1. Speculative queue
    // 2. Commit queue which is non-speculative, e.g.: the store will definitely happen.
    // For simplicity reasons we just keep those two elements and not one real queue
    // should it turn out that this bottlenecks we can still increase the capacity here
    // potentially at the cost of increased area.

    enum { IDLE, WAIT_RVALID } CS, NS;

    struct packed {
        logic [63:0] address;
        logic [63:0] data;
        logic [7:0]  be;
        logic        valid; // entry is valid
    } commit_queue_n, commit_queue_q, store_queue_n, store_queue_q;

    // we can directly output the commit entry since we just have one element in this "queue"
    assign paddr_o = commit_queue_q.address;
    assign data_o  = commit_queue_q.data;
    assign be_o    = commit_queue_q.be;
    assign valid_o = commit_queue_q.valid;

    // memory interface
    always_comb begin : store_if
        // those signals can directly be output to the memory if
        address_o    = commit_queue_q.address;
        data_wdata_o = commit_queue_q.data;
        data_be_o    = commit_queue_q.be;
        data_we_o    = 1'b1; // we will always write in the store queue
        data_req_o   = 1'b0;
        NS           = CS;

        if (~flush_i) begin
            case (CS)
                // we can accept a new request if we were idle
                IDLE: begin
                    if (commit_queue_q.valid) begin
                        data_req_o = 1'b1;
                        if (data_gnt_i) begin// advance to the next state if we received the grant
                            NS = WAIT_RVALID;
                            // we can evict it from the commit buffer
                            commit_queue_n.valid = 1'b0;
                        end
                    end
                end

                WAIT_RVALID: begin

                    if (data_rvalid_i) begin
                        // if we got the rvalid we can already perform a new store
                        if (commit_queue_q.valid)
                            data_req_o = 1'b1;
                        else // if do not need to perform another
                            NS = IDLE;
                    end else // wait here for the rvalid
                        NS = WAIT_RVALID;
                end

                default:;
            endcase
        end

        // shift the store request from the speculative buffer
        // to the non-speculative
        if (commit_i) begin
            commit_queue_n = store_queue_q;
        end
    end

    // LSU interface
    always_comb begin : lsu_if
        // if there is no commit pending and the uncommitted queue is empty as well we can accept the request
        automatic logic ready = ~commit_queue_q.valid & ~store_queue_q.valid;
        ready_o       =  ready;
        store_queue_n = store_queue_q;
        // we are ready to accept a new entry and the input data is valid
        if (ready & valid_i & ~commit_i) begin
            store_queue_n.address = paddr_i;
            store_queue_n.data    = data_i;
            store_queue_n.be      = be_i;
            store_queue_n.valid   = 1'b1;
        end
        // invalidate this result
        // as it is moved to the non-speculative queue
        if (~valid_i & commit_i) begin
            store_queue_n.valid   = 1'b0;
        end
    end

    // registers
    always_ff @(posedge clk_i or negedge rst_ni) begin : proc_
        if(~rst_ni) begin
           commit_queue_q <= '{default: 0};
           store_queue_q  <= '{default: 0};
           CS             <= IDLE;
        end else if (flush_i) begin // just empty the speculative queue
            commit_queue_q <= commit_queue_n;
            store_queue_q  <= '{default: 0};
            CS             <= NS;
        end else begin
            commit_queue_q <= commit_queue_n;
            store_queue_q  <= store_queue_n;
            CS             <= NS;
        end
     end
endmodule