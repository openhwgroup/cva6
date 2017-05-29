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
    input  logic         valid_i,  // this is a valid store
    input  logic [63:0]  paddr_i,  // physical address of store which needs to be placed in the queue
    input  logic [63:0]  data_i,   // data which is placed in the queue
    input  logic [7:0]   be_i,     // byte enable in
    // D$ interface
    output logic [11:0]  address_index_o,
    output logic [43:0]  address_tag_o,
    output logic [63:0]  data_wdata_o,
    output logic         data_req_o,
    output logic         data_we_o,
    output logic [7:0]   data_be_o,
    output logic         kill_req_o,
    output logic         tag_valid_o,
    input  logic         data_gnt_i,
    input  logic         data_rvalid_i
    );
    // we need to keep the tag portion of the address for a cycle later
    logic [43:0] address_tag_n, address_tag_q;
    logic        tag_valid_n, tag_valid_q;

    // the store queue has two parts:
    // 1. Speculative queue
    // 2. Commit queue which is non-speculative, e.g.: the store will definitely happen.
    // For simplicity reasons we just keep those two elements and not one real queue
    // should it turn out that this bottlenecks we can still increase the capacity here
    // at the cost of increased area and worse timing since we need to check all addresses which are committed for
    // potential aliasing.
    //
    // In the current implementation this is represented by a single entry and
    // differentiated by the is_speculative flag.

    struct packed {
        logic [63:0] address;
        logic [63:0] data;
        logic [7:0]  be;
        logic        valid;          // entry is valid
        logic        is_speculative; // set if the entry isn't committed yet
    } commit_queue_n, commit_queue_q;

    // we can directly output the commit entry since we just have one element in this "queue"
    assign paddr_o           = commit_queue_q.address;
    assign data_o            = commit_queue_q.data;
    assign be_o              = commit_queue_q.be;
    assign valid_o           = commit_queue_q.valid;

    // those signals can directly be output to the memory
    assign address_index_o   = commit_queue_q.address[11:0];
    // if we got a new request we already saved the tag from the previous cycle
    assign address_tag_o     = address_tag_q;
    assign data_wdata_o      = commit_queue_q.data;
    assign data_be_o         = commit_queue_q.be;
    assign tag_valid_o       = tag_valid_q;
    // we will never kill a request in the store buffer since we already know that the translation is valid
    // e.g.: a kill request will only be necessary if we are not sure if the requested memory address will result in a TLB fault
    assign kill_req_o        = 1'b0;

    // memory interface
    always_comb begin : store_if
        // if there is no commit pending and the uncommitted queue is empty as well we can accept the request
        // if we got a grant this implies that the value was not speculative anymore and that we
        // do not need to save the values anymore since the memory already processed them
        automatic logic ready = ~commit_queue_q.valid | data_gnt_i;
        ready_o               =  ready & ~flush_i;

        address_tag_n  = address_tag_q;
        commit_queue_n = commit_queue_q;
        tag_valid_n    = 1'b0;

        data_we_o    = 1'b1; // we will always write in the store queue
        data_req_o   = 1'b0;

        // there should be no commit when we are flushing
        if (~flush_i) begin
            // if the entry in the commit queue is valid and not speculative anymore
            // we can issue this instruction
            // we can issue it as soon as the commit_i goes high or any number of cycles later
            // by looking at the is_speculative flag
            if (commit_queue_q.valid && (~commit_queue_q.is_speculative || commit_i)) begin
                data_req_o = 1'b1;
                if (data_gnt_i) begin
                    // we can evict it from the commit buffer
                    commit_queue_n.valid = 1'b0;
                    // save the tag portion
                    address_tag_n        = commit_queue_q.address[55:12];
                    // signal a valid tag the cycle afterwards
                    tag_valid_n          = 1'b1;
                end
            end
            // we ignore the rvalid signal for now as we assume that the store
            // happened
        end

        // shift the store request from the speculative buffer
        // to the non-speculative
        if (commit_i) begin
            commit_queue_n.is_speculative = 1'b0;
        end

        // LSU interface
        // we are ready to accept a new entry and the input data is valid
        if (ready & valid_i) begin
            commit_queue_n.address        = paddr_i;
            commit_queue_n.data           = data_i;
            commit_queue_n.be             = be_i;
            commit_queue_n.valid          = 1'b1;
            commit_queue_n.is_speculative = 1'b1;
        end

        // when we flush evict the speculative store
        if (flush_i & commit_queue_q.is_speculative) begin
            commit_queue_n.valid          = 1'b0;
        end

    end

    // registers
    always_ff @(posedge clk_i or negedge rst_ni) begin : proc_
        if(~rst_ni) begin
            address_tag_q  <= 'b0;
            tag_valid_q    <= 1'b0;
            commit_queue_q <= '{default: 0};
        end else begin
            commit_queue_q <= commit_queue_n;
            tag_valid_q    <= tag_valid_n;
            address_tag_q  <= address_tag_n;
        end
     end
    `ifndef SYNTHESIS
    `ifndef verilator
    // assert that commit is never set when we are flushing this would be counter intuitive
    // as flush and commit is decided in the same stage
    assert property (
        @(posedge clk_i) rst_ni & flush_i |-> ~commit_i)
        else $error ("You are trying to commit and flush in the same cycle");
    `endif
    `endif
endmodule