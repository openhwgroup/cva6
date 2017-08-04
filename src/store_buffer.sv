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

module store_buffer (
    input logic          clk_i,           // Clock
    input logic          rst_ni,          // Asynchronous reset active low
    input logic          flush_i,         // if we flush we need to pause the transactions on the memory
                                          // otherwise we will run in a deadlock with the memory arbiter
    output logic         no_st_pending_o, // non-speculative queue is empty (e.g.: everything is committed to the memory hierarchy)

    input  logic [11:0]  page_offset_i,
    output logic         page_offset_matches_o,

    input  logic         commit_i,        // commit the instruction which was placed there most recently
    output logic         commit_ready_o,  // commit queue is ready to accept another commit request
    output logic         ready_o,         // the store queue is ready to accept a new request
                                          // it is only ready if it can unconditionally commit the instruction, e.g.:
                                          // the commit buffer needs to be empty
    input  logic         valid_i,         // this is a valid store
    input  logic [63:0]  paddr_i,         // physical address of store which needs to be placed in the queue
    input  logic [63:0]  data_i,          // data which is placed in the queue
    input  logic [7:0]   be_i,            // byte enable in

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
    // depth of store-buffers
    localparam int unsigned DEPTH_SPEC   = 4;
    // allocate more space for the commit buffer to be on the save side
    localparam int unsigned DEPTH_COMMIT = 4;

    // we need to keep the tag portion of the address for a cycle later
    logic [43:0] address_tag_n, address_tag_q;
    logic        tag_valid_n, tag_valid_q;

    // the store queue has two parts:
    // 1. Speculative queue
    // 2. Commit queue which is non-speculative, e.g.: the store will definitely happen.

    struct packed {
        logic [63:0] address;
        logic [63:0] data;
        logic [7:0]  be;
        logic        valid;     // this entry is valid, we need this for checking if the address offset matches
    } speculative_queue_n [DEPTH_SPEC-1:0], speculative_queue_q [DEPTH_SPEC-1:0],
      commit_queue_n [DEPTH_COMMIT-1:0],    commit_queue_q [DEPTH_COMMIT-1:0];

    // keep a status count for both buffers
    logic [$clog2(DEPTH_SPEC):0] speculative_status_cnt_n, speculative_status_cnt_q;
    logic [$clog2(DEPTH_COMMIT):0] commit_status_cnt_n, commit_status_cnt_q;
    // Speculative queue
    logic [$clog2(DEPTH_SPEC)-1:0] speculative_read_pointer_n,  speculative_read_pointer_q;
    logic [$clog2(DEPTH_SPEC)-1:0] speculative_write_pointer_n, speculative_write_pointer_q;
    // Commit Queue
    logic [$clog2(DEPTH_COMMIT)-1:0] commit_read_pointer_n,  commit_read_pointer_q;
    logic [$clog2(DEPTH_COMMIT)-1:0] commit_write_pointer_n, commit_write_pointer_q;

    // ----------------------------------------
    // Speculative Queue - Core Interface
    // ----------------------------------------
    always_comb begin : core_if
        automatic logic [DEPTH_SPEC:0] speculative_status_cnt = speculative_status_cnt_q;

        // we are ready if the speculative and the commit queue have a space left
        ready_o = speculative_status_cnt_q < (DEPTH_SPEC - 1);
        // default assignments
        speculative_status_cnt_n    = speculative_status_cnt_q;
        speculative_read_pointer_n  = speculative_read_pointer_q;
        speculative_write_pointer_n = speculative_write_pointer_q;
        speculative_queue_n         = speculative_queue_q;
        // LSU interface
        // we are ready to accept a new entry and the input data is valid
        if (valid_i) begin
            speculative_queue_n[speculative_write_pointer_q].address = paddr_i;
            speculative_queue_n[speculative_write_pointer_q].data    = data_i;
            speculative_queue_n[speculative_write_pointer_q].be      = be_i;
            speculative_queue_n[speculative_write_pointer_q].valid   = 1'b1;
            // advance the write pointer
            speculative_write_pointer_n = speculative_write_pointer_q + 1'b1;
            speculative_status_cnt++;
        end

        // evict the current entry out of this queue, the commit queue will thankfully take it and commit it
        // to the memory hierarchy
        if (commit_i) begin
            // invalidate
            speculative_queue_n[speculative_read_pointer_q].valid = 1'b0;
            // advance the read pointer
            speculative_read_pointer_n = speculative_read_pointer_q + 1'b1;
            speculative_status_cnt--;
        end

        speculative_status_cnt_n = speculative_status_cnt;

        // when we flush evict the speculative stores
        if (ready_o && flush_i) begin
            // reset all valid flags
            for (int unsigned i = 0; i < DEPTH_SPEC; i++)
                speculative_queue_n[i].valid = 1'b0;

            speculative_write_pointer_n = speculative_read_pointer_q;
        end
    end

    // ----------------------------------------
    // Commit Queue - Memory Interface
    // ----------------------------------------
    // those signals can directly be output to the memory
    assign address_index_o = commit_queue_q[commit_read_pointer_q].address[11:0];
    // if we got a new request we already saved the tag from the previous cycle
    assign address_tag_o   = address_tag_q;
    assign tag_valid_o     = tag_valid_q;
    assign data_wdata_o    = commit_queue_q[commit_read_pointer_q].data;
    assign data_be_o       = commit_queue_q[commit_read_pointer_q].be;
    // we will never kill a request in the store buffer since we already know that the translation is valid
    // e.g.: a kill request will only be necessary if we are not sure if the requested memory address will result in a TLB fault
    assign kill_req_o = 1'b0;
    assign data_we_o  = 1'b1; // we will always write in the store queue

    always_comb begin : store_if
        automatic logic [DEPTH_COMMIT:0] commit_status_cnt = commit_status_cnt_q;
        commit_ready_o = (commit_status_cnt_q < DEPTH_COMMIT);
        // no store is pending if we don't have any element in the commit queue e.g.: it is empty
        no_st_pending_o         = (commit_status_cnt_q == 0);
        // default assignments
        commit_read_pointer_n   = commit_read_pointer_q;
        commit_write_pointer_n  = commit_write_pointer_q;

        address_tag_n  = address_tag_q;
        commit_queue_n = commit_queue_q;

        tag_valid_n    = 1'b0;
        data_req_o     = 1'b0;

        // there should be no commit when we are flushing
        // if the entry in the commit queue is valid and not speculative anymore we can issue this instruction
        if (commit_queue_q[commit_read_pointer_q].valid) begin
            data_req_o = 1'b1;
            if (data_gnt_i) begin
                // we can evict it from the commit buffer
                commit_queue_n[commit_read_pointer_q].valid = 1'b0;
                // save the tag portion
                address_tag_n = commit_queue_q[commit_read_pointer_q].address[55:12];
                // signal a valid tag the cycle afterwards
                tag_valid_n  = 1'b1;
                // advance the read_pointer
                commit_read_pointer_n = commit_read_pointer_q + 1'b1;
                commit_status_cnt--;
            end
        end
        // we ignore the rvalid signal for now as we assume that the store
        // happened if we got a grant

        // shift the store request from the speculative buffer to the non-speculative
        if (commit_i) begin
            commit_queue_n[commit_write_pointer_q] = speculative_queue_q[speculative_read_pointer_q];
            commit_write_pointer_n = commit_write_pointer_n + 1'b1;
            commit_status_cnt++;
        end

        commit_status_cnt_n     = commit_status_cnt;
    end

    // ------------------
    // Address Checker
    // ------------------
    // The load should return the data stored by the most recent store to the
    // same physical address.  The most direct way to implement this is to
    // maintain physical addresses in the store buffer.

    // Of course, there are other micro-architectural techniques to accomplish
    // the same thing: you can interlock and wait for the store buffer to
    // drain if the load VA matches any store VA modulo the page size (i.e.
    // bits 11:0).  As a special case, it is correct to bypass if the full VA
    // matches, and no younger stores' VAs match in bits 11:0.
    //
    // checks if the requested load is in the store buffer
    // page offsets are virtually and physically the same
    always_comb begin : address_checker
        page_offset_matches_o = 1'b0;
        // check if the LSBs are identical and the entry is valid
        for (int unsigned i = 0; i < DEPTH_COMMIT; i++) begin
            // Check if the page offset matches and whether the entry is valid, for the commit queue
            if ((page_offset_i[11:3] == commit_queue_q[i].address[11:3]) && commit_queue_q[i].valid) begin
                page_offset_matches_o = 1'b1;
                break;
            end
        end
        for (int unsigned i = 0; i < DEPTH_SPEC; i++) begin
            // do the same for the speculative queue
            if ((page_offset_i[11:3] == speculative_queue_q[i].address[11:3]) && speculative_queue_q[i].valid) begin
                page_offset_matches_o = 1'b1;
                break;
            end
        end
        // or it matches with the entry we are currently putting into the queue
        if ((page_offset_i[11:3] == paddr_i[11:3]) && valid_i) begin
            page_offset_matches_o = 1'b1;
        end
    end


    // registers
    always_ff @(posedge clk_i or negedge rst_ni) begin : proc_
        if(~rst_ni) begin
            address_tag_q               <= 'b0;
            tag_valid_q                 <= 1'b0;
            // initialize the queues
            speculative_queue_q         <= '{default: 0};
            commit_queue_q              <= '{default: 0};
            commit_read_pointer_q       <= '0;
            commit_write_pointer_q      <= '0;
            commit_status_cnt_q         <= '0;
            speculative_read_pointer_q  <= '0;
            speculative_write_pointer_q <= '0;
            speculative_status_cnt_q    <= '0;
        end else begin
            address_tag_q               <= address_tag_n;
            tag_valid_q                 <= tag_valid_n;
            speculative_queue_q         <= speculative_queue_n;
            commit_queue_q              <= commit_queue_n;
            commit_read_pointer_q       <= commit_read_pointer_n;
            commit_write_pointer_q      <= commit_write_pointer_n;
            commit_status_cnt_q         <= commit_status_cnt_n;
            speculative_read_pointer_q  <= speculative_read_pointer_n;
            speculative_write_pointer_q <= speculative_write_pointer_n;
            speculative_status_cnt_q    <= speculative_status_cnt_n;
        end
     end

    `ifndef SYNTHESIS
    `ifndef verilator
    // assert that commit is never set when we are flushing this would be counter intuitive
    // as flush and commit is decided in the same stage
    assert property (
        @(posedge clk_i) rst_ni && flush_i |-> !commit_i)
        else $error ("You are trying to commit and flush in the same cycle");

    assert property (
        @(posedge clk_i) rst_ni && !ready_o |-> !valid_i)
        else $error ("You are trying to push new data although the buffer is not ready");
    `endif
    `endif
endmodule
