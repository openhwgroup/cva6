// Author: Florian Zaruba, ETH Zurich
// Date: 14.05.2017
// Description: Instruction fetch stage
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

module if_stage (
    input  logic                   clk_i,               // Clock
    input  logic                   rst_ni,              // Asynchronous reset active low
    // control signals
    input  logic                   flush_i,
    output logic                   if_busy_o,           // is the IF stage busy fetching instructions?
    // fetch direction from PC Gen
    input  logic [63:0]            fetch_address_i,     // address to fetch from
    input  logic                   fetch_valid_i,       // the fetch address is valid
    input  branchpredict_sbe       branch_predict_i,    // branch prediction structure we get from the PC Gen stage and we
                                                        // we need to pass it on to all the further stages (until ex)
    // I$ Interface
    output logic                   instr_req_o,
    output logic [63:0]            instr_addr_o,
    input  logic                   instr_gnt_i,
    input  logic                   instr_rvalid_i,
    input  logic [63:0]            instr_rdata_i,
    input  exception               instr_ex_i,            // Instruction fetch exception, valid if rvalid is one
    // Output of IF Pipeline stage -> Dual Port Fetch FIFO
    // output port 0
    output fetch_entry             fetch_entry_0_o,       // fetch entry containing all relevant data for the ID stage
    output logic                   fetch_entry_valid_0_o, // instruction in IF is valid
    input  logic                   fetch_ack_0_i,         // ID acknowledged this instruction
    // output port 1
    output fetch_entry             fetch_entry_1_o,       // fetch entry containing all relevant data for the ID stage
    output logic                   fetch_entry_valid_1_o, // instruction in IF is valid
    input  logic                   fetch_ack_1_i          // ID acknowledged this instruction
);

    enum logic [2:0] {IDLE, WAIT_GNT, WAIT_RVALID, WAIT_ABORTED, WAIT_ABORTED_REQUEST } CS, NS;
    // define a type where we can store address and branch-prediction information
    typedef struct packed {
        logic [63:0]      address;
        branchpredict_sbe branchpredict;
    } address_fifo_t;

    logic [63:0]      instr_addr_n, instr_addr_q, fetch_address;
    branchpredict_sbe branchpredict_n, branchpredict_q;
    // Control signals
    address_fifo_t    push_data, pop_data;
    logic             fifo_valid, fifo_ready;
    logic             pop_empty; // pop the address queue in case of a flush, empty signal
    // Address queue status signals
    logic             empty, full, single_element;
    // we are busy if we are either waiting for a grant or if the FIFO is full
    assign if_busy_o = ((CS == WAIT_GNT) || !fifo_ready || (CS == WAIT_ABORTED_REQUEST) || full) && (CS != WAIT_ABORTED);
    assign fetch_address = {fetch_address_i[63:2], 2'b0};

    // --------------------------------------------------
    // Instruction Fetch FSM
    // Deals with Instruction Memory / Instruction Cache
    // --------------------------------------------------
    always_comb begin : instr_fetch_fsm

        NS            = CS;
        instr_req_o   = 1'b0;
        instr_addr_o  = fetch_address;
        push_data     = { fetch_address_i, branch_predict_i };
        fifo_valid    = instr_rvalid_i;
        pop_empty     = instr_rvalid_i; // only pop the address queue

        // get new data by default
        branchpredict_n = branch_predict_i;
        instr_addr_n    = fetch_address_i;

        case (CS)
            // we are idling, and can accept a new request
            IDLE: begin
                // check if we have space in the FIFOs and we want to do a request
                if (fifo_ready && fetch_valid_i && !full) begin
                    instr_req_o = 1'b1;
                    // did we get a grant?
                    if (instr_gnt_i)
                        // Yes, so wait for the rvalid
                        NS = WAIT_RVALID;
                    else
                        // No, so wait for it
                        NS = WAIT_GNT;
                end
            end

            // we sent a request but did not yet get a grant
            WAIT_GNT: begin
                instr_addr_o = {instr_addr_q[63:2], 2'b0};
                instr_req_o  = 1'b1;

                branchpredict_n = branchpredict_q;
                instr_addr_n    = instr_addr_q;

                if (instr_gnt_i) begin
                    // push the old data
                    push_data = { instr_addr_q, branchpredict_q };
                    // we have one outstanding rvalid: wait for it
                    if (flush_i)
                        NS = WAIT_ABORTED;
                    else
                        NS = WAIT_RVALID;
                end
            end

            WAIT_RVALID: begin
                instr_addr_o = fetch_address;

                // prepare for next request, we've got one if the fetch_valid_i is high
                // we can take it if both queues have still places left to store the request
                if (fifo_ready && fetch_valid_i && !full) begin

                    instr_req_o = 1'b1;

                    if (instr_gnt_i) begin
                        // we have one outstanding rvalid -> wait for it
                        NS = WAIT_RVALID;
                    end else begin
                        NS = WAIT_GNT; // lets wait for the grant
                    end
                end else begin
                    // go back to IDLE
                    NS = IDLE;
                end

            end
            // we save a potential new request here
            WAIT_ABORTED: begin
                // abort the current rvalid, we don't want it anymore
                fifo_valid = 1'b0;
                // we've got a new fetch here, the fetch FIFO is for sure empty as we just flushed it, but we still need to
                // wait for the address queue to be emptied
                if (fetch_valid_i && empty) begin
                    // re-do the request
                    if (instr_gnt_i)
                        NS = WAIT_RVALID;
                    else
                        NS = WAIT_GNT;
                end else if (fetch_valid_i) // the fetch is valid but the queue is not empty wait for it
                    NS = WAIT_ABORTED_REQUEST;
                else if (empty) // the fetch is not valid and the queue is empty we are back to normal operation
                    NS = IDLE;
            end

            // our last request was aborted, but we didn't yet get a rvalid
            WAIT_ABORTED_REQUEST: begin
                // abort the current rvalid, we don't want it anymore
                fifo_valid = 1'b0;
                // save request data
                branchpredict_n = branchpredict_q;
                instr_addr_n    = instr_addr_q;
                // here we wait for the queue to be empty, we do not make any new requests
                if (empty) // do the new request
                    NS = WAIT_GNT;
            end
        endcase
        // -------------
        // Flush
        // -------------
        if (flush_i) begin
            // if the address queue is empty this case is simple: just go back to idle
            // also if there is just a single element in the queue and we are commiting we can skip
            // waiting for all rvalids as the queue will be empty in the next cycle anyway
            if (empty && !(instr_req_o && instr_gnt_i))
                NS = IDLE;
            // if it wasn't empty we need to wait for all outstanding rvalids until we can make any further requests
            else
                NS = WAIT_ABORTED;
        end
    end

    // ---------------------------------
    // Address and Branch-predict Queue
    // ---------------------------------
    fifo #(
        .dtype            ( address_fifo_t          ),
        .DEPTH            ( 2                       )  // right now we support two outstanding transactions
    ) i_fifo (
        .flush_i          ( 1'b0                    ), // do not flush, we need to keep track of all outstanding rvalids
        .full_o           ( full                    ), // the address buffer is full
        .empty_o          ( empty                   ), // ...or empty
        .single_element_o ( single_element          ), // just a single element in the queue
        .data_i           ( push_data               ),
        .push_i           ( instr_gnt_i             ), // if we got a grant push the address and data
        .data_o           ( pop_data                ), // data we send to the fetch_fifo, along with the instr data which comes from memory
        .pop_i            ( fifo_valid || pop_empty ), // pop the data if we say that the fetch is valid
        .*
    );

    // ---------------------------------
    // Fetch FIFO
    // consumes addresses and rdata
    // ---------------------------------
    fetch_fifo i_fetch_fifo (
        .branch_predict_i   ( pop_data.branchpredict ),
        .ex_i               ( instr_ex_i             ),
        .addr_i             ( pop_data.address       ),
        .rdata_i            ( instr_rdata_i          ),
        .valid_i            ( fifo_valid             ),
        .ready_o            ( fifo_ready             ),
        .*
    );

    //-------------
    // Registers
    //-------------
    always_ff @(posedge clk_i, negedge rst_ni) begin
      if (~rst_ni) begin
            CS              <= IDLE;
            instr_addr_q    <= '0;
            branchpredict_q <= '{default: 0};
        end else begin
            CS              <= NS;
            instr_addr_q    <= instr_addr_n;
            branchpredict_q <= branchpredict_n;
        end
    end
    //-------------
    // Assertions
    //-------------
    `ifndef SYNTHESIS
    `ifndef VERILATOR
        // there should never be a grant when there was no request
        assert property (
          @(posedge clk_i) (instr_gnt_i) |-> (instr_req_o) )
        else $warning("There was a grant without a request");
    `endif
    `endif
endmodule
