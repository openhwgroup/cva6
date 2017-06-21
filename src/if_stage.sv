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
    // instruction cache interface
    output logic                   instr_req_o,
    output logic [63:0]            instr_addr_o,
    input  logic                   instr_gnt_i,
    input  logic                   instr_rvalid_i,
    input  logic [31:0]            instr_rdata_i,
    input  exception               instr_ex_i,          // Instruction fetch exception, valid if rvalid is one
    // Output of IF Pipeline stage
    output fetch_entry             fetch_entry_o,       // fetch entry containing all relevant data for the ID stage
    output logic                   fetch_entry_valid_i, // instruction in IF is valid
    input  logic                   instr_ack_i          // ID acknowledged this instruction
);

    enum logic [1:0] {IDLE, WAIT_GNT, WAIT_RVALID, WAIT_ABORTED } CS, NS;

    logic [63:0]      fetch_address;
    logic             addr_valid;
    logic [63:0]      instr_addr_q;
    logic             fifo_valid;
    logic             fifo_ready;
    branchpredict_sbe branchpredict_q;

    //---------------------------------
    // Pre-fetch buffer status
    //---------------------------------
    // we are busy if we are either waiting for a grant
    // or if the FIFO is full
    assign if_busy_o = (CS == WAIT_GNT) || !fifo_ready;
    assign fetch_address = {fetch_address_i[63:2], 2'b0};

    //---------------------------------
    // Fetch FIFO
    // consumes addresses and rdata
    //---------------------------------
    fetch_fifo fetch_fifo_i (
        .branch_predict_i      ( branchpredict_q     ),
        .ex_i                  ( instr_ex_i          ),
        .in_addr_i             ( instr_addr_q        ),
        .in_rdata_i            ( instr_rdata_i       ),
        .in_valid_i            ( fifo_valid          ),
        .in_ready_o            ( fifo_ready          ),

        .out_valid_o           ( fetch_entry_valid_i ),
        .out_ready_i           ( instr_ack_i         ),
        .*
    );

    //--------------------------------------------------
    // Instruction fetch FSM
    // deals with instruction memory / instruction cache
    //--------------------------------------------------
    always_comb begin
        instr_req_o   = 1'b0;
        instr_addr_o  = fetch_address;
        fifo_valid    = 1'b0;
        NS            = CS;
        addr_valid    = 1'b0;

        case(CS)
            // default state, not waiting for requested data
            IDLE: begin
                instr_addr_o = fetch_address;
                instr_req_o  = 1'b0;

                // make a new request
                if (fifo_ready && fetch_valid_i) begin
                    instr_req_o = 1'b1;
                    addr_valid  = 1'b1;


                    if (instr_gnt_i) //~>  granted request
                        // we have one outstanding rvalid: wait for it
                        if (flush_i)
                            NS = WAIT_ABORTED;
                        else
                            NS = WAIT_RVALID;
                    else begin //~> got a request but no grant
                        // if we flush we want to stay in the IDLE state
                        if (!flush_i)
                            NS = WAIT_GNT;
                    end
                end
            end // case: IDLE

            // we sent a request but did not yet get a grant
            WAIT_GNT: begin
                instr_addr_o = {instr_addr_q[63:2], 2'b0};
                instr_req_o  = 1'b1;

                if(instr_gnt_i) begin
                    // we have one outstanding rvalid: wait for it
                    if (flush_i)
                        NS = WAIT_ABORTED;
                    else
                        NS = WAIT_RVALID;
                end else begin
                    // if we got a flush request we can safely return to IDLE
                    if (flush_i)
                        NS = IDLE;
                    else
                        NS = WAIT_GNT;
                end
            end // case: WAIT_GNT

              // we wait for rvalid, after that we are ready to serve a new request
            WAIT_RVALID: begin
                instr_addr_o = fetch_address;
                // prepare for next request
                if (fifo_ready && fetch_valid_i) begin
                    // wait for the valid signal
                    if (instr_rvalid_i) begin
                        instr_req_o = 1'b1;
                        fifo_valid  = 1'b1;
                        addr_valid  = 1'b1;

                        if (instr_gnt_i) begin
                        // we have one outstanding rvalid: wait for it
                            // if we are receiving a data item during a flush ignore it
                            if (flush_i)
                                NS = WAIT_ABORTED;
                            else
                                NS = WAIT_RVALID;
                        end else begin
                            if (!flush_i)
                                NS = WAIT_GNT; // lets wait for the grant
                            else // we didn't get a grant yet so go back to IDLE
                                NS = IDLE;
                        end
                    end
                end else begin
                    // we are requested to abort our current request
                    // we didn't get an rvalid yet, so wait for it
                    if (flush_i) begin
                        NS = WAIT_ABORTED;
                    end
                    // just wait for rvalid and go back to IDLE, no new request
                    if (instr_rvalid_i) begin
                      // if we are receiving a data item during a flush ignore it
                        if (flush_i)
                            fifo_valid = 1'b0;
                        else
                            fifo_valid = 1'b1;
                        // in any case we can go back to IDLE safely
                        NS = IDLE;
                    end
                end

            end // case: WAIT_RVALID

            // our last request was aborted, but we didn't yet get a rvalid
            WAIT_ABORTED: begin
                // we can do a new request here, we won't get a grant until the rvalid came back for the
                // request we sent to end in here
                instr_addr_o = fetch_address;
                addr_valid   = 1'b1;
                // we are aborting this instruction so don't tell the FIFO it is valid
                fifo_valid   = 1'b0;
                // check if the fetch is valid before making a new request
                if (fetch_valid_i) begin

                    instr_req_o  = 1'b1;

                    if (instr_gnt_i) begin
                        // we have one outstanding rvalid
                        if (flush_i)
                            NS = WAIT_ABORTED;
                        else
                            NS = WAIT_RVALID;
                    end else begin
                        // only if we are not flushing again leave the state
                        if (!flush_i)
                            NS = WAIT_GNT;
                    end
                end else begin
                    if (instr_rvalid_i) begin
                        // we didn't make a new request but got the rvalid we where waiting for, go back to IDLE
                        NS = IDLE;
                    end
                    // otherwise wait in this state for the rvalid
                end
            end
        endcase
    end

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
            if (addr_valid) begin
              instr_addr_q    <= fetch_address_i;
              branchpredict_q <= branch_predict_i;
            end
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