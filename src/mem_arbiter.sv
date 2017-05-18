// Author: Florian Zaruba, ETH Zurich
// Date: 24.4.2017
// Description: Arbitrates the memory ports
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

// ---------------
// D$ Tag Status
// ---------------
`define WAIT_TRANSLATION  2'b00
`define VALID_TRANSLATION 2'b01
`define ABORT_TRANSLATION 2'b10
`define NOT_IMPL          2'b11


module mem_arbiter #(
        parameter int NR_PORTS = 3
    )
    (
    input  logic                           clk_i,          // Clock
    input  logic                           rst_ni,         // Asynchronous reset active low
    input  logic                           flush_i,
    // slave port
    output logic [63:0]                    address_o,
    output logic [63:0]                    data_wdata_o,
    output logic                           data_req_o,
    output logic                           data_we_o,
    output logic [7:0]                     data_be_o,
    output logic [1:0]                     data_tag_status_o,
    input  logic                           data_gnt_i,
    input  logic                           data_rvalid_i,
    input  logic [63:0]                    data_rdata_i,
    // master ports
    input  logic [NR_PORTS-1:0][63:0]      address_i,
    input  logic [NR_PORTS-1:0][63:0]      data_wdata_i,
    input  logic [NR_PORTS-1:0]            data_req_i,
    input  logic [NR_PORTS-1:0]            data_we_i,
    input  logic [NR_PORTS-1:0][7:0]       data_be_i,
    input  logic [NR_PORTS-1:0][1:0]       data_tag_status_i,
    output logic [NR_PORTS-1:0]            data_gnt_o,
    output logic [NR_PORTS-1:0]            data_rvalid_o,
    output logic [NR_PORTS-1:0][63:0]      data_rdata_o
);
    localparam DATA_WIDTH = $clog2(NR_PORTS);
    // registers
    enum logic [1:0]       {IDLE, WAIT_GNT, WAIT_TAG, WAIT_FLUSH} CS, NS;
    // remember the request port in case of a multi-cycle transaction
    logic [DATA_WIDTH-1:0] request_port_n, request_port_q;
    // local ports
    // FIFO control ports
    logic                  full;
    logic                  empty;
    logic                  single_element;
    // FIFO input port
    logic [DATA_WIDTH-1:0] in_data;
    logic                  push;
    // FIFO output port
    logic [DATA_WIDTH-1:0] out_data;
    logic                  pop;
    logic                  flush_ready;
    // essentially wait for the queue to be empty
    // or we just got a grant -> this means we issued a memory request in this cycle
    // although we are ready if we only got a single element in the queue and an rvalid
    // which means we are getting this element back in this cycle
    assign flush_ready = (empty & ~(|data_gnt_i)) | (single_element & data_rvalid_i);

    fifo #(
        .dtype            ( logic [DATA_WIDTH-1:0] ),
        .DEPTH            ( 4                      )
    ) fifo_i (
        .clk_i            ( clk_i                  ),
        .rst_ni           ( rst_ni                 ),
        .single_element_o ( single_element         ),
        // the flush is accomplished implicitly by waiting for the queue to be drained before accepting any new request
        .flush_i          ( 1'b0                   ),
        .full_o           ( full                   ),
        .empty_o          ( empty                  ),
        .data_i           ( in_data                ),
        .push_i           ( push                   ),
        .data_o           ( out_data               ),
        .pop_i            ( pop                    )
    );

    // addressing read and full write
    always_comb begin : read_req_write
        automatic logic [DATA_WIDTH-1:0] request_index = 0;
        data_req_o                = 1'b0;

        in_data                   = '{default: 0};
        push                      = 1'b0;
        request_port_n            = request_port_q;
        NS                        = CS;

        for (int i = 0; i < NR_PORTS; i++)
            data_gnt_o[i] = 1'b0;
        case (CS)
            // ----------------------------
            // Single-cycle memory requests
            // ----------------------------
            IDLE: begin
                // only go for a new request if we can wait for the valid e.g.: we have enough space in the buffer
                if (~full) begin
                    for (int unsigned i = 0; i < NR_PORTS; i++) begin
                        if (data_req_i[i] == 1'b1) begin
                            data_req_o        = data_req_i[i];
                            // save the request port for future states
                            request_port_n    = i;
                            request_index     = i;
                            // default is that we are waiting for the grant
                            NS = WAIT_GNT;
                            // wait for the grant
                            if (data_gnt_i) begin
                                // set the slave on which we are waiting
                                in_data = i[DATA_WIDTH-1:0];
                                push = 1'b1;
                                // we got a grant so we need to wait for the tag
                                NS = WAIT_TAG;
                            end
                            // we already got a valid translation so we can proceed normally
                            // from the request side the thing is over
                            if (data_tag_status_i[i] == `VALID_TRANSLATION)
                                NS = IDLE;
                            break; // break here as this is a priority select
                        end
                    end
                end
            end
            // ----------------------------
            // Multi-cycle memory requests
            // ----------------------------
            // do we have an outstanding request e.g.: a request which is waiting for a grant or an tag_valid
            // here we need to wait for the tag
            WAIT_GNT: begin
                // we can check for it since we only stay in this state if didn't yet receive a grant
                if (data_gnt_i) begin
                    // default is that we are waiting for the tag to be there
                    // if we are waiting for the tag we can't accept any new instructions
                    NS = WAIT_TAG;
                    // two possibilities to not go into the tag wait state
                    // 1. The tag is valid now
                    // 2. The tag has been aborted
                    if (data_tag_status_i[request_port_q] == `ABORT_TRANSLATION || data_tag_status_i[request_port_q] == `VALID_TRANSLATION) begin
                        NS = IDLE;
                    end
                end
                // or if the request vanished we are going back to idle
                if (!data_req_i[request_port_q])
                    NS = IDLE;

            end
            // here we are waiting for a valid (or aborted) tag
            WAIT_TAG: begin
                // if we are waiting for the tag we can't issue a new request
                if (data_tag_status_i[request_port_q] == `ABORT_TRANSLATION || data_tag_status_i[request_port_q] == `VALID_TRANSLATION) begin
                    NS = IDLE;
                    // if we got a valid tag we can make a new request under the same assumption as in the IDLE state
                    if (~full) begin
                        for (int unsigned i = 0; i < NR_PORTS; i++) begin
                            if (data_req_i[i] == 1'b1) begin
                                data_req_o        = data_req_i[i];
                                // save the request port for future states
                                request_port_n    = i;
                                request_index     = i;
                                // default is that we are waiting for the grant
                                NS = WAIT_GNT;
                                // wait for the grant
                                if (data_gnt_i) begin
                                    // set the slave on which we are waiting
                                    in_data = i[DATA_WIDTH-1:0];
                                    push = 1'b1;
                                    // we got a grant so we need to wait for the tag
                                    NS = WAIT_TAG;
                                end
                                // we already got a valid translation so we can proceed normally
                                // from the request side the thing is over
                                if (data_tag_status_i[i] == `VALID_TRANSLATION)
                                    NS = IDLE;
                                break; // break here as this is a priority select
                            end
                        end
                    end else begin
                        // the FIFO is full so go to IDLE and wait for it
                        NS  = IDLE;
                    end
                end
            end
            // ----------------------------
            // Flush logic
            // ----------------------------
            // here we are waiting for the FIFO to drain until we are ready to accept new requests
            WAIT_FLUSH: begin
                // if the flush has finished go to IDLE
                if (flush_ready)
                    NS = IDLE;
            end
            default : /* default */;
        endcase
        // pass through all signals from the correct slave port
        address_o                 = address_i[request_index];
        data_wdata_o              = data_wdata_i[request_index];
        data_be_o                 = data_be_i[request_index];
        data_we_o                 = data_we_i[request_index];
        data_tag_status_o         = data_tag_status_i[request_index];
        data_gnt_o[request_index] = data_gnt_i;

        // if we got a flush and we are not ready for the flush wait and for it and don't accept any incoming data
        // e.g.: jump to the flush wait state
        if (flush_i && !flush_ready)
                NS = WAIT_FLUSH;
    end

    // results, listening on the input signals of the slave port
    always_comb begin : slave_read_port
        pop = 1'b0;
        // default assignment
        for (int i = 0; i < NR_PORTS; i++) begin
            data_rvalid_o[i] = 1'b0;
            data_rdata_o[i]  = 64'b0;
        end
        // if there is an entry in the queue -> we are waiting for a read/write to return
        // if there is a valid signal the FIFO should not be empty anyway
        if (data_rvalid_i) begin
            // pass the read to the appropriate slave
            pop                 = 1'b1;
            data_rvalid_o[out_data] = data_rvalid_i;
            data_rdata_o[out_data]  = data_rdata_i;
        end
    end

    // sequential process
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if(~rst_ni) begin
            CS             <= IDLE;
            request_port_q <= 1'b0;
        end else begin
            CS             <= NS;
            request_port_q <= request_port_n;
        end
    end

    // ------------
    // Assertions
    // ------------

    `ifndef SYNTHESIS
    `ifndef VERILATOR
    // make sure that we eventually get an rvalid after we received a grant
    assert property (@(posedge clk_i) data_gnt_i |-> ##[1:$] data_rvalid_i )
        else begin $error("There was a grant without a rvalid"); $stop(); end
    // assert that there is no grant without a request
    assert property (@(negedge clk_i) data_gnt_i |-> data_req_o)
        else begin $error("There was a grant without a request."); $stop(); end
    // assert that the address does not contain X when request is sent
    assert property ( @(posedge clk_i) (data_req_o) |-> (!$isunknown(address_o)) )
      else begin $error("address contains X when request is set"); $stop(); end

    // there should be no rvalid when we are in IDLE
    // assert property (
    //   @(posedge clk) (CS == IDLE) |-> (data_rvalid_i == 1'b0) )
    //   else begin $error("Received rvalid while in IDLE state"); $stop(); end

    // assert that errors are only sent at the same time as grant or rvalid
    // assert property ( @(posedge clk) (data_err_i) |-> (data_gnt_i || data_rvalid_i) )
    //   else begin $error("Error without data grant or rvalid"); $stop(); end

    `endif
    `endif
endmodule
