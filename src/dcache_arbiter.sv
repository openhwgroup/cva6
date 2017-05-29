// Author: Florian Zaruba, ETH Zurich
// Date: 24.4.2017
// Description: Arbitrates the dcache ports
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

module dcache_arbiter #(
        parameter int NR_PORTS = 3
    )
    (
    input  logic                           clk_i,          // Clock
    input  logic                           rst_ni,         // Asynchronous reset active low
    // slave port
    output logic [11:0]                    address_index_o,
    output logic [43:0]                    address_tag_o,
    output logic [63:0]                    data_wdata_o,
    output logic                           data_req_o,
    output logic                           data_we_o,
    output logic [7:0]                     data_be_o,
    output logic                           kill_req_o,
    output logic                           tag_valid_o,
    input  logic                           data_gnt_i,
    input  logic                           data_rvalid_i,
    input  logic [63:0]                    data_rdata_i,
    // master ports
    input  logic [NR_PORTS-1:0][11:0]      address_index_i,
    input  logic [NR_PORTS-1:0][43:0]      address_tag_i,
    input  logic [NR_PORTS-1:0][63:0]      data_wdata_i,
    input  logic [NR_PORTS-1:0]            data_req_i,
    input  logic [NR_PORTS-1:0]            data_we_i,
    input  logic [NR_PORTS-1:0][7:0]       data_be_i,
    input  logic [NR_PORTS-1:0]            kill_req_i,
    input  logic [NR_PORTS-1:0]            tag_valid_i,
    output logic [NR_PORTS-1:0]            data_gnt_o,
    output logic [NR_PORTS-1:0]            data_rvalid_o,
    output logic [NR_PORTS-1:0][63:0]      data_rdata_o
);
    // one-hot encoded
    localparam DATA_WIDTH = NR_PORTS;
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

    // FIFO to keep track of the responses
    fifo #(
        .dtype            ( logic [DATA_WIDTH-1:0] ),
        .DEPTH            ( 4                      )
    ) fifo_i (
        .clk_i            ( clk_i                  ),
        .rst_ni           ( rst_ni                 ),
        .single_element_o ( single_element         ),
        // the flush is accomplished implicitly by waiting for the queue to be drained before accepting any new request
        // it is the responsibility of the attached units to make sure it handles any outstanding responses
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
        automatic logic [DATA_WIDTH-1:0] request_index = request_port_q;
        data_req_o                = 1'b0;
        in_data                   = '{default: 0};
        push                      = 1'b0;
        request_port_n            = request_port_q;

        for (int i = 0; i < NR_PORTS; i++)
            data_gnt_o[i] = 1'b0;

        // ----------------------------
        // Single-cycle memory requests
        // ----------------------------
        // only go for a new request if we can wait for the valid e.g.: we have enough space in the buffer
        if (~full) begin
            for (int unsigned i = 0; i < NR_PORTS; i++) begin
                if (data_req_i[i] == 1'b1) begin
                    data_req_o        = data_req_i[i];
                    // save the request port for future states
                    request_port_n    = i;
                    request_index     = i;
                    // wait for the grant
                    if (data_gnt_i) begin
                        // set the slave on which we are waiting
                        in_data = 1'b1 << i[DATA_WIDTH-1:0];
                        push = 1'b1;
                    end

                    break; // break here as this is a priority select
                end
            end
        end

        // pass through all signals from the correct slave port
        address_index_o           = address_index_i[request_index];
        data_wdata_o              = data_wdata_i[request_index];
        data_be_o                 = data_be_i[request_index];
        data_we_o                 = data_we_i[request_index];
        data_gnt_o[request_index] = data_gnt_i;
        // the following signals are to be passed through one-cycle later
        address_tag_o             = address_tag_i[request_port_q];
        kill_req_o                = kill_req_i[request_port_q];
        tag_valid_o               = tag_valid_i[request_port_q];
    end

    // ------------
    // Read port
    // ------------
    // results, listening on the input signals of the slave port
    genvar i;
    // this is very timing sensitive since we can give a new request if we got an rvalid
    // hence this combines the to most critical paths (from and to memory)
    generate
        // default assignment & one hot decoder
        for (i = 0; i < NR_PORTS; i++) begin
            assign data_rvalid_o[i] = out_data[i] & data_rvalid_i;
            assign data_rdata_o[i]  = data_rdata_i;
        end
    endgenerate

    always_comb begin : slave_read_port
        pop = 1'b0;
        // if there is a valid signal the FIFO should not be empty anyway
        if (data_rvalid_i) begin
            pop = 1'b1;
        end
    end

    // sequential process
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (~rst_ni) begin
            request_port_q <= 1'b0;
        end else begin
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
    assert property ( @(posedge clk_i) (data_req_o) |-> (!$isunknown(address_index_o)) )
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
