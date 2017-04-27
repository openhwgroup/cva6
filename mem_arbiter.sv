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

module mem_arbiter #(
        parameter int NR_PORTS = 3
    )
    (
    input  logic                           clk_i,          // Clock
    input  logic                           rst_ni,         // Asynchronous reset active low
    output logic                           flush_ready_o,  // the flush is ready, e.g.: all transaction returned
    // slave port
    output logic [63:0]                    address_o,
    output logic [63:0]                    data_wdata_o,
    output logic                           data_req_o,
    output logic                           data_we_o,
    output logic [7:0]                     data_be_o,
    input  logic                           data_gnt_i,
    input  logic                           data_rvalid_i,
    input  logic [63:0]                    data_rdata_i,
    // master ports
    input  logic [NR_PORTS-1:0][63:0]      address_i,
    input  logic [NR_PORTS-1:0][63:0]      data_wdata_i,
    input  logic [NR_PORTS-1:0]            data_req_i,
    input  logic [NR_PORTS-1:0]            data_we_i,
    input  logic [NR_PORTS-1:0][7:0]       data_be_i,
    output logic [NR_PORTS-1:0]            data_gnt_o,
    output logic [NR_PORTS-1:0]            data_rvalid_o,
    output logic [NR_PORTS-1:0][63:0]      data_rdata_o
);

    logic full_o;
    logic empty_o;
    logic [NR_PORTS-1:0] data_i;
    logic push_i;
    logic [NR_PORTS-1:0] data_o;
    logic pop_i;
    logic single_element_o;
    // essentially wait for the queue to be empty
    // or we just got a grant -> this means we issued a memory request in this cycle
    // although we are ready if we only got a single element in the queue and an rvalid
    // which means we are getting this element back in this cycle
    assign flush_ready_o = (empty_o & ~(|data_gnt_i)) | (single_element_o & data_rvalid_i);

    fifo #(
        .dtype            ( logic [NR_PORTS-1:0] ),
        .DEPTH            ( 4                    )
    ) fifo_i (
        .clk_i            ( clk_i                ),
        .rst_ni           ( rst_ni               ),
        .single_element_o ( single_element_o     ),
        // the flush is accomplished implicitly by waiting for the flush ready signal
        .flush_i          ( 1'b0                 ),
        .full_o           ( full_o               ),
        .empty_o          ( empty_o              ),
        .data_i           ( data_i               ),
        .push_i           ( push_i               ),
        .data_o           ( data_o               ),
        .pop_i            ( pop_i                )
    );

    // addressing read and full write
    always_comb begin : read_req_write
        // default assignment
        data_req_o   = 1'b0;
        address_o    = address_i[0];
        data_wdata_o = data_wdata_i[0];
        data_be_o    = data_be_i[0];
        data_we_o    = data_we_i[0];
        data_i       = '{default: 0};
        push_i       = 1'b0;

        for (int i = 0; i < NR_PORTS; i++)
            data_gnt_o[i] = 1'b0;
        // only go for a new request if we can wait for the valid e.g.: we have enough space in the buffer
        if (~full_o) begin
            for (int i = 0; i < NR_PORTS; i++) begin
                if (data_req_i[i] == 1'b1) begin
                    // pass through all signals from the correct slave port
                    data_req_o   = data_req_i[i];
                    address_o    = address_i[i];
                    data_wdata_o = data_wdata_i[i];
                    data_be_o    = data_be_i[i];
                    data_we_o    = data_we_i[i];

                    // wait on the grant
                    if (data_gnt_i) begin
                        data_gnt_o[i] = data_gnt_i;
                        // set the slave on which we are waiting
                        data_i = i;
                        push_i = 1'b1;
                    end
                    break; // break here as this is a priority select
                end
            end
        end
    end

    // results, listening on the input signals of the slave port
    always_comb begin : slave_read_port
        pop_i = 1'b0;
        // default assignment
        for (int i = 0; i < NR_PORTS; i++) begin
            data_rvalid_o[i] = 1'b0;
            data_rdata_o[i]  = 64'b0;
        end
        // if there is an entry in the queue -> we are waiting for a read/write to return
        // if there is a valid signal the FIFO should not be empty anyway
        if (data_rvalid_i) begin
            // pass the read to the appropriate slave
            pop_i                 = 1'b1;
            data_rvalid_o[data_o] = data_rvalid_i;
            data_rdata_o[data_o]  = data_rdata_i;
        end
    end

endmodule