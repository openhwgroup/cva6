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

module miss_arbiter #(
        parameter int unsigned NR_PORTS = 3
)(
    input  logic                           clk_i,          // Clock
    input  logic                           rst_ni,         // Asynchronous reset active low
    // master ports
    input  logic [NR_PORTS-1:0]            data_req_i,
    input  logic [NR_PORTS-1:0][63:0]      address_i,
    input  logic [NR_PORTS-1:0][63:0]      data_wdata_i,
    input  logic [NR_PORTS-1:0]            data_we_i,
    input  logic [NR_PORTS-1:0][7:0]       data_be_i,
    output logic [NR_PORTS-1:0]            data_gnt_o,
    output logic [NR_PORTS-1:0]            data_rvalid_o,
    output logic [NR_PORTS-1:0][63:0]      data_rdata_o,
    // slave port
    input  logic [$clog2(NR_PORTS)-1:0]    id_i,
    output logic [$clog2(NR_PORTS)-1:0]    id_o,
    output logic                           data_req_o,
    output logic [63:0]                    address_o,
    output logic [63:0]                    data_wdata_o,
    output logic                           data_we_o,
    output logic [7:0]                     data_be_o,
    input  logic                           data_gnt_i,
    input  logic                           data_rvalid_i,
    input  logic [63:0]                    data_rdata_i
);


    // addressing read and full write
    always_comb begin : read_req_write
        automatic logic [$clog2(NR_PORTS)-1:0] request_index = 0;

        data_req_o = 1'b0;
        data_gnt_o = '0;

        for (int unsigned i = 0; i < NR_PORTS; i++) begin
            if (data_req_i[i] == 1'b1) begin
                data_req_o        = data_req_i[i];
                request_index     = i;
                break; // break here as this is a priority select
            end
        end

        // pass through all signals from the correct slave port
        address_o                 = address_i[request_index];
        data_wdata_o              = data_wdata_i[request_index];
        data_be_o                 = data_be_i[request_index];
        data_we_o                 = data_we_i[request_index];
        data_gnt_o[request_index] = data_gnt_i;
        id_o                      = request_index;
    end

    // ------------
    // Read port
    // ------------

    always_comb begin : slave_read_port
        data_rvalid_o = '0;
        data_rdata_o = '0;
        // if there is a valid signal the FIFO should not be empty anyway
        if (data_rvalid_i) begin
            data_rvalid_o[id_i] = data_rvalid_i;
            data_rdata_o [id_i] = data_rdata_i;
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
