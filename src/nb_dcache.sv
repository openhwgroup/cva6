// Author: Florian Zaruba, ETH Zurich
// Date: 13.10.2017
// Description: Nonblocking private L1 dcache
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

import ariane_pkg::*;
import nbdcache_pkg::*;

module nb_dcache #(
    parameter int unsigned INDEX_WIDTH       = 12,
    parameter int unsigned TAG_WIDTH         = 44,
    parameter int unsigned CACHE_LINE_WIDTH  = 256,
    parameter int unsigned SET_ASSOCIATIVITY = 8,
    parameter int unsigned AXI_ID_WIDTH      = 10,
    parameter int unsigned AXI_USER_WIDTH    = 10
)(
    input logic                            clk_i,    // Clock
    input logic                            rst_ni,   // Asynchronous reset active low
    // AXI refill port
    AXI_BUS.Master                         data_if,
    // AMO interface
    input  logic                           amo_commit_i, // commit atomic memory operation
    output logic                           amo_valid_o,  // we have a valid AMO result
    output logic [63:0]                    amo_result_o, // result of atomic memory operation
    // Request ports
    input  logic [2:0][INDEX_WIDTH-1:0]    address_index_i,
    input  logic [2:0][TAG_WIDTH-1:0]      address_tag_i,
    input  logic [2:0][63:0]               data_wdata_i,
    input  logic [2:0]                     data_req_i,
    input  logic [2:0]                     data_we_i,
    input  logic [2:0][7:0]                data_be_i,
    input  logic [2:0]                     kill_req_i,
    input  logic [2:0]                     tag_valid_i,
    output logic [2:0]                     data_gnt_o,
    output logic [2:0]                     data_rvalid_o,
    output logic [2:0][63:0]               data_rdata_o,
    input  amo_t [2:0]                     amo_op_i
);

    localparam NUM_WORDS = 2**INDEX_WIDTH;
    localparam DIRTY_WIDTH = (CACHE_LINE_WIDTH/64)*SET_ASSOCIATIVITY;

    // AMO ALU


    // Cache FSM


    // --------------
    // Memories
    // --------------
    // TODO: Re-work
    generate
        for (genvar i = 0; i < SET_ASSOCIATIVITY; i++) begin : set_associativity
            sram #(
                .DATA_WIDTH ( CACHE_LINE_WIDTH ),
                .NUM_WORDS  ( NUM_WORDS        )
            ) data_sram (
                .clk_i   ( clk_i   ),
                .req_i   (         ),
                .we_i    (         ),
                .addr_i  (         ),
                .wdata_i (         ),
                .be_i    (         ),
                .rdata_o (         )
            );

            sram #(
                .DATA_WIDTH ( TAG_WIDTH        ),
                .NUM_WORDS  ( NUM_WORDS        )
            ) tag_sram (
                .clk_i   ( clk_i   ),
                .req_i   (         ),
                .we_i    (         ),
                .addr_i  (         ),
                .wdata_i (         ),
                .be_i    (         ),
                .rdata_o (         )
            );

        end
    endgenerate

    sram #(
        .DATA_WIDTH ( DIRTY_WIDTH ),
        .NUM_WORDS  ( NUM_WORDS   )
    ) dirty_sram (
        .clk_i   ( clk_i   ),
        .req_i   (         ),
        .we_i    (         ),
        .addr_i  (         ),
        .wdata_i (         ),
        .be_i    (         ),
        .rdata_o (         )
    );

    // AXI Module

`ifndef SYNTHESIS
    initial begin
        assert ($bits(data_if.aw_addr) == 64) else $fatal(1, "Ariane needs a 64-bit bus");
        assert (CACHE_LINE_WIDTH/64 inside {2, 4, 8, 16}) else $fatal(1, "Cache line size needs to be a power of two multiple of 64");
    end
`endif
endmodule
