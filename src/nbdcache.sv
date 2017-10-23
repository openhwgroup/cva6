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

module nbdcache (
    input  logic                           clk_i,    // Clock
    input  logic                           rst_ni,   // Asynchronous reset active low
    // Cache control
    input  logic                           enable_i, // from CSR
    // Cache AXI refill port
    AXI_BUS.Master                         data_if,
    AXI_BUS.Master                         bypass_if,
    // AMO interface
    input  logic                           amo_commit_i, // commit atomic memory operation
    output logic                           amo_valid_o,  // we have a valid AMO result
    output logic [63:0]                    amo_result_o, // result of atomic memory operation
    input  logic                           amo_flush_i,  // forget about AMO
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

    // -------------------------------
    // Controller <-> Arbiter
    // -------------------------------
    // 1. Miss handler
    // 2. PTW
    // 3. Load Unit
    // 4. Store unit
    logic        [3:0][SET_ASSOCIATIVITY-1:0] req;
    logic        [3:0][INDEX_WIDTH-1:0]       addr;
    logic        [3:0]                        gnt;
    cache_line_t [3:0][SET_ASSOCIATIVITY-1:0] rdata;
    cache_line_t [3:0][TAG_WIDTH-1:0]         tag;

    cache_line_t [3:0]                        wdata;
    logic        [3:0]                        we;
    cl_be_t      [3:0]                        be;
    logic        [SET_ASSOCIATIVITY-1:0]      hit_way;
    // -------------------------------
    // Controller <-> Miss unit
    // -------------------------------
    logic [2:0]                        busy;
    logic [2:0][55:0]                  mshr_addr;
    logic [2:0]                        mshr_addr_matches;
    logic [63:0]                       critical_word;
    logic                              critical_word_valid;

    logic [2:0][$bits(miss_req_t)-1:0] miss_req;
    logic [2:0]                        miss_gnt;
    logic [2:0]                        miss_valid;
    logic [2:0][CACHE_LINE_WIDTH-1:0]  miss_data;

    logic [2:0]                        bypass_gnt;
    logic [2:0]                        bypass_valid;
    logic [2:0][CACHE_LINE_WIDTH-1:0]  bypass_data;
    // -------------------------------
    // Arbiter <-> Datram,
    // -------------------------------
    logic [SET_ASSOCIATIVITY-1:0]        req_ram;
    logic [INDEX_WIDTH-1:0]              addr_ram;
    logic                                we_ram;
    cache_line_t                         wdata_ram;
    cache_line_t [SET_ASSOCIATIVITY-1:0] rdata_ram;
    cl_be_t                              be_ram;

    // ------------------
    // Cache Controller
    // ------------------
    generate
        for (genvar i = 0; i < 3; i++) begin : master_ports
            cache_ctrl  #(
                .SET_ASSOCIATIVITY     ( SET_ASSOCIATIVITY    ),
                .INDEX_WIDTH           ( INDEX_WIDTH          ),
                .TAG_WIDTH             ( TAG_WIDTH            ),
                .CACHE_LINE_WIDTH      ( CACHE_LINE_WIDTH     )
            ) i_cache_ctrl (
                .bypass_i              ( ~enable_i            ),
                .busy_o                ( busy            [i]  ),
                .address_index_i       ( address_index_i [i]  ),
                .address_tag_i         ( address_tag_i   [i]  ),
                .data_wdata_i          ( data_wdata_i    [i]  ),
                .data_req_i            ( data_req_i      [i]  ),
                .data_we_i             ( data_we_i       [i]  ),
                .data_be_i             ( data_be_i       [i]  ),
                .kill_req_i            ( kill_req_i      [i]  ),
                .tag_valid_i           ( tag_valid_i     [i]  ),
                .data_gnt_o            ( data_gnt_o      [i]  ),
                .data_rvalid_o         ( data_rvalid_o   [i]  ),
                .data_rdata_o          ( data_rdata_o    [i]  ),
                .amo_op_i              ( amo_op_i        [i]  ),

                .req_o                 ( req             [i]  ),
                .addr_o                ( addr            [i]  ),
                .gnt_i                 ( gnt             [i]  ),
                .data_i                ( rdata                ),
                .tag_o                 ( tag             [i]  ),
                .data_o                ( wdata           [i]  ),
                .we_o                  ( we              [i]  ),
                .be_o                  ( be              [i]  ),
                .hit_way_i             ( hit_way              ),

                .miss_req_o            ( miss_req        [i]  ),
                .miss_gnt_i            ( miss_gnt        [i]  ),
                .miss_valid_i          ( miss_valid      [i]  ),
                .miss_data_i           ( miss_data       [i]  ),
                .critical_word_i       ( critical_word        ),
                .critical_word_valid_i ( critical_word_valid  ),
                .bypass_gnt_i          ( bypass_gnt      [i]  ),
                .bypass_valid_i        ( bypass_valid    [i]  ),
                .bypass_data_i         ( bypass_data     [i]  ),

                .mshr_addr_o           ( mshr_addr         [i] ), // TODO
                .mashr_addr_matches_i  ( mshr_addr_matches [i] ), // TODO
                .*
            );
        end
    endgenerate

    // ------------------
    // Miss Handling Unit
    // ------------------
    miss_handler #(
        .NR_PORTS               ( 3                    )
    ) i_miss_handler (
        .busy_i                 ( |busy                ),
        .miss_req_i             ( miss_req             ),
        .miss_gnt_o             ( miss_gnt             ),
        .miss_valid_o           ( miss_valid           ),
        .miss_data_o            ( miss_data            ),
        .bypass_gnt_o           ( bypass_gnt           ),
        .bypass_valid_o         ( bypass_valid         ),
        .bypass_data_o          ( bypass_data          ),
        .critical_word_o        ( critical_word        ),
        .critical_word_valid_o  ( critical_word_valid  ),
        .mshr_addr_i            ( mshr_addr            ),
        .mashr_addr_matches_o   ( mshr_addr_matches    ),
        .req_o                  ( req             [2]  ),
        .addr_o                 ( addr            [2]  ),
        .gnt_i                  ( gnt             [2]  ),
        .data_o                 ( rdata                ),
        .be_o                   ( wdata           [2]  ),
        .data_i                 ( we              [2]  ),
        .we_o                   ( be              [2]  ),
        .*
    );

    // --------------
    // Memory Arrays
    // --------------
    generate
        for (genvar i = 0; i < SET_ASSOCIATIVITY; i++) begin : sram_block
            sram #(
                .DATA_WIDTH ( CACHE_LINE_WIDTH ),
                .NUM_WORDS  ( NUM_WORDS        )
            ) data_sram (
                .req_i   ( req_ram [i]         ),
                .we_i    ( we_ram              ),
                .addr_i  ( addr_ram            ),
                .wdata_i ( wdata_ram.data      ),
                .be_i    ( be_ram.data         ),
                .rdata_o ( rdata_ram[i].data   ),
                .*
            );

            sram #(
                .DATA_WIDTH ( TAG_WIDTH        ),
                .NUM_WORDS  ( NUM_WORDS        )
            ) tag_sram (
                .req_i   ( req_ram [i]         ),
                .we_i    ( we_ram              ),
                .addr_i  ( addr_ram            ),
                .wdata_i ( wdata_ram.tag       ),
                .be_i    ( be_ram.tag          ),
                .rdata_o ( rdata_ram[i].tag    ),
                .*
            );

        end
    endgenerate

    // ----------------
    // Dirty SRAM
    // ----------------
    sram #(
        .DATA_WIDTH ( DIRTY_WIDTH ),
        .NUM_WORDS  ( NUM_WORDS   )
    ) dirty_sram (
        .clk_i   ( clk_i                                                                            ),
        .req_i   ( req_ram                                                                          ),
        .we_i    ( we_ram                                                                           ),
        .addr_i  ( addr_ram                                                                         ),
        .wdata_i ( {wdata_ram[SET_ASSOCIATIVITY-1:0].dirty, wdata_ram[SET_ASSOCIATIVITY-1:0].valid} ),
        .be_i    ( be_ram.state                                                                     ),
        .rdata_o ( {rdata_ram[SET_ASSOCIATIVITY-1:0].dirty, rdata_ram[SET_ASSOCIATIVITY-1:0].valid} )
    );

    // ------------------------------------------------
    // Tag Comparison and memory arbitration
    // ------------------------------------------------
    tag_cmp #(
        .NR_PORTS           ( 4                  ),
        .ADDR_WIDTH         ( INDEX_WIDTH        ),
        .SET_ASSOCIATIVITY  ( SET_ASSOCIATIVITY  )
    ) i_tag_cmp (
        .req_i              ( req         ),
        .gnt_o              ( gnt         ),
        .addr_i             ( addr        ),
        .wdata_i            ( wdata       ),
        .we_i               ( we          ),
        .be_i               ( be          ),
        .rdata_o            ( rdata       ),
        .tag_i              ( tag         ),
        .hit_way_o          ( hit_way     ),

        .req_o              ( req_ram     ),
        .addr_o             ( addr_ram    ),
        .wdata_o            ( wdata_ram   ),
        .we_o               ( we_ram      ),
        .be_o               ( be_ram      ),
        .rdata_i            ( rdata_ram   ),
        .*
    );


`ifndef SYNTHESIS
    initial begin
        assert ($bits(data_if.aw_addr) == 64) else $fatal(1, "Ariane needs a 64-bit bus");
        assert (CACHE_LINE_WIDTH/64 inside {2, 4, 8, 16}) else $fatal(1, "Cache line size needs to be a power of two multiple of 64");
    end
`endif
endmodule

// --------------
// Tag Compare
// --------------
//
// Description: Arbitrates access to cache memories, simplified request grant protocol
//              checks for hit or miss on cache
//
module tag_cmp #(
        parameter int unsigned NR_PORTS          = 3,
        parameter int unsigned ADDR_WIDTH        = 64,
        parameter type data_t                    = cache_line_t,
        parameter type be_t                      = cl_be_t,
        parameter int unsigned SET_ASSOCIATIVITY = 8
    )(
        input  logic                                         clk_i,
        input  logic                                         rst_ni,

        input  logic  [NR_PORTS-1:0][SET_ASSOCIATIVITY-1:0]  req_i,
        output logic  [NR_PORTS-1:0]                         gnt_o,
        input  logic  [NR_PORTS-1:0][ADDR_WIDTH-1:0]         addr_i,
        input  data_t [NR_PORTS-1:0]                         wdata_i,
        input  logic  [NR_PORTS-1:0]                         we_i,
        input  be_t   [NR_PORTS-1:0]                         be_i,
        output data_t               [SET_ASSOCIATIVITY-1:0]  rdata_o,
        input  logic  [NR_PORTS-1:0][TAG_WIDTH-1:0]          tag_i, // tag in - comes one cycle later
        output logic                [SET_ASSOCIATIVITY-1:0]  hit_way_o, // we've got a hit on the corresponding way


        output logic                [SET_ASSOCIATIVITY-1:0]  req_o,
        output logic                [ADDR_WIDTH-1:0]         addr_o,
        output data_t                                        wdata_o,
        output logic                                         we_o,
        output be_t                                          be_o,
        input  data_t               [SET_ASSOCIATIVITY-1:0]  rdata_i
    );

    // if there is some request output it directly
    assign req_o = |req_i;
    // one hot encoded
    logic [NR_PORTS-1:0] id_d, id_q;

    always_comb begin

        gnt_o     = '0;
        rdata_o   = '0;
        id_d      = '0;
        hit_way_o = '0;

        // Request Side
        // priority select
        for (int unsigned i = 0; i < NR_PORTS; i++) begin
            if (req_i[i]) begin
                id_d     = (1'b1 << i);
                gnt_o[i] = 1'b1;
                addr_o   = addr_i[i];
                be_o     = be_i[i];
                we_o     = we_i[i];
                wdata_o  = wdata_i[i];
                break;
            end
        end

        // Response Side
        for (int unsigned i = 0; i < NR_PORTS; i++) begin
            if (id_q[i]) begin
                rdata_o[i] = rdata_i;
                // Tag compare
                for (int unsigned j = 0; j < SET_ASSOCIATIVITY; j++) begin
                    // compare tag and check validity
                    if (rdata_i[j].tag == tag_i[i] && rdata_i[j].valid)
                        hit_way_o[j] = 1'b1;
                end
            end
        end
        // assert that cache only hits on one way
    end

    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (~rst_ni) begin
            id_q <= 0;
        end else begin
            id_q <= id_d;
        end
    end

endmodule

