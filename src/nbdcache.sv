// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Author: Florian Zaruba, ETH Zurich
// Date: 13.10.2017
// Description: Nonblocking private L1 dcache

import ariane_pkg::*;
import std_cache_pkg::*;

module nbdcache #(
        parameter logic [63:0] CACHE_START_ADDR = 64'h4000_0000
)(
    input  logic                           clk_i,       // Clock
    input  logic                           rst_ni,      // Asynchronous reset active low
    // Cache management
    input  logic                           enable_i,    // from CSR
    input  logic                           flush_i,     // high until acknowledged
    output logic                           flush_ack_o, // send a single cycle acknowledge signal when the cache is flushed
    output logic                           miss_o,      // we missed on a ld/st
    // AMO interface
    input  logic                           amo_commit_i, // commit atomic memory operation
    output logic                           amo_valid_o,  // we have a valid AMO result
    output logic [63:0]                    amo_result_o, // result of atomic memory operation
    input  logic                           amo_flush_i,  // forget about AMO
    // Request ports
    input  dcache_req_i_t [2:0]            req_ports_i,  // request ports
    output dcache_req_o_t [2:0]            req_ports_o,  // request ports 

    // Cache AXI refill port
    AXI_BUS.Master                         data_if,
    AXI_BUS.Master                         bypass_if
);

    // -------------------------------
    // Controller <-> Arbiter
    // -------------------------------
    // 1. Miss handler
    // 2. PTW
    // 3. Load Unit
    // 4. Store unit
    logic        [3:0][DCACHE_SET_ASSOC-1:0]  req;
    logic        [3:0][DCACHE_INDEX_WIDTH-1:0]addr;
    logic        [3:0]                        gnt;
    cache_line_t [DCACHE_SET_ASSOC-1:0]       rdata;
    logic        [3:0][DCACHE_TAG_WIDTH-1:0]  tag;

    cache_line_t [3:0]                        wdata;
    logic        [3:0]                        we;
    cl_be_t      [3:0]                        be;
    logic        [DCACHE_SET_ASSOC-1:0]       hit_way;
    // -------------------------------
    // Controller <-> Miss unit
    // -------------------------------
    logic [2:0]                        busy;
    logic [2:0][55:0]                  mshr_addr;
    logic [2:0]                        mshr_addr_matches;
    logic [2:0]                        mshr_index_matches;
    logic [63:0]                       critical_word;
    logic                              critical_word_valid;

    logic [2:0][$bits(miss_req_t)-1:0] miss_req;
    logic [2:0]                        miss_gnt;
    logic [2:0]                        active_serving;

    logic [2:0]                        bypass_gnt;
    logic [2:0]                        bypass_valid;
    logic [2:0][63:0]                  bypass_data;
    // -------------------------------
    // Arbiter <-> Datram,
    // -------------------------------
    logic [DCACHE_SET_ASSOC-1:0]        req_ram;
    logic [DCACHE_INDEX_WIDTH-1:0]              addr_ram;
    logic                                we_ram;
    cache_line_t                         wdata_ram;
    cache_line_t [DCACHE_SET_ASSOC-1:0] rdata_ram;
    cl_be_t                              be_ram;

    // ------------------
    // Cache Controller
    // ------------------
    generate
        for (genvar i = 0; i < 3; i++) begin : master_ports
            cache_ctrl  #(
                .CACHE_START_ADDR      ( CACHE_START_ADDR     )
            ) i_cache_ctrl (
                .bypass_i              ( ~enable_i            ),

                .busy_o                ( busy            [i]  ),

                .req_port_i            ( req_ports_i     [i]  ),
                .req_port_o            ( req_ports_o     [i]  ),


                .req_o                 ( req            [i+1] ),
                .addr_o                ( addr           [i+1] ),
                .gnt_i                 ( gnt            [i+1] ),
                .data_i                ( rdata                ),
                .tag_o                 ( tag            [i+1] ),
                .data_o                ( wdata          [i+1] ),
                .we_o                  ( we             [i+1] ),
                .be_o                  ( be             [i+1] ),
                .hit_way_i             ( hit_way              ),

                .miss_req_o            ( miss_req        [i]  ),
                .miss_gnt_i            ( miss_gnt        [i]  ),
                .active_serving_i      ( active_serving  [i]  ),
                .critical_word_i       ( critical_word        ),
                .critical_word_valid_i ( critical_word_valid  ),
                .bypass_gnt_i          ( bypass_gnt      [i]  ),
                .bypass_valid_i        ( bypass_valid    [i]  ),
                .bypass_data_i         ( bypass_data     [i]  ),

                .mshr_addr_o           ( mshr_addr         [i] ), // TODO
                .mshr_addr_matches_i   ( mshr_addr_matches [i] ), // TODO
                .mshr_index_matches_i  ( mshr_index_matches[i] ), // TODO
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
        .bypass_gnt_o           ( bypass_gnt           ),
        .bypass_valid_o         ( bypass_valid         ),
        .bypass_data_o          ( bypass_data          ),
        .critical_word_o        ( critical_word        ),
        .critical_word_valid_o  ( critical_word_valid  ),
        .mshr_addr_i            ( mshr_addr            ),
        .mshr_addr_matches_o    ( mshr_addr_matches    ),
        .mshr_index_matches_o   ( mshr_index_matches   ),
        .active_serving_o       ( active_serving       ),
        .req_o                  ( req             [0]  ),
        .addr_o                 ( addr            [0]  ),
        .gnt_i                  ( gnt             [0]  ),
        .data_i                 ( rdata                ),
        .be_o                   ( be              [0]  ),
        .data_o                 ( wdata           [0]  ),
        .we_o                   ( we              [0]  ),
        .*
    );

    assign tag[0] = '0;

    // --------------
    // Memory Arrays
    // --------------
    for (genvar i = 0; i < DCACHE_SET_ASSOC; i++) begin : sram_block
        sram #(
            .DATA_WIDTH ( DCACHE_LINE_WIDTH                 ),
            .NUM_WORDS  ( DCACHE_NUM_WORDS                  )
        ) data_sram (
            .req_i   ( req_ram [i]                          ),
            .we_i    ( we_ram                               ),
            .addr_i  ( addr_ram[DCACHE_INDEX_WIDTH-1:DCACHE_BYTE_OFFSET]  ),
            .wdata_i ( wdata_ram.data                       ),
            .be_i    ( be_ram.data                          ),
            .rdata_o ( rdata_ram[i].data                    ),
            .*
        );

        sram #(
            .DATA_WIDTH ( DCACHE_TAG_WIDTH                  ),
            .NUM_WORDS  ( DCACHE_NUM_WORDS                  )
        ) tag_sram (
            .req_i   ( req_ram [i]                          ),
            .we_i    ( we_ram                               ),
            .addr_i  ( addr_ram[DCACHE_INDEX_WIDTH-1:DCACHE_BYTE_OFFSET]  ),
            .wdata_i ( wdata_ram.tag                        ),
            .be_i    ( be_ram.tag                           ),
            .rdata_o ( rdata_ram[i].tag                     ),
            .*
        );

    end

    // ----------------
    // Dirty SRAM
    // ----------------
    logic [DCACHE_DIRTY_WIDTH-1:0] dirty_wdata, dirty_rdata;

    for (genvar i = 0; i < DCACHE_SET_ASSOC; i++) begin
        assign dirty_wdata[i]                     = wdata_ram.dirty;
        assign dirty_wdata[DCACHE_SET_ASSOC + i] = wdata_ram.valid;
        assign rdata_ram[i].valid                 = dirty_rdata[DCACHE_SET_ASSOC + i];
        assign rdata_ram[i].dirty                 = dirty_rdata[i];
    end

    sram #(
        .DATA_WIDTH ( DCACHE_DIRTY_WIDTH               ),
        .NUM_WORDS  ( DCACHE_NUM_WORDS                 )
    ) dirty_sram (
        .clk_i   ( clk_i                               ),
        .req_i   ( |req_ram                            ),
        .we_i    ( we_ram                              ),
        .addr_i  ( addr_ram[DCACHE_INDEX_WIDTH-1:DCACHE_BYTE_OFFSET] ),
        .wdata_i ( dirty_wdata                         ),
        .be_i    ( {be_ram.valid, be_ram.dirty}        ),
        .rdata_o ( dirty_rdata                         )
    );

    // ------------------------------------------------
    // Tag Comparison and memory arbitration
    // ------------------------------------------------
    tag_cmp #(
        .NR_PORTS           ( 4                  ),
        .ADDR_WIDTH         ( DCACHE_INDEX_WIDTH ),
        .DCACHE_SET_ASSOC   ( DCACHE_SET_ASSOC   )
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
        assert (DCACHE_LINE_WIDTH/64 inside {2, 4, 8, 16}) else $fatal(1, "Cache line size needs to be a power of two multiple of 64");
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
        parameter int unsigned DCACHE_SET_ASSOC = 8
    )(
        input  logic                                         clk_i,
        input  logic                                         rst_ni,

        input  logic  [NR_PORTS-1:0][DCACHE_SET_ASSOC-1:0]  req_i,
        output logic  [NR_PORTS-1:0]                         gnt_o,
        input  logic  [NR_PORTS-1:0][ADDR_WIDTH-1:0]         addr_i,
        input  data_t [NR_PORTS-1:0]                         wdata_i,
        input  logic  [NR_PORTS-1:0]                         we_i,
        input  be_t   [NR_PORTS-1:0]                         be_i,
        output data_t               [DCACHE_SET_ASSOC-1:0]  rdata_o,
        input  logic  [NR_PORTS-1:0][DCACHE_TAG_WIDTH-1:0]          tag_i, // tag in - comes one cycle later
        output logic                [DCACHE_SET_ASSOC-1:0]  hit_way_o, // we've got a hit on the corresponding way


        output logic                [DCACHE_SET_ASSOC-1:0]  req_o,
        output logic                [ADDR_WIDTH-1:0]         addr_o,
        output data_t                                        wdata_o,
        output logic                                         we_o,
        output be_t                                          be_o,
        input  data_t               [DCACHE_SET_ASSOC-1:0]  rdata_i
    );

    assign rdata_o = rdata_i;
    // one hot encoded
    logic [NR_PORTS-1:0] id_d, id_q;
    logic [DCACHE_TAG_WIDTH-1:0] sel_tag;

    always_comb begin : tag_sel
        sel_tag = '0;
        for (int unsigned i = 0; i < NR_PORTS; i++)
            if (id_q[i])
                sel_tag = tag_i[i];
    end

    for (genvar j = 0; j < DCACHE_SET_ASSOC; j++) begin : tag_cmp
        assign hit_way_o[j] = (sel_tag == rdata_i[j].tag) ? rdata_i[j].valid : 1'b0;
    end

    always_comb begin

        gnt_o     = '0;
        id_d      = '0;
        wdata_o   = '0;
        req_o     = '0;
        addr_o    = '0;
        be_o      = '0;
        we_o      = '0;
        // Request Side
        // priority select
        for (int unsigned i = 0; i < NR_PORTS; i++) begin
            req_o    = req_i[i];
            id_d     = (1'b1 << i);
            gnt_o[i] = 1'b1;
            addr_o   = addr_i[i];
            be_o     = be_i[i];
            we_o     = we_i[i];
            wdata_o  = wdata_i[i];

            if (req_i[i])
                break;
        end

        `ifndef SYNTHESIS
        `ifndef VERILATOR
        // assert that cache only hits on one way
        assert property (
          @(posedge clk_i) $onehot0(hit_way_o)) else begin $error("Hit should be one-hot encoded"); $stop(); end
        `endif
        `endif
    end

    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (~rst_ni) begin
            id_q <= 0;
        end else begin
            id_q <= id_d;
        end
    end

endmodule
