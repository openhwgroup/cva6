/* File:   nbdcache_pkh.sv
 * Author: Florian Zaruba <zarubaf@ethz.ch>
 * Date:   13.10.2017
 *
 * Copyright (C) 2017 ETH Zurich, University of Bologna
 * All rights reserved.
 *
 * Description: Contains all the necessary defines for the non-block DCache
 *              of Ariane in one package.
 */

package nbdcache_pkg;

    localparam int unsigned INDEX_WIDTH       = 12;
    localparam int unsigned TAG_WIDTH         = 44;
    localparam int unsigned CACHE_LINE_WIDTH  = 256;
    localparam int unsigned SET_ASSOCIATIVITY = 8;
    localparam int unsigned AXI_ID_WIDTH      = 10;
    localparam int unsigned AXI_USER_WIDTH    = 10;
    localparam int unsigned NR_MSHR           = 1;

    // Calculated params
    localparam NUM_WORDS = 2**INDEX_WIDTH;
    localparam DIRTY_WIDTH = (CACHE_LINE_WIDTH/64)*SET_ASSOCIATIVITY*2;

    typedef enum logic { SINGLE_REQ, CACHE_LINE_REQ } req_t;

    typedef struct packed {
        logic [1:0]  id;     // id for which we handle the miss
        logic        valid;
        logic        we;
        logic [55:0] addr;
    } mshr_t;

    typedef struct packed {
        logic                           valid;
        logic                           bypass;
        logic [63:0]                    addr;
        logic [CACHE_LINE_WIDTH/8-1:0]  be;
        logic                           we;
        logic [CACHE_LINE_WIDTH-1:0]    wdata;
    } miss_req_t;

    typedef struct packed {
        logic [TAG_WIDTH-1:0]        tag;    // tag array
        logic [CACHE_LINE_WIDTH-1:0] data;   // data array
        logic                        valid;  // state array
        logic                        dirty;  // state array
    } cache_line_t;

    // cache line byte enable
    typedef struct packed {
        logic [TAG_WIDTH-1:0]        tag;   // byte enable into tag array
        logic [CACHE_LINE_WIDTH-1:0] data;  // byte enable into data array
        logic [DIRTY_WIDTH-1:0]      state; // byte enable into state array
    } cl_be_t;

    // convert one hot to bin for -> needed for cache replacement
    function logic [$clog2(SET_ASSOCIATIVITY)-1:0] one_hot_to_bin (logic [SET_ASSOCIATIVITY-1:0] in);
        for (logic [$clog2(SET_ASSOCIATIVITY)-1:0] i = '0; i < SET_ASSOCIATIVITY; i++) begin
            if (in[i])
                return i;
        end
    endfunction

endpackage
