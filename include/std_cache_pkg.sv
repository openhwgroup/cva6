// Copyright (c) 2018 ETH Zurich, University of Bologna
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
// Author: Florian Zaruba    <zarubaf@iis.ee.ethz.ch>, ETH Zurich
//         Michael Schaffner <schaffner@iis.ee.ethz.ch>, ETH Zurich
// Date: 15.08.2018
// Description: package for the standard Ariane cache subsystem.

package std_cache_pkg;

    import ariane_pkg::*;

    localparam int unsigned NR_MSHR           = 1;

    // Calculated parameter
    localparam BYTE_OFFSET = $clog2(CACHE_LINE_WIDTH/8);
    localparam NUM_WORDS = 2**(INDEX_WIDTH-BYTE_OFFSET);
    localparam DIRTY_WIDTH = SET_ASSOCIATIVITY*2;
    // localparam DECISION_BIT = 30; // bit on which to decide whether the request is cache-able or not

    typedef enum logic { SINGLE_REQ, CACHE_LINE_REQ } req_t;


    typedef struct packed {
        logic [1:0]      id;     // id for which we handle the miss
        logic            valid;
        logic            we;
        logic [55:0]     addr;
        logic [7:0][7:0] wdata;
        logic [7:0]      be;
    } mshr_t;

    typedef struct packed {
        logic         valid;
        logic [63:0]  addr;
        logic [7:0]   be;
        logic [1:0]   size;
        logic         we;
        logic [63:0]  wdata;
        logic         bypass;
    } miss_req_t;

    typedef struct packed {
        logic [TAG_WIDTH-1:0]           tag;    // tag array
        logic [CACHE_LINE_WIDTH-1:0]    data;   // data array
        logic                           valid;  // state array
        logic                           dirty;  // state array
    } cache_line_t;

    // cache line byte enable
    typedef struct packed {
        logic [TAG_WIDTH-1:0]        tag;   // byte enable into tag array
        logic [CACHE_LINE_WIDTH-1:0] data;  // byte enable into data array
        logic [DIRTY_WIDTH/2-1:0]    dirty; // byte enable into state array
        logic [DIRTY_WIDTH/2-1:0]    valid; // byte enable into state array
    } cl_be_t;

    // convert one hot to bin for -> needed for cache replacement
    function automatic logic [$clog2(SET_ASSOCIATIVITY)-1:0] one_hot_to_bin (input logic [SET_ASSOCIATIVITY-1:0] in);
        for (int unsigned i = 0; i < SET_ASSOCIATIVITY; i++) begin
            if (in[i])
                return i;
        end
    endfunction
    // get the first bit set, returns one hot value
    function automatic logic [SET_ASSOCIATIVITY-1:0] get_victim_cl (input logic [SET_ASSOCIATIVITY-1:0] valid_dirty);
        // one-hot return vector
        logic [SET_ASSOCIATIVITY-1:0] oh = '0;
        for (int unsigned i = 0; i < SET_ASSOCIATIVITY; i++) begin
            if (valid_dirty[i]) begin
                oh[i] = 1'b1;
                return oh;
            end
        end
    endfunction
endpackage : std_cache_pkg

