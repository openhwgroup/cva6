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
// Author: Florian Zaruba    <zarubaf@iis.ee.ethz.ch>, ETH Zurich
//         Michael Schaffner <schaffner@iis.ee.ethz.ch>, ETH Zurich
// Date: 15.08.2018

// ******* WIP *******
// Description: package for the standard Ariane cache subsystem.

package std_cache_pkg;

    // Calculated parameter
    localparam DCACHE_BYTE_OFFSET = $clog2(ariane_pkg::DCACHE_LINE_WIDTH/8);
    localparam DCACHE_NUM_WORDS   = 2**(ariane_pkg::DCACHE_INDEX_WIDTH-DCACHE_BYTE_OFFSET);
    localparam DCACHE_DIRTY_WIDTH = ariane_pkg::DCACHE_SET_ASSOC*2;
    // localparam DECISION_BIT = 30; // bit on which to decide whether the request is cache-able or not

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
        logic [ariane_pkg::DCACHE_TAG_WIDTH-1:0]  tag;    // tag array
        logic [ariane_pkg::DCACHE_LINE_WIDTH-1:0] data;   // data array
        logic                                     valid;  // state array
        logic                                     dirty;  // state array
    } cache_line_t;

    // cache line byte enable
    typedef struct packed {
        logic [(ariane_pkg::DCACHE_TAG_WIDTH+7)/8-1:0]  tag;    // byte enable into tag array
        logic [(ariane_pkg::DCACHE_LINE_WIDTH+7)/8-1:0] data;   // byte enable into data array
        logic [ariane_pkg::DCACHE_SET_ASSOC-1:0]        vldrty; // bit enable into state array (valid for a pair of dirty/valid bits)
    } cl_be_t;

    // convert one hot to bin for -> needed for cache replacement
    function automatic logic [$clog2(ariane_pkg::DCACHE_SET_ASSOC)-1:0] one_hot_to_bin (
        input logic [ariane_pkg::DCACHE_SET_ASSOC-1:0] in
    );
        for (int unsigned i = 0; i < ariane_pkg::DCACHE_SET_ASSOC; i++) begin
            if (in[i])
                return i;
        end
    endfunction
    // get the first bit set, returns one hot value
    function automatic logic [ariane_pkg::DCACHE_SET_ASSOC-1:0] get_victim_cl (
        input logic [ariane_pkg::DCACHE_SET_ASSOC-1:0] valid_dirty
    );
        // one-hot return vector
        logic [ariane_pkg::DCACHE_SET_ASSOC-1:0] oh = '0;
        for (int unsigned i = 0; i < ariane_pkg::DCACHE_SET_ASSOC; i++) begin
            if (valid_dirty[i]) begin
                oh[i] = 1'b1;
                return oh;
            end
        end
    endfunction
endpackage : std_cache_pkg

