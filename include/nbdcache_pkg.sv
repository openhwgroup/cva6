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

    typedef enum logic { SINGLE_REQ, CACHE_LINE_REQ } req_t;
    typedef enum logic { LOAD_MISS, STORE_MISS } miss_t;

    typedef struct packed {
        logic        valid;
        miss_t       req_type;
        logic [55:0] addr;
    } mshr_t;

    typedef struct packed {
        logic          valid;
        logic          bypass;
        logic [63:0]   addr;
        logic [7:0]    be;
        logic          we;
        logic [63:0]   wdata;
    } miss_req_t;

    localparam int unsigned NR_MSHR = 1;
endpackage
