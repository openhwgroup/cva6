/* File:   ariane_pkg.svh
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

endpackage
