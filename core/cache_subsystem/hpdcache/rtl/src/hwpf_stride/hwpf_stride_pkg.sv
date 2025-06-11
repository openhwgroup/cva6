/*
 *  Copyright 2023 CEA*
 *  *Commissariat a l'Energie Atomique et aux Energies Alternatives (CEA)
 *
 *  SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
 *
 *  Licensed under the Solderpad Hardware License v 2.1 (the “License”); you
 *  may not use this file except in compliance with the License, or, at your
 *  option, the Apache License version 2.0. You may obtain a copy of the
 *  License at
 *
 *  https://solderpad.org/licenses/SHL-2.1/
 *
 *  Unless required by applicable law or agreed to in writing, any work
 *  distributed under the License is distributed on an “AS IS” BASIS, WITHOUT
 *  WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
 *  License for the specific language governing permissions and limitations
 *  under the License.
 */
/*
 *  Authors       : Cesar Fuguet
 *  Creation Date : January, 2023
 *  Description   : High-Performance, Data-cache (HPDcache) HW memory
 *                  prefetcher package
 *  History       :
 */
package hwpf_stride_pkg;
    //  Base address configuration register of the hardware memory prefetcher
    //  {{{
    typedef struct packed {
            logic [63:6] base_cline;
            logic [5:3]  unused;
            logic        cycle;
            logic        rearm;
            logic        enable;
            } hwpf_stride_base_t;
    //  }}}

    //  Parameters configuration register of the hardware memory prefetcher
    //  {{{
    typedef struct packed {
            logic [63:48] nblocks;
            logic [47:32] nlines;
            logic [31:0]  stride;
            } hwpf_stride_param_t;
    //  }}}

    //  Throttle configuration register of the hardware memory prefetcher
    //  {{{
    typedef struct packed {
            logic [31:16] ninflight;
            logic [15:0]  nwait;
            } hwpf_stride_throttle_t;
    //  }}}

    //  Status register of the hardware memory prefetcher
    //  {{{
    typedef struct packed {
            logic [63:48] unused1;
            logic [47:32] busy;
            logic         free;
            logic [30:20] unused0;
            logic [19:16] free_index;
            logic [15:0]  enabled;
            } hwpf_stride_status_t;
    //  }}}

endpackage
