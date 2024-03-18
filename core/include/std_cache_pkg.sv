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
    logic        valid;
    logic [63:0] addr;
    logic [7:0]  be;
    logic [1:0]  size;
    logic        we;
    logic [63:0] wdata;
    logic        bypass;
  } miss_req_t;

  typedef struct packed {
    logic                req;
    ariane_pkg::ad_req_t reqtype;
    ariane_pkg::amo_t    amo;
    logic [3:0]          id;
    logic [63:0]         addr;
    logic [63:0]         wdata;
    logic                we;
    logic [7:0]          be;
    logic [1:0]          size;
  } bypass_req_t;

  typedef struct packed {
    logic        gnt;
    logic        valid;
    logic [63:0] rdata;
  } bypass_rsp_t;

endpackage : std_cache_pkg

