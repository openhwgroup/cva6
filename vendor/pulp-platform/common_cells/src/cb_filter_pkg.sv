// Copyright (c) 2019 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Author: Wolfgang Roenninger <wroennin@ethz.ch>

/// Package with the struct definition for the seeds and an example.
package cb_filter_pkg;
  typedef struct packed {
    int unsigned PermuteSeed;
    int unsigned XorSeed;
  } cb_seed_t;

  // example seeding struct
  localparam cb_seed_t [2:0] EgSeeds = '{
    '{PermuteSeed: 32'd299034753, XorSeed: 32'd4094834  },
    '{PermuteSeed: 32'd19921030,  XorSeed: 32'd995713   },
    '{PermuteSeed: 32'd294388,    XorSeed: 32'd65146511 }
  };
endpackage
