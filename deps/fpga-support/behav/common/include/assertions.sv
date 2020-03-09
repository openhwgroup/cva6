// Copyright 2016 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

/**
 * Assertions for Actual/Expected Comparisons in Testbenches
 *
 * Current Maintainers:
 * - Andreas Kurth  <akurth@iis.ee.ethz.ch>
 * - Pirmin Vogel   <vogelpi@iis.ee.ethz.ch>
 */

`ifndef ASSERTIONS_SV
`define ASSERTIONS_SV

`define assert_equal(actual, expected) \
  assert (actual == expected) \
    else $error("Failed assertion: %0d == %0d", actual, expected);

`define assert_equal_msg(actual, expected, msg, ln) \
  assert (actual == expected) \
    else $error("Failed assertion (ExpResp LN %04d, %s): %x == %x", \
        ln, msg, actual, expected);

`endif // ASSERTIONS_SV

// vim: nosmartindent autoindent
