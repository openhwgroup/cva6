// Copyright 2020 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Author: Florian Zaruba <zarubaf@iis.ee.ethz.ch>
//
/// Contains common ECC definitions and helper functions.

package ecc_pkg;

  // Calculate required ECC parity width:
  function automatic int unsigned get_parity_width (input int unsigned data_width);
    // data_width + cw_width + 1 <= 2**cw_width
    int unsigned cw_width = 2;
    while (unsigned'(2**cw_width) < cw_width + data_width + 1) cw_width++;
    return cw_width;
  endfunction

  // Calculate required ECC codeword width:
  function automatic int unsigned get_cw_width (input int unsigned data_width);
    // data width + parity width + one additional parity bit (for double error detection)
    return data_width + get_parity_width(data_width);
  endfunction

endpackage
