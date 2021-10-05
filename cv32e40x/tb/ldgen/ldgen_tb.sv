// Copyright 2021 OpenHW Group
// Copyright 2021 Silicon Labs, Inc.
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     https://solderpad.org/licenses/
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

`include "cv32e40x_pkg.sv"

import cv32e40x_pkg::pma_region_t;

`include "uvmt_cv32e40x_constants.sv"
`include "pma_adapted_mem_region_gen.sv"
`include "cv32e40x_ldgen.sv"

module ldgen_tb;

  initial begin : ldgen_start
    cv32e40x_ldgen_c linker_generator;
    linker_generator = new();
    linker_generator.gen_pma_linker_scripts();
  end

endmodule : ldgen_tb
