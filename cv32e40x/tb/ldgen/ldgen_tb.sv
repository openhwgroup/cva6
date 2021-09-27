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
