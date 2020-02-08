CV32 Core Testcases
===================
This is the root directory for assembler and C testcases for CV32E40P.  These
tests were originally developed for the `core` testbench located at `../../tb/core`,
but can also be executed by the `cv32_uvmt` verification environment.
<br>
Currently these include the 
[riscv-tests](https://github.com/riscv/riscv-tests/tree/master/isa)(rv32ui,
rv32uc) and
[riscv-compliance-tests](https://github.com/riscv/riscv-compliance)(rv32i).

Running the Testcases
---------------------
Althought there is a Makefile at this location, simulations should be run in
the **_sim_** directory (cv32/sim/core).  The Makefile located here will be
removed in the coming weeks and is not currently supported.
