Directory for MCY coverage reporting
==================================

This is an example setup for using Mutation Cover with Yosys (MCY).
The module targeted for mutation testing is `riscv_alu_div`. There are two tests
performed on the mutated module: `test_sim` runs the verilator testbench on the
whole core, with the mutated module substituted in the ALU. `test_eq` checks if
the mutation introduces a relevant behavioral modification using a bounded model
check on a miter circuit comparing the original and mutated module.

This assumes that the SEDA suite and the pulp-riscv-gcc can be found in the path.
Set it e.g. as follows:

  export PATH=/opt/symbiotic/bin:/opt/riscv/bin:$PATH

Current Status / Issues / Points of relevance:
----------------------------------

- The verilator testbench currently contains some failing tests as well as a
fatal error if the standard riscv-gcc is used (instead of the pulp-riscv-gcc).
This should be fixed, but right now `test_sim` just suppresses the return value
and checks for the magic number of errors.
- A timeout facility was added to `test_sim.sh` because mutations can cause
deadlock (e.g. illegal instruction loop).
- `test_sim` now runs a modified version of the verilator testbench that can
test multiple mutations with a single compiled binary using a command line
argument.
- `test_sim` will also run a reduced firmware first and only run the full
firmware if the first test passes.
- Verilator does not support arbitrary expressions in events yet
(https://github.com/verilator/verilator/issues/2184), so mutations that affect
the clock or reset signal lead to compilation errors. As a workaround,
`opt_rmdff` was added to the mutation script in `test_sim.sh`.
