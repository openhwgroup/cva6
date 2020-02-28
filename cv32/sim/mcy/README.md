Directory for MCY coverage reporting
==================================

This is an example setup for using Mutation Cover with Yosys (MCY).
The module targeted for mutation testing is `riscv_alu_div`. There are two tests
performed on the mutated module: `test_sim` runs the verilator testbench on the
whole core, with the mutated module substituted in the ALU. `test_eq` checks if
the mutation introduces a relevant behavioral modification using a bounded model
check on a miter circuit comparing the original and mutated module.

Current Status / Issues / Points of relevance:
----------------------------------

- The verilator testbench currently contains some failing tests as well as a
fatal error. This should be fixed, but right now `test_sim` just suppresses the
return value and checks for the magic number of errors.
- A timeout facility needs to be added to either the testbench or `test_sim.sh`
because it seems that a mutation can occasionally create a deadlock.
- A large amount of the runtime is currently spent re-compiling the verilator
testbench with each mutated module. This can be spared by surfacing the `mutsel`
input as a command line argument to the testbench.
- The current tagging logic always runs all tests. If unit tests are available,
it could be cleverer.
- A separate MCY project will have to be set up for each module/mutation unit,
so subdirectories should be introduced.
