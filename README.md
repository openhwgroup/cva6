[![Build Status](https://travis-ci.org/pulp-platform/ariane.svg?branch=master)](https://travis-ci.org/pulp-platform/ariane)

# Ariane RISC-V CPU

![](docs/fig/ariane_overview.png)

## Getting Started

Go and get the [RISC-V tools](https://github.com/riscv/riscv-tools).

Checkout the repository and initialize all submodules
```
git checkout https://github.com/pulp-platform/ariane.git
git submodule update --init --recursive
```

Build the Verilator model of Ariane by using the Makefile:
```
make verilate
```

This will create a C++ model of the core including a SystemVerilog wrapper and link it against a C++ testbench (in the `tb` subfolder). The binary can be found in the `obj_dir` and accepts a RISC-v ELF binary as an argument, e.g.:

```
obj_dir/Variane_wrapped -p rv64um-v-divuw
```

The Verilator testbench makes use of the `riscv-fesvr`. That means that bare `riscv-tests` can be run on the simulator.

<!--
Start the simulation using Modelsim:
```
make sim
```
To specify the test to run use (e.g.: you want to run `rv64ui-p-sraw` inside the riscv-tests isa folder:
```
make sim riscv-test=rv64ui-p-sraw
```
If you call `simc` instead of `sim` it will run without the GUI.

Or start any of the unit tests by:
```
make dcache_arbiter
``` -->
<!-- ### Randomized Constrained Testing with Torture

Ariane's core testbench is fully compatible with the randomized constrained testing framework called Torture. To start testing Ariane all you need is to step into the `riscv-torture/` folder and issue:
```
make rgentest
```
Which will produce a single randomized program, runs it on Spike (see [Getting Started](#getting_started)) and on the RTL simulator (QuestaSim) by calling `ariane-run-torture`.

Torture's overnight tests work the same way, just call
```
make rnight
```

C (a.k.a. Verilator) tests are currently not supported. -->

# Contributing

Check out the [contribution guide](CONTRIBUTING.md)

