[![Build Status](https://travis-ci.org/pulp-platform/ariane.svg?branch=master)](https://travis-ci.org/pulp-platform/ariane)

# Ariane RISC-V CPU

Ariane is a 6-stage, single issue, in-order CPU which implements the 64-bit RISC-V instruction set. It fully implements I, M and C extensions as specified in Volume I: User-Level ISA V 2.1 as well as the draft privilege extension 1.10. It implements three privilege levels M, S, U to fully support a Unix-like operating system. Furthermore it is compliant to the draft external debug spec 0.13.

It has configurable size, separate TLBs, a hardware PTW and branch-prediction (branch target buffer and branch history table). The primary design goal was on reducing critical path length.

![](docs/img/ariane_overview.png)

## Getting Started


Go and get the [RISC-V tools](https://github.com/riscv/riscv-tools). Make sure that your `RISCV` environment variable points to your RISC-V installation (see the RISC-V tools and related projects for futher information).

Checkout the repository and initialize all submodules
```
$ git clone https://github.com/pulp-platform/ariane.git
$ git submodule update --init --recursive
```

The testbench relies on `riscv-fesvr` which can be found [here](https://github.com/riscv/riscv-fesvr). Follow the README there and make sure that your compiler and linker is aware of the library (e.g.: add it to your path if it is in a non-default directory).

Build the Verilator model of Ariane by using the Makefile:
```
$ make verilate
```
To build the verilator model with support for vcd files run
```
$ make verilate DEBUG=1
```

This will create a C++ model of the core including a SystemVerilog wrapper and link it against a C++ testbench (in the `tb` subfolder). The binary can be found in the `work-ver` and accepts a RISC-V ELF binary as an argument, e.g.:

```
$ work-ver/Variane_testharness rv64um-v-divuw
```

The Verilator testbench makes use of the `riscv-fesvr`. This means that you can use the `riscv-tests` repository as well as `riscv-pk` out-of-the-box. As a general rule of thumb the Verilator model will behave like Spike (exception for being orders of magnitudes slower).

Both, the Verilator model as well as the Questa simulation will produce trace logs. The Verilator trace is more basic but you can feed the log to `spike-dasm` to resolve instructions to mnemonics. Unfortunately value inspection is currently not possible for the Verilator trace file.

```
$ spike-dasm < trace_core_00_0.dasm > logfile.txt
```

### Running Applications

It is possible to run user-space binaries on Ariane with `riscv-pk` ([link](https://github.com/riscv/riscv-pk)). As Ariane currently does not support atomics and floating point extensions make sure that you configure `riscv-pk` with:
`--with-arch=rv64imc`. In particular inside the `riscv-pk` directory do:

```
$ mkdir build
$ cd build
$ ../configure --prefix=$RISCV --host=riscv64-unknown-elf --with-arch=rv64imc
$ make
$ make install
```

Then to run a RISC-V ELF using the Verilator model do:

```
$ make verilate
$ work-ver/Variane_testharness /path/to/pk path/to/riscv.elf
```

If you want to use QuestaSim to run it you can use the following command:
```
$ make simc riscv-test=/path/to/pk target-options=path/to/riscv.elf
```

> Be patient! RTL simulation is way slower than Spike. If you think that you ran into problems you can inspect the trace files.

## FPGA Emulation

Coming.

## Planned Improvements

While developing Ariane it has become evident that, in order to support Linux, the atomic extension is going to be mandatory. While the core is currently booting Linux by emulating Atomics in BBL (in a single core environment this is trivially met by disabling interrupts) this is not the behavior which is intended. For that reason we are going to fully support all atomic extensions in the very near future.

## Going Beyond

The core has been developed with a full licensed version of QuestaSim. If you happen to have this simulator available yourself here is how you could run the core with it.

To specify the test to run use (e.g.: you want to run `rv64ui-p-sraw` inside the `tmp/risc-tests/build/isa` folder:
```
$ make sim riscv-test=tmp/risc-tests/build/isa/rv64ui-p-sraw
```

If you call `simc` instead of `sim` it will run without the GUI. QuestaSim uses `riscv-fesvr` for communication as well.

### CI Testsuites and Randomized Constrained Testing with Torture

We provide two CI configuration files for Travis CI and GitLab CI that run the RISCV assembly tests, the RISCV benchmarks and a randomized RISCV Torture test. The difference between the two is that Travis CI runs these tests only on Verilator, whereas GitLab CI runs the same tests on QuestaSim and Verilator. 

If you would like to run the CI test suites locally on your machine, follow any of the two scripts `ci.travis-ci-emul.sh` and `ci.travis-ci-emul.sh` (depending on whether you have QuestaSim or not). In particular, you have to get the required packages for your system, the paths in `ci/path-setup.sh` to match your setup, and run the installation and build scripts prior to running any of the tests suites. 

Once everything is set up and installed, you can run the tests suites as follows (using Verilator):

```
$ make verilate 
$ make run-asm-tests-verilator  
$ make run-benchmarks-verilator 
```

In order to run randomized Torture tests, you first have to generate the randomized program prior to running the simulation:

```
$ make torture-gen
$ make torture-rtest-verilator

```
This runs the randomized program on Spike and on the RTL target, and checks whether the two signatures match. The random instruction mix can be configured in the `./tmp/riscv-torture/config/default.config` file. 


# Contributing

Check out the [contribution guide](CONTRIBUTING.md)

