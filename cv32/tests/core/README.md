Testcase for RI5CY Core Testbench
=================================
The tb/core testbench runs
[riscv-tests](https://github.com/riscv/riscv-tests/tree/master/isa)(rv32ui,
rv32uc) and
[riscv-compliance-tests](https://github.com/riscv/riscv-compliance)(rv32i) on
RI5CY in a minimalistic setting. It contains a RAM model and a small pseudo
peripheral that dumps any writes to `0x1000_0000` to stdout. The small tests
signal success or failure by writing `12345679` or `1` respectively to
`0x2000_0000`. At the time, only `dsim` were tested as simulators.

Supported C Compilers
----------------------
Note that this testbench requires either the upstream
[riscv-gcc](https://github.com/riscv/riscv-gcc) or if you want to use our custom
PULP instructions our PULP
[riscv-gcc](https://github.com/pulp-platform/pulp-riscv-gcc) (recommended to be
installed through our [sdk](https://github.com/pulp-platform/pulp-sdk)).

Running your own programs
---------------------
The `custom` folder has an example on a hello world program that can be run with
the testbench. The relevant sections in the Makefile on how to compile and link
this program can be found under `Running custom programs`. In order to compile
it successfully you need gcc with RISC-V support and a fitting newlib installed.
It is strongly recommended you use the [RISC-V GNU
Toolchain](https://github.com/riscv/riscv-gnu-toolchain) for that (follow the
`Installation (Newlib)` section) and point your `RISCV` environment variable to
it.

We have prepared a hello world program which you can run in the testbench. It
demonstrates how you can run your own programs. Call `custom-vsim-run` or
`custom-veri-run` to run it with `vsim` or `verilator` respectively.

Supported SystemVerilog Simulators
----------------------------------
At the time of this writting (2019-12-02) only The Metrics **_dsim_** and Cadence
**_Xcelium_** simulators are known to work.  Near future plans include
support for Synopsys **_vcs_**.  Support for other SystemVerilog simulators
is contingent on community interest and support.

Running the testbench with Metrics [dsim](https://metrics.ca)
----------------------
Point you environment variable `RISCV` to your RISC-V toolchain. Call
`make dsim-hello_world` to build and run the testbench with the hello_world
test in the custom directory. Other rules of interest:
* `make dsim-cv32_riscv_tests` to build and run the testbench with all the testcases in the riscv_tests directory.
* TODO: `make dsim-cv32_riscv_compliance_tests` to build and run the tests in riscv_compliance_tests.
* `make dsim-firmware` to build and run the testbench with all the testcases in the riscv_tests and riscv_compliance_tests directories.
* You can clean up the mess you made with `make dsim-clean`.

Running the testbench with Cadence Xcelium [xrun](https://www.cadence.com/en_US/home/tools/system-design-and-verification/simulation-and-testbench-verification/xcelium-parallel-simulator.html)
----------------------
Point you environment variable `RISCV` to your RISC-V toolchain. Call
`make xrun-hello_world` to build and run the testbench with the hello_world
test in the custom directory. Other rules of interest:
* `make xrun-firmware` to build and run the testbench with all the testcases in the riscv_tests/ and riscv_compliance_tests/ directories.
* You can clean up the mess you made with `make xsim-clean` (deletes xsim intermediate files) and `xrun-clean-all` (deletes xsim intermedaites and all testcase object files).

Running the testbench with vsim (not currently supported)
---------------------------------------------------------
Point you environment variable `RISCV` to your RISC-V toolchain. Call `make
firmware-vsim-run` to build the testbench and the firmware, and run it. Use
`VSIM_FLAGS` to configure the simulator e.g. `make firmware-vsim-run
VSIM_FLAGS="-gui -debugdb"`.

Running the testbench with vcs (not currently supported)
----------------------
Point you environment variable `RISCV` to your RISC-V toolchain.
Call `make firmware-vcs-run` to build the testbench and the firmware, and run it.
Use `SIMV_FLAGS` or `VCS_FLAGS` to configure the simulator and build respectively e.g.
`make firmware-vcs-run VCS_FLAGS+="-cm line+cond+fsm+tgl+branch" SIMV_FLAGS+="-cm line+cond+fsm+tgl+branch"`

Running the testbench with [verilator](https://www.veripool.org/wiki/verilator) (not currently supported)
----------------------
Point you environment variable `RISCV` to your RISC-V toolchain. Call `make
firmware-veri-run` or just `make` to build the testbench and the firmware, and
run it. Use `VERI_FLAGS` to configure verilator e.g. `make firmware-veri-run
VERI_FLAGS="+firmware=path_to_firmware"`.

Options (out of date)
----------------------
A few plusarg options are supported.
* `+verbose` to show all memory read and writes and other miscellaneous information.

* `+vcd` to produce a vcd file called `riscy_tb.vcd`. Verilator always produces
  a vcd file called `verilator_tb.vcd`.

* `+firmware=path_to_firmware` to load a specific firmware. It is a bit tricky to
build and link your own program. Have a look at `picorv_firmware/start.S` and
`picorv_firmware/link.ld` for more insight.

Examples (out of date)
-----------------------
Run all riscv-tests to completion and produce a vcd dump:
`make firmware-vsim-run VSIM_FLAGS=+vcd`
