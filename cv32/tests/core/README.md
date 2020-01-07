Testcases for CV32E Core Testbench
==================================
This is the root directory for assembler and C testcases for CV32E.  Currently
these include the 
[riscv-tests](https://github.com/riscv/riscv-tests/tree/master/isa)(rv32ui,
rv32uc) and
[riscv-compliance-tests](https://github.com/riscv/riscv-compliance)(rv32i).

The testbench for the CV32E Core is at ../../tb/core.  It contains a RAM model
and a small pseudo peripheral that dumps any writes to `0x1000_0000` to stdout.
The small tests signal success or failure by writing `12345679` or `1` respectively
to `0x2000_0000`.

To run the testcases you will need a SystemVerilog simulator and RISC-V GCC compiler.

Supported SystemVerilog Simulators
----------------------------------
At the time of this writting (2019-12-14) only **_Verilator_**, the Metrics
**_dsim_** and Cadence **_Xcelium_** simulators are known to work.  Support for other
SystemVerilog simulators such as Synopsys **_vcs_** and Mentor **_Questa_** is contingent
on community interest and support.

Supported C Compilers
----------------------
Compiling the riscv-tests and riscv-compliance-tests requires either the upstream
[riscv-gcc](https://github.com/riscv/riscv-gcc) or if you want to use the custom
PULP instructions the PULP
[riscv-gcc](https://github.com/pulp-platform/pulp-riscv-gcc) (recommended to be
installed through our [sdk](https://github.com/pulp-platform/pulp-sdk)).
For compiling C programs you need gcc with RISC-V support and a fitting newlib installed.
It is strongly recommended you use the [RISC-V GNU
Toolchain](https://github.com/riscv/riscv-gnu-toolchain) for that (follow the
`Installation (Newlib)` section) and point your `RISCV` environment variable to
it.

Running your own C programs
---------------------
A hello world program is available and you can run it in the testbench. Invoke the
`dsim-hello_world` or `custom-veri-run` makefile rules to run it with `dsim` or
`verilator` respectively.

The hello world program is located in the `custom` folder. The relevant sections
in the Makefile on how to compile and link this program can be found under `Running
custom programs`.  Make sure you have a working C compiler (see above) and keep in
mind that you are running on a very basic machine.

Running your own Assembler programs
---------------------
Admittedly, this needs work.  Check out the Makefile for `+firmware=path_to_firmware`
to load a specific firmware. It is a bit tricky to build and link your own program.
Have a look at `picorv_firmware/start.S` and `picorv_firmware/link.ld` for more insight.
This will be cleaned up in the future.

Running the testbench with [verilator](https://www.veripool.org/wiki/verilator)
----------------------
Point your environment variable `RISCV` to your RISC-V toolchain. Call `make
firmware-veri-run` or just `make` to build the testbench and the firmware, and
run it. Use `VERI_FLAGS` to configure verilator e.g. `make firmware-veri-run
VERI_FLAGS="+firmware=path_to_firmware"`.  You can clean up the mess you made
with `make veri-clean` (yes, it is amusing to say that).

Running the testbench with Metrics [dsim](https://metrics.ca)
----------------------
Point your environment variable `RISCV` to your RISC-V toolchain. Call
`make dsim-hello_world` to build and run the testbench with the hello_world
test in the custom directory. Other rules of interest:
* `make dsim-cv32_riscv_tests` to build and run the testbench with all the testcases in the riscv_tests directory.
* `make dsim-cv32_riscv_compliance_tests` to build and run the tests in riscv_compliance_tests.
* `make dsim-firmware` to build and run the testbench with all the testcases in the riscv_tests and riscv_compliance_tests directories.
* You can clean up the mess you made with `make dsim-clean`.

Running the testbench with Cadence Xcelium [xrun](https://www.cadence.com/en_US/home/tools/system-design-and-verification/simulation-and-testbench-verification/xcelium-parallel-simulator.html)
----------------------
**Note:** This testbench is known to require Xcelium 19.09 or later.  See [Issue 11](https://github.com/openhwgroup/core-v-verif/issues/11) for more info.
Point your environment variable `RISCV` to your RISC-V toolchain. Call
`make xrun-hello_world` to build and run the testbench with the hello_world
test in the custom directory. Other rules of interest:
* `make xrun-firmware` to build and run the testbench with all the testcases in the riscv_tests/ and riscv_compliance_tests/ directories.
* Clean up your mess: `make xsim-clean` (deletes xsim intermediate files) and `xrun-clean-all` (deletes xsim intermedaites and all testcase object files).

Running the testbench with vsim (not currently supported)
---------------------------------------------------------
Point your environment variable `RISCV` to your RISC-V toolchain. Call `make
firmware-vsim-run` to build the testbench and the firmware, and run it. Use
`VSIM_FLAGS` to configure the simulator e.g. `make firmware-vsim-run
VSIM_FLAGS="-gui -debugdb"`.

Running the testbench with vcs (not currently supported)
----------------------
Point your environment variable `RISCV` to your RISC-V toolchain.
Call `make firmware-vcs-run` to build the testbench and the firmware, and run it.
Use `SIMV_FLAGS` or `VCS_FLAGS` to configure the simulator and build respectively e.g.
`make firmware-vcs-run VCS_FLAGS+="-cm line+cond+fsm+tgl+branch" SIMV_FLAGS+="-cm line+cond+fsm+tgl+branch"`

Options (out of date)
----------------------
A few plusarg options are supported.
* `+verbose` to show all memory read and writes and other miscellaneous information.

* `+vcd` to produce a vcd file called `riscy_tb.vcd`. Verilator always produces
  a vcd file called `verilator_tb.vcd`.

Examples
--------
Run all riscv_tests to completion with **dsim**, writting compile and simulation results in /data/$USER/results:  
`make dsim-cv32_riscv_tests DSIM_RESULTS=/data/$USER`  

