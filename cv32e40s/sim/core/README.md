Simulation Directory for CV32E Core Testbench
==================================
This is the directory in which you should run all tests of the Core Testbench.
The testbench itself is located at `../../tb/core` and the test-programs are at
`../../tests`.  See the README in those directories for more information.

To run the core testbench you will need a SystemVerilog simulator and RISC-V GCC compiler.

Supported SystemVerilog Simulators
----------------------------------
The core testbench and associated test-programs can be run using **_Verilator_**, the Metrics
**_dsim_**, Mentor's **_Questa_**, Cadence **_Xcelium_**, Synopsys **_vcs_** and Aldec **_Riviera-PRO_**
simulators. Note that **_Icarus_** verilog cannot compile the RTL and there are no plans
to support Icarus in the future.

RISC-V GCC Compiler "Toolchain"
-------------------------------
Pointers to the recommended toolchain for CV32E40S are in `../TOOLCHAIN`.

Running your own C programs
---------------------
A hello world program is available and you can run it in the CV32E Core testbench.
Invoke the `dsim-hello_world` or `hello-world-veri-run` makefile rules to run it with
`dsim` or `verilator` respectively.

The hello world program is located in the `custom` folder. The relevant sections
in the Makefile on how to compile and link this program can be found under `Running
custom programs`.  Make sure you have a working C compiler (see above) and keep in
mind that you are running on a very basic machine.

Running the testbench with [verilator](https://www.veripool.org/wiki/verilator)
----------------------
Point your environment variable `RISCV` to your RISC-V toolchain. Call `make`
to run the default test (hello_world).

Running your own Assembler programs
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Admittedly, this needs work. If you have a C or assembly program in `../../tests/core/custom`
then the following will work with Verilator:<br>
```
make custom CUSTOM_PROG=dhrystone
make custom CUSTOM_PROG=misalign
make custom CUSTOM_PROG=fibonacci
make custom CUSTOM_PROG=illegal
make custom CUSTOM_PROG=riscv_ebreak_test_0
```

Running the testbench with Metrics [dsim](https://metrics.ca)
----------------------
Point your environment variable `RISCV` to your RISC-V toolchain. Call
`make dsim-hello_world` to build and run the testbench with the hello_world
test in the custom directory. Other rules of interest:
* `make dsim-cv32_riscv_tests` to build and run the testbench with all the testcases in the riscv_tests directory.
* `make dsim-cv32_riscv_compliance_tests` to build and run the tests in riscv_compliance_tests.
* `make dsim-firmware` to build and run the testbench with all the testcases in the riscv_tests and riscv_compliance_tests directories.
<br><br>The Makefile now supports running individual assembler tests from either
the riscv_tests or riscv_compliance_tests directories. For example, to run the ADD IMMEDIATE test from riscv_tests:
* `make dsim-unit-test addi`
<br>To run I-LBU-01.S from the riscv_compliance_tests:
* `make dsim-unit-test I_LBU_01`
<br>You can clean up the mess you made with `make dsim-clean`.

Running the testbench with Cadence Xcelium [xrun](https://www.cadence.com/en_US/home/tools/system-design-and-verification/simulation-and-testbench-verification/xcelium-parallel-simulator.html)
----------------------
**Note:** This testbench is known to require Xcelium 19.09 or later.  See [Issue 11](https://github.com/openhwgroup/core-v-verif/issues/11) for more info.
Point your environment variable `RISCV` to your RISC-V toolchain. Call
`make xrun-hello_world` to build and run the testbench with the hello_world
test in the custom directory. Other rules of interest:
* `make xrun-firmware` to build and run the testbench with all the testcases in the riscv_tests/ and riscv_compliance_tests/ directories.
* Clean up your mess: `make xsim-clean` (deletes xsim intermediate files) and `xrun-clean-all` (deletes xsim intermedaites and all testcase object files).

Running the testbench with Questa (vsim)
---------------------------------------------------------
Point your environment variable `RISCV` to your RISC-V toolchain. Call `make
firmware-vsim-run` to build the testbench and the firmware, and run it. Use
`VSIM_FLAGS` to configure the simulator e.g. `make firmware-vsim-run
VSIM_FLAGS="-gui -debugdb"`.
<br>The Makefile also supports running individual assembler tests from either
the riscv_tests or riscv_compliance_tests directories using vsim. For example,
to run the ADD IMMEDIATE test from riscv_tests:
* `make questa-unit-test addi`
<br>To run I-LBU-01.S from the riscv_compliance_tests:
* `make questa-unit-test I_LBU_01`

Running the testbench with VCS (vcs)
----------------------
Point your environment variable `RISCV` to your RISC-V toolchain.
Call `make firmware-vcs-run` to build the testbench and the firmware, and run it.
Use `SIMV_FLAGS` or `VCS_FLAGS` to configure the simulator and build respectively e.g.
`make firmware-vcs-run VCS_FLAGS+="-cm line+cond+fsm+tgl+branch" SIMV_FLAGS+="-cm line+cond+fsm+tgl+branch"`

Running the testbench with Riviera-PRO (riviera)
----------------------
Point you environment variable `RISCV` to your RISC-V toolchain. Call `make
riviera-hello-world` to build the testbench and the firmware, and run it. Use
`ASIM_FLAGS` to configure the simulator e.g. `make custom-asim-run
ASIM_FLAGS="-gui"`.

Options
-------
A few plusarg options are supported:
* `+verbose` to show all memory read and writes and other miscellaneous information.

* `+vcd` to produce a vcd file called `riscy_tb.vcd`. Verilator always produces
  a vcd file called `verilator_tb.vcd`.

Examples
--------
Run all riscv_tests to completion with **dsim**:
`make dsim-cv32_riscv_tests`

