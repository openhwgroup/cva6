Simulation Directory for CV32E UVM Verification Environment
==================================
This is the directory in which you should run all tests of the UVM environment.
The testbench for the environment is located at `../../tb/uvmt_cv32` and the
testcases are at `../../tests/uvmt_cv32` (note that some of these testcases use test programs found in
`cv32/tests/core`).  See the README in those directories for more information.
<br><br>
To run the testcases you will need a SystemVerilog simulator, the UVM-1.2 library and RISC-V GCC compiler.

SystemVerilog Simulators
----------------------------------
Any SystemVerilog simulator that implements complete support for [IEEE-1800-2017](https://ieeexplore.ieee.org/document/8299595)
will be able to compile and run this verification environment. At the time of this writting
(2020-02-08) the Metrics **_dsim_**, Cadence **_Xcelium_** and Mentor's **_Questa_** simulators are supported by the Makefile. 
If you have access to other SystemVerilog simulators such as Synopsys **_VCS_**, Aldec **_RivieraPRO_** or some other simulator
not listed here and would like to add support to the Makefile, your pull-request will be graciously accepted!

UVM-1.2 Libraries
-------------
The UVM environments in core-v-verif require the use of version 1.2 of the UVM library (1.1 will not suffice). Typically,
the UVM library comes with the distribution of your SystemVerilog simulator.  Point your environment
variable `UVM_HOME` to your simulator's UVM library. For example Metrics dsim users will have something
like this:<br>`export UVM_HOME=/tools/Metrics/dsim/20191112.8.0/uvm-1.2`.
<br><br>
Alternately, you can download the source code from
[Accellera](https://www.accellera.org/downloads/standards/uvm).  The UVM LRM (IEEE-1800.2) can be obtained
from the [IEEE Standards Association](https://standards.ieee.org/).

RISC-V GCC Compilers
--------------------
Compiling the riscv-tests and riscv-compliance-tests requires either the upstream
[riscv-gcc](https://github.com/riscv/riscv-gcc) or if you want to use the custom
PULP instructions the PULP
[riscv-gcc](https://github.com/pulp-platform/pulp-riscv-gcc) (recommended to be
installed through our [sdk](https://github.com/pulp-platform/pulp-sdk)).
For compiling C programs you need gcc with RISC-V support and a fitting newlib installed.
It is strongly recommended you use the [RISC-V GNU
Toolchain](https://github.com/riscv/riscv-gnu-toolchain) for that (follow the
`Installation (Newlib)` section) and point your `RISCV` environment variable to it.

Makefiles
-----------
`Make` is used to generate the command-lines that compile and run simulations.
Your cwd is `cv32/sim/uvmt_cv32` and the **Makefile** at this location is the
'root' Makefile that supports all common and simulator-specific variables,
rules and targets used to build the command-line to run a specific test. These
files are organized as shown below:
```
cv32/sim/
      |
      +--- Common.mk
      |
      +--- uvmt_cv32/
              |
              +--- Makefile
              +--- vsim.mk
              +--- dsim.mk
              +--- xrun.mk
              +--- <other_simulators>.mk
```
The goal of this structure is to minimize the amount of redundant code in the
Makefiles and ease the maintance of a given simulator's specific variables,
rules and targets.<br><br>
The basic usage is: `make SIMULATOR=<sim> <target>` where typically a target
selects a specific testcase.

Running the envrionment with Metrics [dsim](https://metrics.ca)
----------------------
Point your environment variable `RISCV` to your RISC-V toolchain. The Makefile
Set make variable SIMULATION to `dsim`.  You can pass the name of the testcase using the `TEST` variable:
* **make SIMULATOR=dsim no-firmware UVM_TESTNAME=uvmt_cv32_\<testname\>**: run uvmt_cv32_\<testname\> without loading any firmware.
* **make SIMULATOR=dsim hello-world**: run the hello_world program found at `../../tests/core/custom`.
* **make SIMULATOR=dsim cv32_riscv_tests**: run the CV32-specific RISC-V tests found at `../../tests/core/cv32_riscv_tests_firmware`
* **make SIMULATOR=dsim cv32_riscv_compilance_tests**: run the CV32-specific RISC-V tests found at `../../tests/core/cv32_riscv_compliance_tests_firmware`
* **make SIMULATOR=dsim firmware**: run all the programs found at `../../tests/core/firmware`.
* **make SIMULATOR=dsim dsim-riscv_tests**: run the RISC-V tests found at `../../tests/core/riscv_tests`
* **make SIMULATOR=dsim riscv_compilance_tests**: run the RISC-V tests found at `../../tests/core/riscv_compliance_tests`
* **make SIMULATOR=dsim dsim-unit-test \<prog\>**: Run one <prog> from the firmware suite of tests.  For example: `make dsim-unit-test addi`

Running the environment with Cadence [Xcelium](https://www.cadence.com/en_US/home/tools/system-design-and-verification/simulation-and-testbench-verification/xcelium-parallel-simulator.html)(xrun) or Mentor Graphics [Questa](https://www.mentor.com/products/fv/questa/)(vsim)
----------------------
**Note:** This testbench is known to require Xcelium 19.09 or later.  See [Issue 11](https://github.com/openhwgroup/core-v-verif/issues/11) for more info.
Point your environment variable `RISCV` to your RISC-V toolchain.<br>
The command-lines **make SIMULATOR=xrun hello-world** or<br>**make SIMULATOR=vsim hello-world**<br>do what you'd expect.
