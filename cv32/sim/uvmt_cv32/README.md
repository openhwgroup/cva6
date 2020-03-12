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

Running the envrionment with Metrics [dsim](https://metrics.ca)
----------------------
Point your environment variable `RISCV` to your RISC-V toolchain. The Makefile rule to run a testcase
with dsim is `make dsim`.  You can pass the name of the testcase using the `TEST` variable:
* **make dsim-no-firmware UVM_TESTNAME=uvmt_cv32_smoke_test**:compile, run, come of out reset and die.
* **make dsim-hello_world**: run the hello_world program found at `../../tests/core/custom`.
* **make dsim-cv32_riscv_tests**: run the CV32-specific RISC-V tests found at `../../tests/core/cv32_riscv_tests_firmware`
* **make dsim-cv32_riscv_compilance_tests**: run the CV32-specific RISC-V tests found at `../../tests/core/cv32_riscv_compliance_tests_firmware`
* **make dsim-firmware**: run all the programs found at `../../tests/core/firmware`.
* **make dsim-riscv_tests**: run the RISC-V tests found at `../../tests/core/riscv_tests`
* **make dsim-riscv_compilance_tests**: run the RISC-V tests found at `../../tests/core/riscv_compliance_tests`
* **make dsim-unit-test <prog>**: Run one <prog> from the firmware suite of tests.  For example: `make dsim-unit-test addi`

Running the environment with Cadence Xcelium [xrun](https://www.cadence.com/en_US/home/tools/system-design-and-verification/simulation-and-testbench-verification/xcelium-parallel-simulator.html)
----------------------
**Note**: this has not yet been fully tested<br>
**Note:** This testbench is known to require Xcelium 19.09 or later.  See [Issue 11](https://github.com/openhwgroup/core-v-verif/issues/11) for more info.
Point your environment variable `RISCV` to your RISC-V toolchain. 
* To clean up your mess: `make xsim-clean` (deletes xsim intermediate files) and `xrun-clean-all` (deletes xsim intermedaites and all testcase object files).


