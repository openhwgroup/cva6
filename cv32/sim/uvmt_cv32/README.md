Simulation Directory for CV32E UVM Verification Environment
==================================
This is the directory in which you should run all tests of the UVM environment.
The testbench for the environment is located at `../../tb/uvmt_cv32` and the
testcases are at `../../tests/uvmt_cv32`.  See the README in those directories
for more information.
<br><br>
To run the testcases you will need a SystemVerilog simulator, the UVM library and RISC-V GCC compiler.

Supported SystemVerilog Simulators
----------------------------------
At the time of this writting (2020-02-08) the Metrics
**_dsim_** and Cadence **_Xcelium_** simulator are supported by the Makefile.  Support for other
SystemVerilog simulators such as Synopsys **_vcs_** and Mentor **_Questa_** is contingent
on community interest and support.  Verilator is not supported.

UVM Libraries
-------------
Typically, these come with the distribution of a SystemVerilog simulator.  If they do not, you
can download the source code from [Accellera](https://www.accellera.org/downloads/standards/uvm).
The UVM LRM (IEEE-1800.2) can be obtained from the [IEEE Standards Association](https://standards.ieee.org/).

Supported RISC-V GCC Compilers
-------------------------------
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

Running the envrionment with Metrics [dsim](https://metrics.ca)
----------------------
Point your environment variable `RISCV` to your RISC-V toolchain. The Makefile rule to run a testcase
with dsim is `make dsim`.  You can pass the name of the testcase using the `TEST` variable:
<br> `make dsim TEST=uvmt_cv32_smoke_test`

Running the environment with Cadence Xcelium [xrun](https://www.cadence.com/en_US/home/tools/system-design-and-verification/simulation-and-testbench-verification/xcelium-parallel-simulator.html)
----------------------
**Note**: this has not yet been fully tested<br>
**Note:** This testbench is known to require Xcelium 19.09 or later.  See [Issue 11](https://github.com/openhwgroup/core-v-verif/issues/11) for more info.
Point your environment variable `RISCV` to your RISC-V toolchain. 
* To clean up your mess: `make xsim-clean` (deletes xsim intermediate files) and `xrun-clean-all` (deletes xsim intermedaites and all testcase object files).


