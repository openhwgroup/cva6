Simulation Directory for CV32E UVM Verification Environment
==================================
This is the directory in which you should run all tests of the UVM environment.
The UVM testcases are at `../../tests/uvmt_cv32`, and the test-programs can be
found in `cv32/tests/core`.  See the README in those directories for more information.
<br><br>
Please refer to the [Verification Strategy](https://core-v-docs-verif-strat.readthedocs.io/en/latest/sim_tests.html#simulation-tests-in-the-uvm-environments)
for a discussion on the distinction between a _testcase_ and a _test-program_ in this environment.
<br><br>
To run the UVM environment you will need:
- a run-time license for the Imperas OVPsim Instruction Set Simulator
(free to OpenHW Group members),
- a SystemVerilog simulator,
- the UVM-1.2 library,
- the RISC-V GCC compiler, and
- at least some familiarity with [Make](https://www.gnu.org/software/make/manual/) and Makefiles.

Imperas OVPsim Instruction Set Simulator
----------------------------------------
This UVM verification environment uses the Imperas OVPsim Instruction Set Simulator
(ISS) as a reference model.   The run-time license for this ISS is free to OpenHW
Group members.  Go to the [Imperas website](http://www.imperas.com/) for installation instructions.

SystemVerilog Simulators
----------------------------------
Any SystemVerilog simulator that implements complete support for [IEEE-1800-2017](https://ieeexplore.ieee.org/document/8299595)
will be able to compile and run this verification environment. At the time of this writting
(2020-02-08) the Metrics **_dsim_**, Cadence **_Xcelium_** and Mentor's **_Questa_** simulators are supported by the Makefiles. 
If you have access to other SystemVerilog simulators such as Synopsys **_VCS_**, Aldec **_RivieraPRO_** or some other simulator
not listed here and would like to add support to the Makefile, your pull-request will be graciously accepted!

UVM-1.2 Libraries
-------------
The UVM environments in core-v-verif require the use of version 1.2 of the UVM library (1.1 will not suffice). Typically,
the UVM library comes with the distribution of your SystemVerilog simulator.  Point your shell environment
variable `UVM_HOME` to your simulator's UVM library. For example Metrics dsim users will have something
like this:<br>`export UVM_HOME=/tools/Metrics/dsim/20191112.8.0/uvm-1.2`.
<br><br>
Alternately, you can download the source code from
[Accellera](https://www.accellera.org/downloads/standards/uvm).  The UVM LRM (IEEE-1800.2) can be obtained
from the [IEEE Standards Association](https://standards.ieee.org/).

RISC-V GCC Compilers
--------------------
Compiling the riscv-tests and riscv-compliance-tests requires a cross-compiler,
often refered to as the "toolchain".  It is recommended that you use the
[PULP RISCV GNU Toolchain](https://github.com/pulp-platform/pulp-riscv-gnu-toolchain)
from the Pulp Platform team.
<br><br>
Some teams use the [riscv-gcc](https://github.com/riscv/riscv-gcc) toolchain, but this
does not support the custom PULP instructions.
<br><br>
**IMPORTANT:** Once the toolchain is set up, define a shell environment
variable `RISCV` to the path of your RISC-V toolchain (e.g. `export RISCV=/opt/riscv`).

Makefiles
-----------
`Make` is used to generate the command-lines that compile and run simulations.
The cwd of this README is `cv32/sim/uvmt_cv32` and the **Makefile** at this location is the
'root' Makefile.  `../Common.mk` supports all common variables, rules
and targets, including specific targets to clone the RTL from
[cv32e40p](https://github.com/openhwgroup/cv32e40p) and
[fpnew](https://github.com/pulp-platform/fpnew) as appropriate. Simulator-specific
Makefiles are used to build the command-line to run a specific test with a specific
simulator.  These files are organized as shown below:
```
cv32/sim/
      +--- Common.mk                        # Common variables and targets
      +--- uvmt_cv32/
              +--- Makefile                 # 'Root' Makefile
              +--- vsim.mk                  # Mentor Questa
              +--- dsim.mk                  # Metrics dsim
              +--- xrun.mk                  # Cadance Xcelium
              +--- <other_simulators>.mk
```
The goal of this structure is to minimize the amount of redundant code in the
Makefiles and ease the maintance of a given simulator's specific variables,
rules and targets.
<br><br>
The basic usage is: `make SIMULATOR=<sim> <target>` where `sim` is vsim, dsim
or xrun and `target` selects a specific testcase or other rule (e.g. "clean").
<br><br>
**Hint**: define shell ENV variable "SIMULATOR" to match one of the supported
simulator-specific Makefiles (e.g. vsim) to save yourself a lot of typing.
<br><br>
To run your own test-program use the `custom` target.  For example `make custom CUSTOM_PROG=illegal`
will run illegal.c from the cv32/tests/core/custom directory.

Running the envrionment with Metrics [dsim](https://metrics.ca)
----------------------
The command **make SIMULATOR=dsim sanity** will run the sanity testcase using _dsim_.
<br><br>
Setting a shell environment variable `SIMULATOR` to "dsim" will also define the
Makefile variable SIMULATOR to `dsim` and you can save yourself a lot of typing. For
example, in a bash shell:
<br>**export SIMULATOR=dsim**
<br>**make sanity**
<br><br>
The Makefile for dsim also supports variables to control wave dumping.  For example:
<br>**make sanity WAVES=1**
<br>Have a look at `dsim.mk` to see additional variables to control the filename
of the dumpfile, etc.
<br><br>
The Makefile variable DSIM_RUN_FLAGS can be used to pass user define arguments
to dsim at run-time.  For example:
<br>**make sanity DSIM\_RUN\_FLAGS=+print\_uvm\_runflow\_banner=1**

Running the environment with Cadence [Xcelium](https://www.cadence.com/en_US/home/tools/system-design-and-verification/simulation-and-testbench-verification/xcelium-parallel-simulator.html) (xrun)
----------------------
The command **make SIMULATOR=xrun sanity** will run the sanity testcase
using _xrun_.  Set the shell variable SIMULATOR to `xrun` to simply that to **make <target>**.
<br><br>
**Note for Cadence users:** This testbench is known to require Xcelium 19.09 or
later.  See [Issue 11](https://github.com/openhwgroup/core-v-verif/issues/11)
for more info.

Running the environment with Mentor Graphics [Questa](https://www.mentor.com/products/fv/questa/) (vsim)
----------------------
The command **make SIMULATOR=vsim sanity** will run the sanity testcase using _vsim_.
Set the shell variable SIMULATOR to `vsim` to simply that to **make <target>**.

SANITY
-------
The `make` commands here assume you have set your shell SIMULATION
environment variable to your specific simulator (see above).
<br><br>
Before making changes to the code in your local branch, it is a good idea to run the sanity
test to ensure you are starting from a stable code-base.  The code (both RTL
and verification) should _always_ pass sanity, so if it does not, please
raise an issue and assign it to @mikeopenhwgroup.  The definition of "sanity"
will change over time as the ability of the verification environment to
stress the RTL improves.  Running sanity is trivial:
<br><br>
**make sanity**
<br><br>
Before issuing a pull-request for either the RTL or verification code, please
re-run the sanity test.   Your pull-request will be rejected if sanity does not
compile and run successfully.   For extra points, go to the `ci` directory at the
top of this repository and run `ci_check`.

Available Test Programs
-----------------------
The `make` commands here assume you have set your shell SIMULATION
There are three targets that can run a specific test-program by name:
* **make hello-world**:<br>run the hello_world program found at `../../tests/core/custom`.
* **make cv32-riscv-tests**:<br>run the CV32-specific RISC-V tests found at `../../tests/core/cv32_riscv_tests_firmware`
* **make cv32-riscv-compilance-tests**:<br>run the CV32-specific RISC-V tests found at `../../tests/core/cv32_riscv_compliance_tests_firmware`
Some targets are simulator specific:
* **make make dsim-unit-test <prog>**:<br>run one <prog> from the firmware suite
of tests.  For example: `make SIMULATOR=dsim dsim-unit-test addi`.
<br><br>
There are also a few targets that do something other than run a test:
* **make clean\_all**:<br>deletes all SIMULATOR generated intermediates, waves and logs **plus** the cloned RTL code.

Custom Test Programs
--------------------
The `uvmt_cv32` environment supports the ability to run any arbitrary test program that can run on the cv32e40p core, as long as it has
been pre-compiled into a hex-file.  These are called `Type 1` tests in the
[Verification Strategy](https://core-v-docs-verif-strat.readthedocs.io/en/latest/sim_tests.html#test-program).
<br><br>
The Makefile implements a rule called `custom` that will compile a test-program and pass it to the SystemVerilog simulation.  The user
must specify `CUSTOM_DIR`, the _absolute_ path to the compiled program, and `CUSTOM_PROG`, the filename of the test program (no extension).
For example:<br>
```
make custom CUSTOM_DIR=/your-abs-path-to-core-v-verif/cv32/tests/uvmt_cv32/test-programs CUSTOM_PROJ=hello_world
```
This could be a lot of typing, so its useful to pre-define the path as a shell environment variable:
<br>
`export CUSTOM_DIR=/your-abs-path-to-core-v-verif/cv32/tests/uvmt_cv32/test-programs`
<br>
You can now run any test program in that directory:<br>
```
make custom CUSTOM_PROJ=hello_world
make custom CUSTOM_PROJ=smoke
```
