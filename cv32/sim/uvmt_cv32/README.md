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
(free to OpenHW Group Contributors),
- a SystemVerilog simulator,
- the UVM-1.2 library,
- the RISC-V GCC compiler, and
- at least some familiarity with [Make](https://www.gnu.org/software/make/manual/) and Makefiles.

Imperas OVPsim Instruction Set Simulator
----------------------------------------
This UVM verification environment uses the Imperas OVPsim Instruction Set Simulator
(ISS) as a reference model.   The run-time license for this ISS is free to OpenHW
Group Contributors.  Please contact @MikeOpenHWGroup to be added as a Contributor and
go to the [Imperas website](http://www.imperas.com/) for installation instructions.

SystemVerilog Simulators
----------------------------------
Any SystemVerilog simulator that implements complete support for [IEEE-1800-2017](https://ieeexplore.ieee.org/document/8299595)
will be able to compile and run this verification environment. At the time of this writting
(2020-02-08) the Metrics **_dsim_**, Cadence **_Xcelium_**, Mentor's **_Questa_**  and Synopsys **_VCS_** simulators are supported by the Makefiles. 
If you have access to other SystemVerilog simulators such as Aldec **_RivieraPRO_** or some other simulator
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
from the Pulp Platform team.  See [TOOLCHAIN](https://github.com/openhwgroup/core-v-verif/blob/master/cv32/sim/TOOLCHAIN.md)
for detailed installation instructions.
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
              +--- vcs.mk                   # Synopsys VCS
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
Setting a shell environment variable `CV_SIMULATOR` to "dsim" will also define the
Makefile variable SIMULATOR to `dsim` and you can save yourself a lot of typing. For
example, in a bash shell:
<br>**export CV_SIMULATOR=dsim**
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
using _xrun_.  Set the shell variable SIMULATOR to `xrun` to simply run **`make <target>`**.
<br><br>
**Note for Cadence users:** This testbench is known to require Xcelium 19.09 or
later.  See [Issue 11](https://github.com/openhwgroup/core-v-verif/issues/11)
for more info.

Running the environment with Mentor Graphics [Questa](https://www.mentor.com/products/fv/questa/) (vsim)
----------------------
The command **make SIMULATOR=vsim sanity** will run the sanity testcase using _vsim_.
Set the shell variable SIMULATOR to `vsim` to simply run **`make <target>`**.

Running the environment with Synopsys VCS [VCS](https://www.synopsys.com/verification/simulation/vcs.html) (vcs)
----------------------
The command **make SIMULATOR=vcs sanity** will run the sanity testcase using _vsim_.
Set the shell variable SIMULATOR to `vcs` to simply run **`make <target>`**.
<br><br>
**Note for Synopsys users:** This testbench has not been compiled/run
with _vcs_ in several weeks.  If you need to update the Makefiles, please do
so and issue a Pull Request.

Common Makefile Flags
---------------
For all tests in the <i>uvmt_cv32</i> directory the following flags and targets are supported for common operations with the simulators.  For all flags and targets described in this section it is assumed that the user will supply a SIMULATOR setting on the make command line or populate the CV_SIMULATOR environment variable.

Current supported simulators: <i>Note that eventually all simulators will be supported</i>

| SIMULATOR | Supported |
|-----------|-----------|
|dsim       | Yes       |
|xrun       | Yes       |
|questa     | Yes       |
|vcs        | Yes       |

For certain simulators multiple debug tools are available that enable advanced debug capabilities but generally require respective licenses from the vendor.  By default all debug-related commands in this section will support a standard debug tool with the simulator.   However support is provided for advanced debug tools when avaiable.  The advanced debug tool is selected with each make command by setting the **ADV_DEBUG=YES** flag.

| SIMULATOR | Standard Debug Tool | Advanced Debug Tool |
|-----------|---------------------|---------------------|
| dsim      | N/A                 | N/A                 |
| xrun      | SimVision           | Indago              |
| questa    | Questa Tk GUI       | Visualizer          |
| vcs       | DVE                 | Verdi               |

### Interactive Simulation

To run a simulation in interactive mode (to enable single-stepping, breakpoints, restarting), use the GUI=1 command when running a test.  

If applicable for a simulator, line debugging will be enabled in the compile to enable single-stepping.

**make test TEST=hello-world GUI=1**

### Set the UVM quit count

All error signaling and handling is routed through the standard UVM report server for all OpenHW testbenches.  By default the UVM is configured 
to allow up to 5 errors to be signaled before aborting the test.  There is a run-time plusarg to configure this that should work for all
tests.  Use the USER_RUN_FLAGS make variable with the standard UVM_MAX_QUIT_COUNT plusarg as below.  Please note that the NO is required
and signals that you want UVM to use your plusarg over any internally configured quit count values.

**make test TEST=hello-world USER_RUN_FLAGS=+UVM_MAX_QUIT_COUNT=10,NO**

### Post-process Waveform Debug

There are flags and targets defined to support generating waveforms during simulation and viewing those waveforms in a post-process debug tool specific to the respective simulator used.<br>

To create waves during simulation, set the **WAVES=YES** flag.<br>

The waveform dump will include all signals in the <i>uvmt_tb32</i> testbench and recursively throughout the hierarchy.

**make test TEST=hello-world WAVES=1**

If applicable for a simulator, dumping waves for an advanced debug tool is available.

**make hello-world WAVES=1 ADV_DEBUG=1**

To invoke the debug tool itself use the **make waves** target.  Note that the test must be provided.  Additionally the advanced debug tool flag must match the setting used during waveform generation.

Invoke debug tool on hello-world test using the standard debug tool.

**make waves TEST=hello-world**

Invoke debug tool on hello-world test using the advanced debug tool.

**make waves TEST=hello-world ADV_DEBUG=1**

### Coverage

The makefile supports the generation of coverage databases during simulation and invoking simulator-specific coverage reporting and browsing tools.

By default coverage information is not generated during a simulation for <i>xrun, questa, and vcs.</i>  Therefore a flag was added to the makefiles to enable generation of a coverage database during simulation.  The coverage database will include line, expression, toggle, functional and assertion coverage in the generated database.

To generate coverage database, set **COV=1**.

**make test TEST=hello-world COV=1**

To view coverage results a new target **cov** was added to the makefiles.  By default the target will generate a coverage report in the same directory as the output log files and the coverage database.<br>

The user can invoke the GUI coverage browsing tool specific to the simulator by setting **GUI=1** on the **make cov** command line.

Generate coverage report for the hello-world test

**make cov TEST=hello-world**

Invoke GUI coverage browser for the hello-world test:

**make cov TEST=hello-world GUI=1**

An additional option to the **make cov** target exists to <i>merge</i> coverage.  To merge coverage the makefiles will look in **all** existing test results directories <i>for the selected simulator</i> and generate a merged coverage report in <i>&lt;simulator>_results/merged_cov</i>.  The respective coverage report of GUI invocation will use that directory as the coverage database.  Coverage merging is selected by setting the <i>MERGE=1</i> flag.

Generate coverage report for all executed tests with coverage databases.

**make cov MERGE=1**

Invoke GUI coverage browser for all executed tests with coverage databases.

**make cov MERGE=1 GUI=1**

Available Tests
---------------
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
* **make test TEST=hello-world**:<br>run the hello_world program found at `../../tests/core/custom`.
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

Build Configurations
--------------------
The `uvmt_cv32` environment supports adding compile flags to the testbench to support a specialized configuration of the core.  The testbench
flow supports a single compilation object at any point in time so it is recommended that any testbench options be supported as run-time
options (see the Test Specification documentation for setting run-time plusargs).  However if, for instance, parameters to the DUT need to be
changed then this flow needs to be used.<br>

All build configurations are in the files:<br>

```
cv32/tests/cfg/<cfg>.yaml
```

The contents of the YAML file support the following tags:
| YAML Tag      | Required | Description |
|---------------|----------|---------------------|
| name          | Yes      | The name of the configuration                |
| description   | Yes      | Brief description of the intent of the build configuration |
| compile_flags | No       | Compile flags passed to the simulator compile-step    |
| ovpsim        | No       | Flags for the IC file for the OVPSim ISS   |

<br>
The following is an example build configuration:<br>

```
name: no_pulp
description: Sets all PULP-related flags to 0
compile_flags: >
    +define+NO_PULP
    +define+HAHAHA
ovpsim: >
    --override root/cpu0/misa_Extensions=0x1104
    --showoverrides
```