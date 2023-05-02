Common Makefile for the CORE-V-VERIF UVM Verification Environment
==================================
This directory contains the _Common_ makefiles for the UVM and Core testbenches to perform common functionality: <br>
- Cloning third party repositories (Core RTL, libraries, ISGs, RISC-V compliance library, etc.)
- Invoking the toolchain to compile directed and/or random test programs into machine code for simulation
- Invoking the toolchain to compile compliance test programs for simulation
- Importing the source code in DVT Eclipse IDE (https://dvteclipse.com/)

In the core-v-verif UVM environment, the distinction between a **_testcases_** and **_test-program_** is important.
* **testcase**: a SystemVerilog class extended from uvm_test that instantiates and controls the UVM environment.
A testcase will control things like whether or not, and when, an interrupt is asserted and randomization of cycle timing on the external memory interfaces.
* **test-program**: a C or assembler program that is executed by the core RTL model.
<br><br>
There may be only one testcase, but typically there are many test-programs.
For more information please refer to the [Verification Strategy](https://core-v-docs-verif-strat.readthedocs.io/en/latest/intro.html)
<br><br>
The testcases are at located at `CV_CORE/tests/uvmt`.
Test-programs can be found in `CV_CORE/tests/program`.
See the README in those directories for more information.
<br><br>
To run the UVM environment you will need:
- a run-time license for the Imperas OVPsim Instruction Set Simulator
- a SystemVerilog simulator,
- the UVM-1.2 library,
- the RISC-V GCC compiler, and
- at least some familiarity with [Make](https://www.gnu.org/software/make/manual/) and Makefiles.

Required COREV Environment Variables
------------------------------------
The Makefile use a set of common shell environment variables to control individual simulations and/or regressions.
The following variables **must** be set for any `make` invocation to run tests in core-v-verif.
These can be set on the command line (e.g. `make CV_SIMULATOR=xrun`) or set in the user's shell environment.
Note that `CV_CORE` is infered by the Makefiles if you launch a test from a `uvmt` directory.

| Environment Variable | Description  |
|----------------------|--------------|
| CV_SIMULATOR         | The default simulator to use for all tools (dsim, vcs, xrun, vsim, riviera).  Can be overridden on any make invocation. |
| CV_CORE              | The core to simulate by default.  Can be overridden on any make command line. |
| CV_SW_TOOLCHAIN      | Points to SW toolchain installation for compiling, assembling, and/or linking test programs. |
| CV_SW_PREFIX         | Prefix of the SW toolchain installation. |

**Notes:**
1. A toolchain is required for running any tests in the core-v-verif environments, see below for more detail.
2. If CV_CORE is not set, running a simulation from the `<core>/sim/uvmt` directory will automatically set it to "core".

A toolchain is comprised of a set of executables (e.g. gcc, objcopy, etc.) each of which typically has a path of the form `$(CV_SW_TOOLCHAIN)/bin/$(CV_SW_PREFIX)`.
For example, if your toolchain executables are at `/opt/riscv/bin/riscv32-unknown-elf-`, then you would set `CV_SW_TOOLCHAIN` to **_/opt/riscv_** and `CV_SW_PREFIX` to **_riscv32-unknown-elf-_**.

Optional COREV Environment Variables
----------------------------------------
The Makefile use a set of common shell environment variables to control individual simulations and/or regressions.
The following environment variables may be set for any `make` invocation to run tests or set in the user's environment to customize setting.

| Environment Variable | Description  |
|----------------------|--------------|
| CV_SIM_PREFIX        | Prepended to all simulation compile and/or execution invocations.  Can be used to invoke job-scheduling tool (e.g. LSF). |
| CV_TOOL_PREFIX       | Prepended to all standalone tool (i.e. non-interacitive) simulation tool invocations such as coverage tools and waveform viewers.  Can be used to invoke job-scheduling tool (e.g. LSF). |
| CV_RESULTS           | Optional simulator output redirection path. Defaults to blank, i.e. simulation outputs will be located in <i>&lt;core></i>/mk/uvmt/<i>&lt;simulator></i>\_results if a relative path is given.  Optionally an absolute path can be used as well and simulation outputs will be located in  $(CV\_RESULTS)/<i>&lt;simulator></i>\_results |
| CV_SW_MARCH          | Architecture of tool chain to invoke. The default is `rv32imc`. |
| CV_SW_CFLAGS         | Optional command-line arguments (flags) passed to $(CV_SW_CC). |
| CV_SW_CC             | Postfix name of the C compiler used to compile the test-program. The default is `gcc`. If you are using an LLVM toolchain, this would typically be set to `cc`. |

Imperas Reference Models
------------------------
Many CORE-V cores verified in CORE-V-VERIF use a reference model from [Imperas](https://www.imperas.com/).
Earlier generations of CORE-V-VERIF used the **_OVPsim Instruction Set Simulator_**, and as of March, 2023 we have transitioned to **_ImperasDV_**.
To purchase a run-time license for ImperasDV, please contact Imperas at the link above.

To run CORE-V-VERIF without the reference model, set the `USE_ISS` make variable to "NO":
```
$ make test TEST=hello-world SIMULATOR=<your-simulator> USE_ISS=NO
```
The above works for all tests, but be aware that most test-programs in CORE-V-VERIF are not self-checking,
so without a running reference model, passing simulations are vacuous.

SystemVerilog Simulators
----------------------------------
Any SystemVerilog simulator that implements complete support for [IEEE-1800-2017](https://ieeexplore.ieee.org/document/8299595)
will be able to compile and run this verification environment. Metrics **_dsim_**, Cadence **_Xcelium_**, Mentor's **_Questa_**,
Aldec's **_Riviera-PRO_**  and Synopsys **_VCS_** simulators are supported by the Makefiles. If you have access to a SystemVerilog
simulator not listed here and would like to add support to the Makefiles, your pull-request will be graciously accepted!

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

Toolchains
----------
Compiling the test-programs requires a RISC-V cross-compiler, often refered to as the "toolchain".
See [TOOLCHAIN](./TOOLCHAIN.md) for detailed installation instructions.

Makefiles
-----------
`Make` is used to generate the command-lines that compile and run simulations.<br>
- `CV_CORE/sim/uvmt/Makefile` is the 'root' Makefile from which users can invoke simulations.
This Makefile is largely empty and include:
- `CV_CORE/sim/ExternalRepos.mk` should be used to define variables to point to third-party libraries.
This include the RTL repo to simulate; Google riscv-dv; RISCV compliance suite and other external repositories.
- `CORE-V-VERIF/mk/uvmt/uvmt.mk`, which implements simulation execution targets and:
- `CORE-V-VERIF/mk/Common.mk` supports all common variables, rules and targets, including specific targets to clone the RTL.
<br><br> 
Simulator-specific Makefiles are used to build the command-line to run a specific test with a specific
simulator.  These files are organized as shown below:
```
CORE-V-VERIF/
     |
     +--- mk/
     |     +--- Common.mk                       # Common variables and targets
     |     +--- uvmt/
     |            +--- uvmt.mk                  # Simulation makefile (includes ../Common.mk and simulator-specific mk)
     |            +--- vcs.mk                   # Synopsys VCS
     |            +--- vsim.mk                  # Mentor Questa
     |            +--- dsim.mk                  # Metrics dsim
     |            +--- xrun.mk                  # Cadance Xcelium
     |            +--- riviera.mk               # Aldec Riviera-PRO
     |            +--- <other_simulators>.mk
     +--- CV_CORE/
            +--- sim/
                   +--- ExternalRepos.mk         # URLs, hashes to external repos (RTL, riscv-dv, etc.)
                   +--- uvmt/
                          +--- Makefile          # "root" Makefile
                                                 # includes ../ExternalRepos.mk and CORE-V-VERIF/mk/uvmt/uvmt.mk
```
The goal of this structure is to minimize the amount of redundant code in the
Makefiles, maintain common look-and-feel across all cores and ease the maintance of a given simulator's specific variables,
rules and targets.
<br><br>
The basic usage is: `make SIMULATOR=<sim> <target>` where `sim` is vsim, dsim,
 xrun, vcs or riviera and `target` selects one or more activities (e.g. 'clean', 'test', 'gen_corev-dv')
<br><br>
**Hint**: define shell ENV variable "SIMULATOR" to match one of the supported
simulator-specific Makefiles (e.g. vsim) to save yourself a lot of typing.
<br><br>
The basic format to run a test is `make test SIMULATOR=<sim> TEST=<test-program>` where `test-program`
is the name of a [test-program](https://core-v-docs-verif-strat.readthedocs.io/en/latest/sim_tests.html#test-program)
(either C or RISC-V assembler) located in <CV_CORE>/tests/programs/custom/<testprogram>.

Importing the source code in DVT Eclipse IDE [dvt](https://www.dvteclipse.com/products/dvt-eclipse-ide)
----------------------
Alongside the simulator-specific Makefiles, there is also a makefile called `dvt.mk`.
The command `make SIMULATOR=<sim> open_in_dvt_ide` will import the core-v-verif testbench and RTL source code 
in the DVT Eclipse IDE.
<br> <br>
**Note:** `CV_CORE/sim/uvmt/Makefile` is the 'root' Makefile from which users can invoke DVT.
<br>

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
<br>

Running the environment with Mentor Graphics [Questa](https://www.mentor.com/products/fv/questa/) (vsim)
----------------------
The command **make SIMULATOR=vsim sanity** will run the sanity testcase using _vsim_.
Set the shell variable SIMULATOR to `vsim` to simply run **`make <target>`**.
<br> <br>
**Note for Mentor users:** This testbench is known to require Questa 2019.2 or later.
<br>

Running the environment with Synopsys VCS [VCS](https://www.synopsys.com/verification/simulation/vcs.html) (vcs)
----------------------
The command **make SIMULATOR=vcs sanity** will run the sanity testcase using _vsim_.
Set the shell variable SIMULATOR to `vcs` to simply run **`make <target>`**.
<br><br>
**Note for Synopsys users:** This testbench has not been compiled/run
with _vcs_ in several weeks.  If you need to update the Makefiles, please do
so and issue a Pull Request.

Running the environment with Aldec [Riviera-PRO](https://www.aldec.com/en/products/functional_verification/riviera-pro) (riviera)
----------------------
The command **make SIMULATOR=riviera sanity** will run the sanity testcase using _riviera_.
Set the shell variable SIMULATOR to `riviera` to simply run **`make <target>`**.

Sanity Tests
---------------
The `make` commands here assume you have set your shell SIMULATION
environment variable to your specific simulator (see above).
<br><br>
Before making changes to the code in your local branch, it is a good idea to run the sanity
test to ensure you are starting from a stable code-base.  The code (both RTL
and verification) should _always_ pass sanity, so if it does not, please
raise an issue and assign it to @mikeopenhwgroup.  The definition of "sanity"
may change over time as the ability of the verification environment to
stress the RTL improves.  Running sanity is trivial:
```
make sanity
```

CI Mini-regression
------------------
OpenHW uses the [Metrics CI platform]() for regressions.  The control script for this is `.metrics.json`
located at the top-level of this repository.  A pythin script `ci/ci_check` can be used to run the
"cv32 CI check regression" specified in the control script.  Before issuing a pull-request for either
the RTL or verification code, please run `ci_check`.  Your pull-request will be rejected if `ci_check`
does not compile and run successfully. Usage is simple:
```
./ci_check --core cv32e40p -s xrun
```
will run the CI sanity regression on the cv32e40p using Xcelium.
<br><br>
Complete user information is obtained in the usual way:
```
./ci_check -h
```

Available Test Programs
-----------------------
The `make` commands here assume you have set your shell SIMULATION
environment variable to your specific simulator (see above).
<br>
The general form to run a test is `make test TEST=<test-program>`, where _test-program_ is the filename
of a test-program (without the file extension) of a test program located at <CV_CORE>/tests/programs/custom.
Each test-program (either C or assembler) has its own directory, which contains the program itself (either
C or assembler) plus `test.yaml`, the test-program configuration file (see Build Configurations, below).
<br>
Here are a few examples
* **make test TEST=hello-world**:<br>run the hello_world program found at `<CV_CORE>/tests/programs/custom`.
* **make test TEST=dhrystone**:<br>run the dhrystone program found at `<CV_CORE>/tests/programs/custom`.
* **make test TEST=riscv_arithmetic_basic_test**:<br>run the riscv_arithmetic_basic_test program found at `<CV_CORE>/tests/programs/custom`.
<br>
There are also a few targets that do something other than run a test.  The most popular is:
```
**make clean_all**
```
which deletes all SIMULATOR generated intermediates, waves and logs **plus** the cloned RTL code.

### CoreMark

There is a port of the [CoreMark](https://www.eembc.org/coremark/)
benchmark runnable with the following make command.

* **make test TEST=coremark USE_ISS=NO**

This will run the benchmark and print out the results.
The numbers "Total ticks" and "Iterations" can be used to compute the CoreMak/MHz score with
the following equation `CoreMark/MHz = iterations / (totalticks / 1e6)`.

COREV-DV Generated Tests
---------------
The CV32 UVM environment uses the [Google riscv-dv](https://github.com/google/riscv-dv)
generator to automate the generation of test-programs.  The generator
is cloned by the Makefiles to `$(CV_CORE)/vendor_lib/google` as needed.  Specific
classes ar extended to create a `corev-dv` generator that is specific to this environment.
Note that riscv-dv is not modified, merely extended, allowing core-v-verif to stay
up-to-date with the latest release of riscv-dv.
<br><br>
Riscv-dv uses test templates such as "riscv_arithmetic_basic_test" and "riscv_rand_jump_test".
Corev-dv has a set of templates for corev-dv generated test-programs at `<CV_CORE>/tests/programs/corev-dv`.
Running these is a two-step process.  The first step is to clone riscv-dv and compile corev-dv:
```
make corev-dv
```
Note that the `corev-dv` target need only be run once.  The next step is to generate, compile
and run a test.  For example:
```
make gen_corev-dv test TEST=corev_rand_jump_stress_test
```

RISC-V Compliance Test-suite and Regressions
---------------
The CV32 UVM environment is able to run the [RISC-V compliance](https://github.com/riscv/riscv-compliance)
test-suite in step-and-compare mode with the ISS Reference Model, and can optionally dump and check a signature
file against a reference signature.  As with riscv-dv, the compliance test-suite
is cloned by the Makefiles to `$(CV_CORE)/vendor_lib/riscv` as needed.  The form of the target to run a single test-program
from the compliance test suite is as follows:
```
make compliance RISCV_ISA=<ISA> COMPLIANCE_PROG=<test-program>
```
To have the signature dumped and checked:
```
make compliance_check_sig RISCV_ISA=<ISA> COMPLIANCE_PROG=<test-program>
```
Note that running either of these targets will invoke the `all_compliance` target which clones riscv-compliance
and compiles all the test-programs.  Below is an example of running a specific test-program from the suite:
```
make compliance RISCV_ISA=rv32Zifencei COMPLIANCE_PROG=I-FENCE.I-01
```
**Note:** There is a dependancy between RISCV_ISA and COMPLIANCE_PROG.  For example, because the I-ADD-01 test-program is part of the rv32i testsuite this works:
```
make compliance RISCV_ISA=rv32i COMPLIANCE_PROG=I-ADD-01
```
But this does not:
```
make compliance RISCV_ISA=rv32imc COMPLIANCE_PROG=I-ADD-01
```
The `compliance_check_sig` target can be used in the same way as above to run the simulation plus perform a post-simulation
check of the signature file and the reference signature provided as part of the compliance test-suite.
<br><br>
Per-extension compliance regressions can be run using the `compliance_regression` target.   For example:
```
make compliance_regression RISCV_ISA=rv32imc
```
will run all compressed instruction tests in the compliance test-suite, diff the signature files and produce a summary report. Note that four of the test-programs
in the rv32i compliance suite are deliberately ignored.  See [issue #412](https://github.com/openhwgroup/core-v-verif/issues/412).
<br><br>
The _cv_regress_ utility can also be used to run the compliance regression tests found in the [cv32_compliance](https://github.com/openhwgroup/core-v-verif/blob/master/cv32e40p/regress/cv32_compliance.yaml) YAML regression
specification.  This is supported for Metrics JSON (--metrics), shell script (--sh), and Cadence Vmanager VSIF (--vsif) output formats.  Use the following example:
```
# Shell script output
% cv_regress --file=cv32e40p_compliance --sim=xrun --sh
% ./cv32e40p_compliance.sh
```

Build Configurations
--------------------
The `uvmt` environment supports adding compile flags to the testbench to support a specialized configuration of the core.  The testbench
flow supports a single compilation object at any point in time so it is recommended that any testbench options be supported as run-time
options (see the Test Specification documentation for setting run-time plusargs).  However if, for instance, parameters to the DUT need to be
changed then this flow needs to be used.<br>

All build configurations are in the files:<br>

```
<CV_CORE>/tests/cfg/<cfg>.yaml
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
To facilitate multiple simultaneous runs with different configurations, simulation databases and output files are located in the <i>&lt;simulator</i>_results/<i>&lt;CFG></i>-subdirectories, where CFG is the name of the current yaml configuration. If not overriden, the default configuration is chosen and the subdirectory named accordingly.

Common Makefile Flags
---------------
For all tests in the <i>uvmt</i> directory the following flags and targets are supported for common operations with the simulators.  For all flags and targets described in this section it is assumed that the user will supply a SIMULATOR setting on the make command line or populate the CV_SIMULATOR environment variable.

| SIMULATOR    | Supported |
|--------------|-----------|
|dsim          | Yes       |
|xrun          | Yes       |
|vsim(questa)  | Yes       |
|vcs           | Yes       |
|Riviera-PRO   | Yes       |

For certain simulators multiple debug tools are available that enable advanced debug capabilities but generally require respective licenses from the vendor.  By default all debug-related commands in this section will support a standard debug tool with the simulator.   However support is provided for advanced debug tools when avaiable.  The advanced debug tool is selected with each make command by setting the **ADV_DEBUG=YES** flag.

| SIMULATOR   | Standard Debug Tool | Advanced Debug Tool |
|-------------|---------------------|---------------------|
| dsim        | gtkwave             | N/A                 |
| xrun        | SimVision           | Indago              |
| questa      | Questa Tk GUI       | Visualizer          |
| vcs         | DVE                 | Verdi               |
| Riviera-PRO | Riviera-PRO         | Riviera-PRO         |

### Interactive Simulation

To run a simulation in interactive mode (to enable single-stepping, breakpoints, restarting), use the GUI=1 command when running a test.  

If applicable for a simulator, line debugging will be enabled in the compile to enable single-stepping.

**make test TEST=hello-world GUI=1**

### Passing run-time arguments to the simulator

The Makefiles support a user controllable variable **USER_RUN_FLAGS** which can be used to pass run-time arguments.  Two typical use-cases for this are provided below:

#### Set the UVM quit count

All error signaling and handling is routed through the standard UVM report server for all OpenHW testbenches.  By default the UVM is configured 
to allow up to 5 errors to be signaled before aborting the test.  There is a run-time plusarg to configure this that should work for all
tests.  Use the USER_RUN_FLAGS make variable with the standard UVM_MAX_QUIT_COUNT plusarg as below.  Please note that the NO is required
and signals that you want UVM to use your plusarg over any internally configured quit count values.

**make test TEST=hello-world USER_RUN_FLAGS=+UVM_MAX_QUIT_COUNT=10,NO**

#### UVM verbosity control

The following will increase the verbosity level to DEBUG.

**make test TEST=hello-world USER_RUN_FLAGS=+UVM_VERBOSITY=UVM_DEBUG**

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

An additional option to the **make cov** target exists to <i>merge</i> coverage.  To merge coverage the makefiles will look in **all** existing test results directories <i>for the selected simulator</i> and configuration, and generate a merged coverage report in <i>&lt;simulator>_results/&lt;cfg>/merged_cov</i>.  The respective coverage report of GUI invocation will use that directory as the coverage database.  Coverage merging is selected by setting the <i>MERGE=1</i> flag.

Generate coverage report for all executed tests with coverage databases.

**make cov MERGE=1**

Invoke GUI coverage browser for all executed tests with coverage databases.

**make cov MERGE=1 GUI=1**

