## Toolchain Installation Instructions

The following are instructions for obtaining and installing a toolchain on your system.
Please refer to the [README](./README.md) in this directory for instructions on setting up the core-v-verif to use your Toolchain.
[Toolchain Parameters Example](#toolchain-parameters-example), below, provides an explainer on how to select from multiple toolchain parameters on a per-test-program basis.

### CORE-V Toolchain
The recommended toolchain for all CORE-V cores is available from Embecosm
[here](https://www.embecosm.com/resources/tool-chain-downloads/#corev).
It is recommended that you install this at `/opt/corev`.
As detailed in [README](./README.md#required-corev-environment-variables), you will need to define a shell variable to point to it:
```
$ export CV_SW_TOOLCHAIN="/opt/riscv"
```

### RISC-V Toolchain
For many CORE-V cores, the standard RISC-V toolchain will work. You can obtain pre-built version for various platforms from Embecosm
[here](https://www.embecosm.com/resources/tool-chain-downloads/#riscv).
It is recommended that you install this at `/opt/riscv` and define a shell variable to point to it:
```
$ export CV_SW_TOOLCHAIN="/opt/riscv"
```

### LLVM Toolchain
The core-v-verif testbench also supports usage of an LLVM/Clang toolchain.
An LLVM toolchain with RISCV32 support built for various Linux binary platforms is available [here](https://www.embecosm.com/resources/tool-chain-downloads/#riscv-stable).

All tests and regressions for the CV32E40X and CV32E40S should be buildable and runnable with LLVM/Clang.

To use LLVM it is recommended that you install it at `/opt/llvm` and define a shell variable to point to it:
```
$ export CV_SW_TOOLCHAIN="/opt/llvm"
```

#### Known caveats with LLVM
* When using a non-standard extension, the test should set the cflag `-menable-experimental-extensions`
* The clang integrated assembler cannot properly convert conditional branches to jump sequences when the branch distance is too large
(i.e. beyond +-2KB).  Set the cflag `-fno-integrated-as` to use a GNU system assembler with this ability.

### PULP Toolchain
If you are using the PULP instruction extensions, you will need access to the PULP toolchain.  **Note** that this toolchain is
out-of-date and cannot compile all test-programs for the CV32E40P, so it is recommended to use the COREV toolchain by
default and the PULP toolchain as needed.  The see the comment header in `Common.mk` (in this directory) to
see how to set this up.

#### Pre-built PULP Toolchain
The PULP toolchain for CV32E40P is available [here](https://www.embecosm.com/resources/tool-chain-downloads/#pulp).
It is recommended that you install this at /opt/pulp.

#### Building the PULP Toolchain from source
What follows is a set of commands that can be used to install the Toolchain from the PULP-Platform team.
If you use these commands verbatim you should not encounter any issues.  If you do, please open an issue and assign it to @MikeOpenHWGroup.
<br><br>
The process takes about two hours
<br><br>
Please note that the OpenHW Group expects to update the recommended Toolchain in the near future.
```
# Create directory for the toolchain
$ sudo mkdir /opt/pulp
# Create shell ENV variables to point to it (put this in .bashrc)
$ PATH="/opt/pulp/bin:$PATH"
$ export PULP="YES"
# Get prerequists
$ sudo apt-get update
$ sudo apt-get install autoconf automake autotools-dev curl libmpc-dev \
               libmpfr-dev libgmp-dev gawk build-essential bison flex texinfo gperf \
               libtool patchutils bc zlib1g-dev
# Clone the toolchain repo (assumes you are placing the cloned code in
# ~GitHubRepos/pulp-platform/pulp-riscv-gnu-toolchain/master).
$ cd ~GitHubRepos/pulp-platform/pulp-riscv-gnu-toolchain
$ git clone --recursive \
            https://github.com/pulp-platform/pulp-riscv-gnu-toolchain \
            master
$ cd master
# Build the toolchain
$ ./configure --prefix=/opt/pulp  --with-arch=rv32imc \
              --with-cmodel=medlow --enable-multilib
$ sudo make
# Wait about 2 hours (seriously, it takes that long)
```

## Test-Program Definitions

Events such as generating a test-program, compiling the test-program
and compiling/simulating the SystemVerilog testbench are all controlled by
a the set of environment variables described in the [README](./README.md), plus
a set of YAML files collectively known as the _test-program definitions_.

The YAML files allow for fine-grained control of the
[required](./README.md#required-corev-environment-variables) and
[optional](./README.md#optional-corev-environment-variables) CORE-V-VERIF environment variables,
plus a host of other variables such as SystemVerilog "plusargs".
Each test-program will have its own test-program defintion, _test.yaml_,
which resides in the same directory as the test-program sources,
plus a configuration-level test-program defintion that resides in `tests/cfg`.
If a configuration-level test-program defintion is not specfied then _default.yaml_ is used.

The following describes how this works in core-v-verif.

In core-v-verif each test-program has its own directory and the test-program defintion, _test.yaml_ is required to exist in that directory.
This test-program defintion contains variables used by the software toolchain and SystemVerilog simulator.
For an example see:
`$(CORE_V_VERIF)/$(CORE_V_CORE)/tests/programs/custom/hello-world/test.yaml`


The test-program defintion can overload the defintion of the CV_SW_TOOLCHAIN and CV_SW_PREXFIX, if required.
For example:
```
cv_sw_toolchain: /opt/llvm
cv_sw_prefix: riscv-openhw-elf-
```

Similarily, each pseudo-random (corev-dv) test-program is required to have two YAML files:
1. _corev-dv.yaml_ is the test-program defintion for the corev-dv instruction generator.
2. _test.yaml_ is the test-program defintion for the toolchain and SystemVerilog simulator. This test.yaml serves the same function as for manually written test-programs.

For examples see:
`$(CORE_V_VERIF)/$(CORE_V_CORE)/tests/programs/corev-dv/corev_rand_arithmetic_base_test/corev-dv.yaml` and 
`$(CORE_V_VERIF)/$(CORE_V_CORE)/tests/programs/corev-dv/corev_rand_arithmetic_base_test/test.yaml`.

The script [YAML2MAKE](../bin/yaml2make) will parse test.yaml and create a set of Makefile variables that are used by the Makefile to:
* Compile the test-program.
* Compile UVM environment.
* Pass run-time arguments to the SystemVerilog simulator.
These variables all have a "TEST\_" prefix.

Similarily, [YAML2MAKE](../bin/yaml2make) also parses corev-dv.yaml and create a set of
variables that are used by the corev-dv to pass run-time arguments to the
SystemVerilog simulator, typically as plusargs to control how corev-dv
generates the pseudo-random test-program. These variables all have a "GEN\_"
prefix. NOTE: defining toolchain parameters in corev-dv is not required
as the Makefile does not use variables prefixed with "GEN\_" to access or control the toolchain.

Lastly, if the "CFG" variable is set, [CFGYAML2MAKE](../bin/cfgyaml2make) parses a specific YAML file in `$(CORE_V_VERIF)/$(CORE_V_CORE)/tests/cfg`.
The variables generated by this script all have a "CFG\_" prefix.
The "CFG" variable must be set to the filename (no extension) of a yaml file in the cfg directory.
Note that "CFG" can be a shell environment variable or passed to "make" on the comand line:
     make test TEST=my_test_program CFG=my_cfg

Note: if "CFG" is not defined, then `$(CORE_V_VERIF)/$(CORE_V_CORE)/tests/cfg/default.yaml` is used.

The common Makefile, ([Common.mk](./Common.mk)), will launch the yaml2make and cfgyaml2make scripts to generate the TEST\*, GEN\* and CFG\* variables.
These are then used to set the appropriate parameters for generating the test-program, compiling the test-program, compiling and simulating the SystemVerilog testbench.

### Toolchain Parameter Example

Let's take, as an example, setting of the `march` argument for gcc.
This is determined by the value of CV_SW_MARCH.
This could be determined by defining a shell environment variable CV_SW_MARCH, as discussed at the top of this document.
If the test-program definition and default configuration definitions do not define this variable, then the value of `march` used is determined by the shell variable.
However, if _either_ the test-program definition or default configuration definition set this variable, that will override the environment variable.
Suppose the default configuration test-program defintion,`$(CORE_V_VERIF)/$(CORE_V_CORE)/tests/cfg/default.yaml`, contains the following line:
```
cv_sw_march: rv32imc_zba1p00_zbb1p00_zbc1p00_zbs1p00
```
This would set CV_SW_MARCH for all tests that use cfg/default.yaml.
The priority order for controlling variables is ENV > TEST > CFG.

### Non-defaults

Recall that the toolchain selection variables, CV_SW_TOOLCHAIN and CV_SW_PREFIX are not optional.
These shell environment variables must be set, or the Makefiles will fatal-out and terminate execution immediately.
Due to the priority ordering of toolchain selection variables discussed above,
this means that the value of CV_SW_TOOLCHAIN and CV_SW_PREFIX cannot be set in either the test-program definition or the default configuration definition.
