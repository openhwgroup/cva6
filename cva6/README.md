# CVA6: Verification Environment for the CVA6 CORE-V processor core

- [Directories](#directories)
- [Prerequisites](#prerequisites)
- [Test execution](#test-execution)
- [Environment variables](#environment-variables)
- [32-bit configuration](#32-bit-configuration)

## Directories:
- **bsp**:   board support package for test-programs compiled/assembled/linked for the CVA6.
This BSP is used by both `core` testbench and `uvmt_cva6` UVM verification environment.
- **regress**: scripts to install tools, test suites, CVA6 code and to execute tests
- **sim**:   simulation environment (e.g. riscv-dv)
- **tb**:    testbench module instancing the core
- **tests**: source of test cases and test lists

There are README files in each directory with additional information.

## Prerequisites
To execute tests on CVA6 core, you need a RISC-V toolchain.

For instance, you can use the gcc 10 toolchain.
To build and install it, use scripts located at
https://github.com/ThalesGroup/cva6-tools

Once the toolchain is installed, set the `RISCV` environment variable
to your toolchain installation path e.g. `RISCV = /path/to/gcc-10.2`
to run the test scripts.

## Test execution
Run one of the shell scripts:

- `source cva6/regress/dv-riscv-compliance.sh`:
[riscv-compliance](https://github.com/riscv/riscv-compliance) test suite,
- `source cva6/regress/dv-riscv-tests.sh`:
[riscv-tests](https://github.com/riscv/riscv-tests) test suite.

These tests are using [riscv-dv](https://github.com/google/riscv-dv)
as environment.

## Environment variables
Other environment variables can be set to overload default values
provided in the different scripts.

The default values are:

- `RISCV_GCC`: `$RISCV/bin/riscv-none-elf-gcc`
- `RISCV_OBJCOPY`: `$RISCV/bin/riscv-none-elf-objcopy`
- `VERILATOR_ROOT`: `../tools/verilator-4.110` to install in core-v-verif/tools
- `SPIKE_ROOT`: `../tools/spike` to install in core-v-verif/tools

- `CVA6_REPO`: `https://github.com/openhwgroup/cva6.git`
- `CVA6_BRANCH`: `master`
- `CVA6_HASH`: see value in `regress/install-cva6.sh`
- `CVA6_PATCH`: no default value
- `COMPLIANCE_REPO`: `https://github.com/riscv/riscv-compliance.git`
- `COMPLIANCE_BRANCH`: `master`
- `COMPLIANCE_HASH`: `220e78542da4510e40eac31e31fdd4e77cdae437`
- `COMPLIANCE_PATCH`: no default value
- `TESTS_REPO`: `https://github.com/riscv/riscv-tests.git`
- `TESTS_BRANCH`: `master`
- `TESTS_HASH`: `f92842f91644092960ac7946a61ec2895e543cec`
- `DV_REPO`: `https://github.com/google/riscv-dv.git`
- `DV_BRANCH`: `master`
- `DV_HASH`: `0ce85d3187689855cd2b3b9e3fae21ca32de2248`
- `DV_PATCH`: no default value
- `DV_TARGET`: `cv64a6_imafdc_sv39`
- `DV_SIMULATORS`: `veri-core,spike`
- `DV_TESTLISTS`: `../tests/testlist_riscv-tests-$DV_TARGET-p.yaml
../tests/testlist_riscv-tests-$DV_TARGET-v.yaml`
- `DV_OPTS`: no default value

## 32-bit configuration
To test the CVA6 in 32-bit configuration, use `DV_TARGET` with
a 32-bit variant (e.g. `cv32a6_imac_sv0`).

The following environment variables have to be modified before executing
test script.

- `DV_TARGET`: `cv32a6_imac_sv0`
