# CVA6: Verification Environment for the CVA6 CORE-V processor core

- [Prerequisites](#prerequisites)
- [Test execution](#test-execution)
- [Environment variables](#environment-variables)
- [32-bit configuration](#32-bit-configuration)

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

- `source cva6/dv-riscv-compliance.sh`:
[riscv-compliance](https://github.com/riscv/riscv-compliance) test suite,
- `source cva6/dv-riscv-tests.sh`:
[riscv-tests](https://github.com/riscv/riscv-tests) test suite.

These tests are using [riscv-dv](https://github.com/ThalesGroup/riscv-dv)
as environment (forked from https://github.com/google/riscv-dv).

## Environment variables
Other environment variables can be set to overload default values
provided in the different scripts.

The default values are:

- `RISCV_GCC`: `$RISCV/bin/riscv-none-elf-gcc`
- `RISCV_OBJCOPY`: `$RISCV/bin/riscv-none-elf-objcopy`
- `VERILATOR_ROOT`: `../tools/verilator-4.014` to install in core-v-verif/tools
- `SPIKE_ROOT`: `../tools/spike` to install in core-v-verif/tools

- `CVA6_REPO`: `https://github.com/ThalesGroup/cva6.git`
- `CVA6_BRANCH`: `master-verif`
- `CVA6_HASH`: `22f718c0f25e1abaae46aafe4b1760ff0be903d0`
- `CVA6_PATCH`: no default value
- `COMPLIANCE_REPO`: `https://github.com/riscv/riscv-compliance.git`
- `COMPLIANCE_BRANCH`: `master`
- `COMPLIANCE_HASH`: `220e78542da4510e40eac31e31fdd4e77cdae437`
- `COMPLIANCE_PATCH`: no default value
- `TESTS_REPO`: `https://github.com/riscv/riscv-tests.git`
- `TESTS_BRANCH`: `master`
- `TESTS_HASH`: `f92842f91644092960ac7946a61ec2895e543cec`
- `DV_REPO`: `https://github.com/ThalesGroup/riscv-dv.git`
- `DV_BRANCH`: `oss`
- `DV_HASH`: `8ff0a5ecb56269cfff94b59c9f7f4e267630ef20`
- `DV_PATCH`: no default value
- `DV_TARGET`: `rv64gc`
- `DV_SIMULATORS`: `verilator,spike`
- `DV_TESTLISTS`: `../../cva6/tests/testlist_riscv-tests-$DV_TARGET-p.yaml
../../cva6/tests/testlist_riscv-tests-$DV_TARGET-v.yaml`
- `DV_OPTS`: no default value

## 32-bit configuration
To test the CVA6 in 32-bit configuration, `XLEN` has to be set to 32
instead to 64. This can be done by patching the `riscv_pk.sv` file.
Additionally, the architecture used for building the tests has to be
modified.

The following environment variables have to be modified before executing
test script.

- `CVA6_PATCH`: `../cva6/cva6-32bit.patch`
- `DV_TARGET`: `rv32ima` as C, F, D extensions are not yet supported

