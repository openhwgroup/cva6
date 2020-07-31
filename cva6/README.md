# CVA6: Verification Environment for the CVA6 CORE-V processor core

To execute tests on CVA6 core, run one of the shell scripts:

- `source cva6/dv-riscv-compliance.sh`: [riscv-compliance](https://github.com/riscv/riscv-compliance) test suite,
- `source cva6/dv-riscv-tests.sh`: [riscv-tests](https://github.com/riscv/riscv-tests) test suite,

These tests are using [riscv-dv](https://github.com/ThalesGroup/riscv-dv)
as environment (forked from https://github.com/google/riscv-dv).

To run the scripts, the `RISCV` environment variable has to be set
with your toolchain installation path.

Tests are built with gcc 10 toolchain.
To build and install it, use scripts located at
https://github.com/ThalesGroup/cva6-tools

As the built gcc toolchain is independent from XLEN values,
the `RISCV_PREFIX` environment variable has to be set to `riscv-none-elf-`.

Other environment variables can be set to overload default values
provided in the different scripts.

The default values are:

- `VERILATOR_ROOT`: `../tools/verilator-4.014` to install in core-v-verif/tools
- `SPIKE_ROOT`: `../tools/spike` to install in core-v-verif/tools

- `CVA6_REPO`: `https://github.com/ThalesGroup/cva6.git`
- `CVA6_BRANCH`: `master-verif`
- `CVA6_HASH`: `5bee8d3836f9b2f8f2a083a3d24369ac86dfd255`
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
- `DV_HASH`: `7593c32194c349e5ba617da02abefbf9fcc3edb5`
- `DV_PATCH`: no default value

- `DV_TARGET`: `rv64gc`
- `DV_SIMULATORS`: `verilator,spike`
- `DV_TESTLISTS`: `../../tests/testlist_riscv-tests-$DV_TARGET-p.yaml ../../tests/testlist_riscv-tests-$DV_TARGET-v.yaml`
- `DV_OPTS`: no default value
- `RISCV_GCC`: `$RISCV/bin/riscv-none-elf-gcc`
- `RISCV_OBJCOPY`: `$RISCV/bin/riscv-none-elf-objcopy`

## 32-bit configuration
The following environment variables have to be modified.

- `CVA6_PATCH`: `../cva6/cva6-32bit.patch`
- `DV_TARGET`: `rv32ima` as C, F, D extensions are not yet supported

