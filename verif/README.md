# CVA6: Verification Environment for the CVA6 CORE-V processor core

- [Directories](#directories)
- [Prerequisites](#prerequisites)
- [Test execution](#test-execution)
- [Verification plan](#verification-plan)
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

Be aware that only gcc 11.1.0 or newer are supported in core-v-verif repository.
To build and install riscv gcc compiler in local, you can use the following commands :

- `git clone https://github.com/riscv-collab/riscv-gnu-toolchain`
- `cd riscv-gnu-toolchain`
- `git clone https://github.com/gcc-mirror/gcc -b releases/gcc-13 gcc-13`
- ```./configure –prefix:/path/to/installation/directory --with-multilib-generator="rv32e-ilp32e--;rv32i-ilp32--;rv32im-ilp32--;rv32iac-ilp32--;rv32imac-ilp32--;rv32imafc-ilp32f--;rv32imafdc-ilp32d--;rv64i-lp64--;rv64ic-lp64--;rv64iac-lp64--;rv64imac-lp64--;rv64imafdc-lp64d--;rv64im-lp64--;" --with-gcc-src=`pwd`/gcc-13```
- `make –j32`

These commands will install the riscv gcc 13.1.0 compiler which is the latest version.
Once running the previous commands, your environment must be updated with :

- `export RISCV=/path/to/installation/directory`
- `export RISCV_PREFIX=/path/to/installation/directory/bin/riscv64-unknown-`
- `export RISCV_GCC=/path/to/installation/directory/bin/riscv64-unknown-gcc`
- `export CV_SW_PREFIX=riscv64-unknown-elf-`

This 4 variables will ensure you use correctly the new gcc compiler you have just installed.
You will now be able to run the test scripts.

## Test execution
Run one of the shell scripts:

- `source cva6/regress/dv-riscv-compliance.sh`:
[riscv-compliance](https://github.com/riscv/riscv-compliance) test suite,
- `source cva6/regress/dv-riscv-tests.sh`:
[riscv-tests](https://github.com/riscv/riscv-tests) test suite.

These tests are using [riscv-dv](https://github.com/google/riscv-dv)
as environment.

## Verification plan
Verification plan is available only for vcs tool and located in sim/cva6.hvp, it's used within a modifier to filter out only needed features. Example sim/modifier_embedded.hvp for embedded config.

To generate the coverage database user should run at least a test or regression with coverage enabled by setting:
- `export cov=1`

To view or edit verification plan use command:
- `cd sim`
- `verdi -cov -covdir vcs_results/default/vcs.d/simv.vdb -plan cva6.hvp -mod modifier_embedded.hvp`

To generate verification plan report in html format use command:
- `cd sim`
- `urg -hvp_proj cva6_embedded -group instcov_for_score -hvp_attributes description -dir vcs_results/default/vcs.d/simv.vdb -plan cva6.hvp -mod modifier_embedded.hvp`

## Environment variables
Other environment variables can be set to overload default values
provided in the different scripts.

The default values are:

- `RISCV_GCC`: `$RISCV/bin/riscv-none-elf-gcc`
- `RISCV_OBJCOPY`: `$RISCV/bin/riscv-none-elf-objcopy`
- `VERILATOR_ROOT`: `../tools/verilator-4.110` to install in core-v-verif/tools
- `SPIKE_INSTALL_DIR`: `../tools/spike` to install in core-v-verif/tools

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
