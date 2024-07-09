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

- `DV_TARGET`: `cv64a6_imafdc_sv39`
- `DV_SIMULATORS`: `veri-testharness,spike`
- `DV_TESTLISTS`: `../tests/testlist_riscv-tests-$DV_TARGET-p.yaml
../tests/testlist_riscv-tests-$DV_TARGET-v.yaml`
- `DV_OPTS`: no default value
