# CV32E40P: Verification Environment for the CV32E40P CORE-V processor core.

CV32E40P-specific SystemVerilog sources plus C and assembly test-program sources for the CV32E40P verification environment.
Non-CV32E40P-specific verification components used in this verification environment are in `../lib` and `../vendor_lib`.

## Directories:
- **bsp**:   the "board support package" for test-programs compiled/assembled/linked for the CV32E40P.  This BSP is used by both the `core` testbench and the `uvmt_cv32` UVM verification environment.
- **env**:   the UVM environment class and its associated infrastrucutre.
- **sim**:   directory where you run the simulations.
- **tb**:    the Testbench module that instanitates the core.
- **tests**: this is where all the testcases are.

There are README files in each directory with additional information.

## Getting Started
Check out the Quick Start Guide in the [CORE-V-VERIF Verification Strategy](https://core-v-docs-verif-strat.readthedocs.io/en/latest/).
