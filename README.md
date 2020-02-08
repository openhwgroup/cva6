# core-v-verif
Functional verification project for the CORE-V family of RISC-V cores. This project is under active construction, and changes are happening regularly.

## Getting Started
First, have a look at the [OpenHW Group's website](https://www.openhwgroup.org) to learn a bit more about who we are and what we are doing.

The documentation for the various CORE-V cores is located in the [OpenHW Group's CORE-V documentation repo](https://github.com/openhwgroup/core-v-docs).

If you want to run a simulation there are currently two perferred options:
1. To run the CORE testbench (based on the RI5CY testbench) and associated testcases, go to cv32/sim/core and read the README.
2. To run the CV32E40P UVM environment, go to cv32/sim/uvmt_cv32 and type `make`.  Note that only the Metrics **_dsim_** SystemVerilog simulator has been tested at this time (although it _should_ work with Cadence **_xrun_** as well).
<br><br>A third option is to `cv32/tests/core` and look at the README and Makefile.  Please note that this will eventually be deprecated.
