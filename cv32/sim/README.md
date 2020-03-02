## SIM directory
The directories from which you should launch your interactive simulations and
regressions are located here.  You do not _have_ to do this, but keep in mind
that the Makefiles assume you are running from a peer level to `core` or
`uvmt_cv32`.
<br><br>There is a sub-dir for each supported CV32 verification environment.
Each sub-dir has its specific Makefile and both include `Common.mk` from this
directory.

### core
The Makefile will run the SystemVerilog testbench found in `../tb/core` and
its associated tests from `../tests/core`.  This testbench and tests were
inherited from the PULP-Platform team and have been modified only slightly.

### uvmt_cv32
The Makefile will run the SystemVerilog/UVM verification environment found in
`../tb/uvmt_cv32` and the associated tests from `../tests/uvmt_cv32`.
