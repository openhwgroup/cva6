## SIM directory
Convenient directories for launching simulations.
By default, all generated files will be written to a subdirectory of either the `core` or `uvmt` directories.
This can be controlled using environment variables as explained in `$CORE_V_VERIF/mk/uvmt/README.md`.

### Cloning the RTL
The Makefiles will automatically clone the required RTL to `$CORE_V_VERIF/core-v-cores/cv32e40p`.
<br><br>
Variables in `./ExternalRepos.mk` control the URL, branch and hash of the cloned code - see
the comment header for examples.  The defaults for these variables will clone the
most up-to-date and stable version of the RTL.  Note that this is not always the
head of the master branch.

### Directories

#### core
The Makefile will run the SystemVerilog testbench found in `../tb/core` and
its associated tests from `../tests/core`.  This testbench and tests were
inherited from the PULP-Platform team and have been modified only slightly.

#### uvmt
The Makefile will run the SystemVerilog/UVM verification environment found in
`../tb/uvmt` and the associated tests from `../tests/uvmt`.

#### tools
Tool specific sub-dirs for some of the tools used in the CV32E40P.  For example,
Tcl control files for waveform viewing support.
