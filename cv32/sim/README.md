## SIM directory
The directories from which you should launch your interactive simulations and
regressions are the `core` and `uvmt_cv32` directories located here.

### Cloning the RTL
The Makefiles will automatically clone the required RTL to `../../core-v-cores/cv32e40p`.
<br><br>
There are user variables
in `./Common.mk` that control the URL, branch and hash of the cloned code - see
the comment header for examples.  The defaults for these variables will clone the
most up-to-date and stable version of the RTL.  Note that this is not always the
head of the master branch.

### Simulation Directories
There is a sub-dir for each supported CV32 verification environment.
Each sub-dir has its specific Makefile and both include `Common.mk` from this
directory.

#### core
The Makefile will run the SystemVerilog testbench found in `../tb/core` and
its associated tests from `../tests/core`.  This testbench and tests were
inherited from the PULP-Platform team and have been modified only slightly.

#### uvmt_cv32
The Makefile will run the SystemVerilog/UVM verification environment found in
`../tb/uvmt_cv32` and the associated tests from `../tests/uvmt_cv32`.

#### tools
Tool specific sub-dirs for some of the tools used in the CV32.  For example,
Tcl control files for waveform viewing support.

### Other directories
There are also specific sub-dirs for some of the tools used in the CV32
project.  These will be moved the the `tools` directory in a future update:

#### xrun
Cadence Xcelium Tcl scripts for GUI and waveform viewing support.

#### questa
Mentor Questa Tcl scripts for GUI and waveform viewing support.

#### vcs
Synopsys VCS Tcl scripts for GUI and waveform viewing support.

#### mcy
Setup and configuration for [Mutual Coverage with Yosys](https://github.com/YosysHQ/mcy) from [SymbioticEDA](https://www.symbioticeda.com/).
