Core-V-Verif Utilities
==================================

This directory contains various utilities for running tests and performing various verification-related 
activities in the core-v-verif repository.

Unless otherwise noted all utilities in this directory should be agnostic to $CWD.  Therefore a user
should be able to run the utilities via a PATH from any directory.  The utilities will be able to 
determine their own directory based on the implementation langugage hooks available.

For example from a bash-type shell:<br>
> % export PATH=./core-v-verif/bin:$PATH

Utility Documentation
==================================

Documentation for each of the utilities are included below.  Each utility should also support a help option
on the command line for describing options and arguments available.

==================================

## makecv32
This is a simple wrapper around the main simulation Makefile located in:<br>

cv32/sim/uvmt_cv32

This should enable simulations to be executed regardess of current shell directory.  All common make flags
and conventions should be passed to the underlying Makefile directory.

*Examples:*
> % makecv32 sanity WAVES=1 SIMUALTOR=vsim<br>
% makecv32 corev-dv corev_rand_instr_test_0`

## ci_check

Continuous integration checker script.  This script runs a quick sanity regression on the requested 
simulator for the purposes of ensuring a pull-request can be safely made.  Note that *ci_check* should now
be able to be executed in any directory where previously it required the user to *cd* to ci/.  Please 
refer to *ci_check*'s help utility for more details on options

*Examples:*
> \# Run CI sanity regression on Xcelium<br>
% ci_check -s xrun<br>
> \# Get help of all available options<br>
% ci_check --help

## cv_regress

Regression script generator utility.  *cv_regress* will read in one or more regressions defined in a specific
YAML format into an output format suitable for the specified regression platform or utlity.  The currently supported
output platforms are:<br>
- Metrics JSON (--metrics)
- Shell Script (--sh)

The format of the YAML testlist file is given below.  All YAML regression testslists should go in the following directory:
> core-v-verif/\<project>/regress<br>

where *\<project>* is either cv32 (default) or cv64.

Note that the utility has the ability to combine multiple testlists to build larger regressions.  Therefore the --file 
option may be specified multiple times.

Please refer to the help utility of *cv_regress* for more details on the utility.

*Examples:*
> \# Read in *cv32_ci_check* testlist with Questa and emit an executable shell script<br>
% cv_regress --file=cv32_ci_check.yaml --simulator=vsim --outfile=vsim_ci_check.sh

### Regression YAML Format

The following describes the YAML format for regression testlists.  

>\<*Required*: the name of the testlist><br>
name: \<string\><br>
\<*Required*: human-readable description to specify the intent of the testlist><br>
description: \<string><br>
><br>
\# List of builds, this can include SystemVerilog compiles and riscv-dv compiles<br>
\# Multiple builds may be defined<br>
builds:<br>
&nbsp;&nbsp;build_name0:<br>
&nbsp;&nbsp;&nbsp;&nbsp;<*Required*: make command for the build><br>
&nbsp;&nbsp;&nbsp;&nbsp;cmd: make comp<br>
&nbsp;&nbsp;&nbsp;&nbsp;<*Required*: make directory for the build><br>
&nbsp;&nbsp;&nbsp;&nbsp;dir: cv32/sim/uvmt_cv32<br>
><br>
\# List of tests<br>
\# Multiple tests can be defined<br>
tests:<br>
&nbsp;&nbsp;test_name0:<br>
&nbsp;&nbsp;&nbsp;&nbsp;<*Required*: build dependecies, can be a list of single build_name><br>
&nbsp;&nbsp;&nbsp;&nbsp;build: \<string><br>
&nbsp;&nbsp;&nbsp;&nbsp;<*Required*: human-readable test description><br>
&nbsp;&nbsp;&nbsp;&nbsp;description: \<string><br>
&nbsp;&nbsp;&nbsp;&nbsp;<*Required*: make directory for the test><br>
&nbsp;&nbsp;&nbsp;&nbsp;dir: \<string><br>
&nbsp;&nbsp;&nbsp;&nbsp;<*Optional*: A make command to run before running the test(s).  This could be used for gen_* makes for corev-dv<br>
&nbsp;&nbsp;&nbsp;&nbsp;precmd: \<string><br>
&nbsp;&nbsp;&nbsp;&nbsp;<*Required*: make directory for the test><br>
&nbsp;&nbsp;&nbsp;&nbsp;cmd: \<string><br>
&nbsp;&nbsp;&nbsp;&nbsp;<*Optional*: The number of test iterations to run.  Note that all runs will receive a random seed><br>
&nbsp;&nbsp;&nbsp;&nbsp;num: \<number>


