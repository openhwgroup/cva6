Core-V-Verif Utilities
==================================

This directory contains various utilities for running tests and performing various verification-related 
activities in the core-v-verif repository.

Unless otherwise noted all utilities in this directory should be agnostic to $CWD.  Therefore a user
should be able to run the utilities via a PATH from any directory.  The utilities will be able to 
determine their own directory based on the implementation langugage hooks available.

For example from a bash-type shell:<br>
> % export PATH=./core-v-verif/bin:$PATH

Requirements
============
Much of the scriptware in CORE-V-VERIF is written in python and makes use of external packages that are not necessarily distributed with python itself.
An easy way to get the Python plug-ins installed on your machine is:
> % git clone https://github.com/openhwgroup/core-v-verif.git \<core-v-verif><br>
> % cd \<core-v-verif>/bin<br>
> % pip3 install -r requirements.txt<br>

Utility Documentation
=====================

Documentation for each of the utilities are included below.  Each utility should also support a help option
on the command line for describing options and arguments available.

## makeuvmt
This is a simple wrapper to redirect a make call to any core's UVMT Makefile.  This redirection script
simply requires that you either:
- specify CV_CORE in your environment -or-
- specify CV_CORE on the maekeuvmt command line as an override

The script will then invoke make in the following directory:<br>
> \<core-v-verif>/$(CV_CORE)/sim/uvmt

This should enable simulations to be executed regardess of current shell directory.  All common make flags
and conventions should be passed to the underlying Makefile directory.

*Examples:*
> \# makeuvmt can be invoked from any directory<br>
> % makeuvmt test TEST=hello-world WAVES=1 SIMUALTOR=vsim<br>
> \# Override the core to cv32e40x (regardless of CV_CORE environment setting)<br>
> % makeuvmt test TEST=hello-world WAVES=1 CV_CORE=cv32e40x<br>

## ci_check

Continuous integration checker script.  This script runs a quick sanity regression on the requested 
simulator for the purposes of ensuring a pull-request can be safely made.  Note that *ci_check* should now
be able to be executed in any directory where previously it required the user to *cd* to ci/.  Please 
refer to *ci_check*'s help utility for more details on options

If required, the step and compare ISS can be disabled for this regression by setting _--iss=0_

*Examples:*
> \# Run CI sanity regression on Xcelium<br>
% ci_check -s xrun<br>
> \# Run CI sanity regression on Xcelium with the ISS disabled<br>
% ci_check -s xrun --iss=0<br>
> \# Get help of all available options<br>
% ci_check --help

## cv_regress

Regression script generator utility.  *cv_regress* will read in one or more regressions defined in a specific
YAML format into an output format suitable for the specified regression platform or utlity.  The currently supported
output platforms are:<br>
- Metrics JSON (--metrics)
- Shell Script (--sh)
- Vmanager VSIF (--vsif)

The format of the YAML testlist file is given below.  All YAML regression testslists should go in the following directory:
> core-v-verif/\<project>/regress<br>

where *\<project>* is a core (cv32e40p or cva6)

Note that the utility has the ability to combine multiple testlists to build larger regressions.  Therefore the --file 
option may be specified multiple times.

Please refer to the help utility of *cv_regress* for more details on the utility.

*Examples:*
> \# Read in *cv32e40p_ci_check* testlist with Questa and emit an executable shell script<br>
% cv_regress --file=cv32e40p_ci_check.yaml --simulator=vsim --outfile=vsim_ci_check.sh

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


