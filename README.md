# core-v-verif
Functional verification project for the CORE-V family of RISC-V cores. This project is under active development.

## NEWS FLASH
The OpenHW Group CV32E40P is now live!<br>This repository no longer contains a local copy of the RTL.  The RTL is cloned from the appropriate [core-v-cores](https://github.com/openhwgroup/core-v-cores) repository as needed.

## Getting Started
First, have a look at the [OpenHW Group's website](https://www.openhwgroup.org) to learn a bit more about who we are and what we are doing.  

The design and verification documentation for the various CORE-V cores is located in the [OpenHW Group's CORE-V documentation repo](https://github.com/openhwgroup/core-v-docs).  Reading the [Verification Strategy](https://github.com/openhwgroup/core-v-docs/blob/master/verif/Common/OpenHWGroup_CORE-V_Verif_Strategy.pdf) is strongly recommended.

If you want to run a simulation there are two options:
1. To run the CORE testbench (based on the RI5CY testbench) and associated testcases, go to `cv32/sim/core` and read the README.
2. To run the CV32E40P UVM environment, go to `cv32/sim/uvmt_cv32` and read the README.
<br><br>Note that the ability to run tests from `cv32/tests/core` has been depreciated.  The README in that location is now out-of-date and Makefile no longer works.  These will be removed altogether in the not-to-distant future.

## Directory Structure of this Repo
### ci
Explainer for the CI flow used by CORE-V-VERIF.

### core-v-cores
Empty sub-directory into which the RTL from one or more of the [CORE-V-CORES](https://github.com/openhwgroup/core-v-cores) repositories is cloned.

### cv32
Verification Environments, testbenches, testcases and simulation Makefiles for the CV32E cores.

### cv64
Verification Environments, testbenches, testcases and simulation Makefiles for the CV64A cores.

### doc
Empty.  Please see the [CORE-V-DOCS](https://github.com/openhwgroup/core-v-docs) repository.

### lib
Common components for the CV32 and CV64 verification environments.
