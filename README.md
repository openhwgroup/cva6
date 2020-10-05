# core-v-verif
Functional verification project for the CORE-V family of RISC-V cores. This project is under active development.

## NEWS UPDATES:
**2020-09-04**: a new (and _much_ better) method of specifying and organizating test-programs and simulations is now merged in.  See slide "_Test Specification Updates_" in the [2020-08-31 CV32E40P project update](https://github.com/openhwgroup/core-v-docs/blob/master/verif/MeetingPresentations/20200831-CV32E40P-ProjectScheduleUpdate.pptx).
<br>
**2020-06-12**: a new "Board Support Package" for CV32E40P simulations is installed at `cv32/bsp`.  This BSP should be used to compile/assemble your [test-programs](https://core-v-docs-verif-strat.readthedocs.io/en/latest/test_program_environment.html).  The Makefiles for both the CORE testbench and UVM verification environment have been updated to use this BSP.
<br>
**2020-06-02:** The [Imperas OVPsim Instruction Set Generator](http://www.ovpworld.org/) has been integrated into the UVM environment as the Referenece Model for the CV32E40(P).  You will need to obtain a license from Imperas to use it.
<br>
**2020-02-28:** The OpenHW Group CV32E40P is now live!<br>This repository no longer contains a local copy of the RTL.  The RTL is cloned from the appropriate [core-v-cores](https://github.com/openhwgroup/core-v-cores) repository as needed.  The specific branch and hash of the RTL is controlled by a set of variables in `cv32/sim/Common.mk`.

## Getting Started
First, have a look at the [OpenHW Group's website](https://www.openhwgroup.org) to learn a bit more about who we are and what we are doing.  

The design and verification documentation for the various CORE-V cores is located in the [OpenHW Group's CORE-V documentation repo](https://github.com/openhwgroup/core-v-docs).  Reading the [Verification Strategy](https://core-v-docs-verif-strat.readthedocs.io/en/latest/) is strongly recommended.

### With CV32E40P
If you want to run a simulation there are two options:
1. To run the CORE testbench (based on the RI5CY testbench), go to `cv32/sim/core` and read the README.
2. To run the CV32E40P UVM environment, go to `cv32/sim/uvmt_cv32` and read the README.

## With CVA6
To run CVA6 testbench, go to [cva6](cva6) directory and read the README.

## Directory Structure of this Repo
### bin
Various utilities for running tests and performing various verification-related activities in the core-v-verif repository.

### ci
Scriptware for user regression tests and an explainer for the Metrics continuous integration flow used by CORE-V-VERIF.

### core-v-cores
Empty sub-directory into which the RTL from one or more of the [CORE-V-CORES](https://github.com/openhwgroup/core-v-cores) repositories is cloned.

### cv32
Verification Environments, testbenches, testcases and simulation Makefiles for the CV32E cores.

### cva6
Verification Environments, testbenches, testcases and simulation Makefiles for the CVA6 cores.

### doc
Contains a pointer to the [CORE-V-DOCS](https://github.com/openhwgroup/core-v-docs) repository.

### lib
Common components for the CV32 and CVA6 verification environments.

### vendor_lib
Verification components supported by third-parties.

## Contributing
We highly appreciate community contributions. You can get a sense of our current needs by reviewing the GitHub
[projects](https://github.com/openhwgroup/core-v-verif/projects) associated with this repository.   Individual work-items
within a project are defined as [issues](https://github.com/openhwgroup/core-v-verif/issues) with a `task` label.
<br><br>To ease our work of reviewing your contributions, please:

* Review [CONTRIBUTING](https://github.com/openhwgroup/core-v-verif/blob/master/CONTRIBUTING.md).
* Split large contributions into smaller commits addressing individual changes or bug fixes. Do not mix unrelated changes
into the same commit!
* Write meaningful commit messages.
* If asked to modify your changes, do fixup your commits and rebase your branch to maintain a clean history.
