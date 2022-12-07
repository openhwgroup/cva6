<!--

 Copyright 2020, 2021 OpenHW Group

 Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
 you may not use this file except in compliance with the License.
 You may obtain a copy of the License at

     https://solderpad.org/licenses/

 Unless required by applicable law or agreed to in writing, software
 distributed under the License is distributed on an "AS IS" BASIS,
 WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 See the License for the specific language governing permissions and
 limitations under the License.

 SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0

-->

# core-v-verif
Functional verification project for the CORE-V family of RISC-V cores.

<!--
## NEWS UPDATES:
**2021-07-15**: The verificaton environment for the [cv32e40s](https://github.com/openhwgroup/cv32e40s) is up and running.
<br>
**2021-03-23**: The verificaton environment for the [cv32e40x](https://github.com/openhwgroup/cv32e40x) is up and running.
<br>
**2020-12-16**: The [cv32e40p_v1.0.0](https://github.com/openhwgroup/core-v-verif/releases/tag/22dc5fc) of core-v-verif is released.
This tag clones the v1.0.0 release of the CV32E40P CORE-V core and will allow you to reproduce the verification environment as it existed at `RTL Freeze`.
<br>
More news is available in the [archive](https://github.com/openhwgroup/core-v-verif/blob/master/NEWS_ARCHIVE.md).
-->

## Getting Started
First, have a look at the [OpenHW Group's website](https://www.openhwgroup.org) to learn a bit more about who we are and what we are doing.
<br>
For first time users of CORE-V-VERIF, the **Quick Start Guide** in the [CORE-V-VERIF Verification Strategy](https://docs.openhwgroup.org/projects/core-v-verif/en/latest/quick_start.html) is the best place to start.

<!--
### Getting started with CV32E4\* cores
If you want to run a simulation there are two options:
1. To run the CORE testbench for the CV32E40P, go to `cv32e40p/sim/core` and read the README.
2. To run any of the CV32E4\* UVM environment go to `mk/uvmt` and read the README.
-->

<!--
#### CV32E40P coverage data
The most recently published coverage report for the CV32E40P can be found [here](https://openhwgroup.github.io/core-v-verif/).
-->

<!--
### Getting started with CVA6
To run CVA6 testbench, go to [cva6](cva6) directory and read the README.
-->

## Directory Structure of this Repo
### bin
Various utilities for running tests and performing various verification-related activities in the core-v-verif repository.

### core-v-cores
Empty sub-directory into which the RTL from one or more of the [CORE-V-CORES](https://github.com/openhwgroup/core-v-cores) repositories is cloned.

### cv32e40p, cv32e40x, cv32e40s, cva6
Core-specific verification code.

### docs
Sources for the Verification Strategy document, DV plans, coding style guidelines and available coverage reports.

### mk
Common simulation Makefiles that support testbenches for all CORE-V cores.

### lib
Common components for the all CORE-V verification environments.

### vendor_lib
Verification components supported by third-parties.

## Contributing
We highly appreciate community contributions. You can get a sense of our current needs by reviewing the GitHub
[projects](https://github.com/openhwgroup/core-v-verif/projects) associated with this repository.   Individual work-items
within a project are defined as [issues](https://github.com/openhwgroup/core-v-verif/issues) with a `task` label.
<br><br>To ease our work of reviewing your contributions, please:

* Review [CONTRIBUTING](https://github.com/openhwgroup/core-v-verif/blob/master/CONTRIBUTING.md)
and our [SV/UVM coding style guidelines](https://github.com/openhwgroup/core-v-verif/blob/master/docs/CodingStyleGuidelines.md).
* Split large contributions into smaller commits addressing individual changes or bug fixes.
Do not mix unrelated changes into the same commit!
* Write meaningful commit messages.
* If asked to modify your changes, do fixup your commits and rebase your branch to maintain a clean history.
