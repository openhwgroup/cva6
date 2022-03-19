..
   Copyright (c) 2020, 2021, 2022 OpenHW Group

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


.. _quick_start:

CORE-V-VERIF Quick Start Guide
==============================

Many people who come to `core-v-verif <https://github.com/openhwgroup/core-v-verif>`_ for the first time
are anxious to 'get something running' and this section is written to satisfy that itch.

Note: in several places in this chapter a reference is made to $CORE_V_VERIF.
This is used as short hand for the absolute path to your local working directory.
You will not need to set this shell environment variable yourself.

A good place to start is the CV32E40P core testbench since the CV32E40P is mature, and the core testbench is very simple and runs with open-source tools.
You will need:

1. A Linux machine (core-v-verif has been successfully run under Ubuntu, Debian and CentOS).
2. Python3 and a set of plug-ins. The current plug-in list is kept in `$CORE_V_VERIF/bin/requirements.txt`.
   The easiest way to get these requirements installed on your machine is::

   $ cd $CORE_V_VERIF/bin
   $ pip install -r requirements.txt

3. A GCC cross-compiler (aka "the `Toolchain <https://github.com/openhwgroup/core-v-verif/blob/master/mk/TOOLCHAIN.md#core-v-toolchain>`_").
   Even if you already have a toolchain, please do follow that link and read **TOOLCHAIN.md** for recommended ENV variables to point to it.
4. `Verilator <https://veripool.org/guide/latest/install.html>`_.

Once the above is in place type the following::

    $ git clone https://github.com/openhwgroup/core-v-verif.git
    $ cd core-v-verif/cv32e40p/sim/core
    $ make

The above will compile the RTL and the core testbench using Verilator and run the 'hello-world' test-program.
The simulation run should produce the following::

    HELLO WORLD!!!
    This is the OpenHW Group CV32E40P CORE-V processor core.
    CV32E40P is a RISC-V ISA compliant core with the following attributes:
        mvendorid = 0x602
        marchid   = 0x4
        mimpid    = 0x0
        misa      = 0x40001104
        XLEN is 32-bits
        Supported Instructions Extensions: MIC

The README in the cv32e40p/sim/core directory will explain how to run other tests and use other simulators.

Where is the RTL?
-----------------

As core-v-verif is a single repository for the verification of several different CORE-V cores, you will not find the RTL here.
Each CORE-V core is managed in its own repository, and is automatically cloned into $CORE_V_VERIF/cores/<core_name> by the Makefiles, as needed.
If you have successfully run the hello-world test above, then you may have noticed that the RTL was cloned to $CORE_V_VERIF/cores/cv32e40p/rtl (have a look!).

UVM
---

Up to this point, the discussion has been about the "core" testbench, which is intended as demonstration vehicle only.
The primary verification environments implemented in core-v-verif are all based on the UVM.
The UVM enviroment for CV32E40P is completely separate from the core testbench and uses a different set of Makefiles.

In order to use the UVM environments you will need items 1, 2 and 3 from the list above, plus a SystemVerilog simulator capable of supporting UVM and the Imperas OVPsim Instruction Set Simulator (ISS).
You should also review the README in `$CORE_V_VERIF/mk/uvmt` for a description of the `shell ENV vars used by the UVM environment <https://github.com/openhwgroup/core-v-verif/blob/master/mk/README.md#required-corev-environment-variables>`_.
With these in place you can do the following::

    $ git clone https://github.com/openhwgroup/core-v-verif.git
    $ cd core-v-verif/cv32e40p/sim/uvmt
    $ make test TEST=hello-world CV_SIMULATOR=<xrun|vcs|vsim|riveria|dsim>

The above will compile the RTL and the UVM testbench using the selected simulator and run the 'hello-world' test-program.
Note that this is the same test-program as was used in the core testbench example above.
The simulation run will produce similar results, with lots of additional UVM messaging.

If you do not have access to the Imperas ISS you can disable it at run-time::

    $ make test TEST=hello-world CV_SIMULATOR=<xrun|vcs|vsim|riveria|dsim> USE_ISS=NO

Why UVM?
~~~~~~~~

There are three reasons why the UVM was selected as the verification methodology used by core-v-verif:
1. Using a standard methodology provides a common framework making it practical for verification IP from multiple and diverse teams to inter-operate.
2. To date, all of the cores in the OpenHW Group CORE-V family are implemented in SystemVerilog and the SystemVerilog implementation of the UVM is both complete and robust.
3. Core-v-verif was specifically created to bring industrial practises to bear for CORE-V verification, and the UVM is by far the most popular methodology used in dynamic (simulation) based verification today.

Do I need an ISS?
~~~~~~~~~~~~~~~~~

The short answer is **yes**.
Core-v-verif uses an Instruction Set Simulator (ISS) as a reference model of the CORE-V core (the Device Under Test).
A key feature of the core-v-verif UVM environments is that the state of the DUT is compared to the state of the reference model after each instruction is retired.
Without a comparison to a reference model, the pass/fail status of a given simulation is mostly vacuous.

There are two popular options for a RISC-V ISS, `Spike <https://github.com/riscv-software-src/riscv-isa-sim>`_ and `Imperas OVPsim <https://www.ovpworld.org/technology_ovpsim>`_.
At the time of this writting (2021-12-07) core-v-verif uses a commerical version of Imperas OVPsim for the CV32E4 cores.
A contribution to integrate another reference model into core-v-verif would be welcome.

Doing More in CORE-V-VERIF
--------------------------

As far as is practical, core-v-verif maintains "in place" documentation.
That is, most directries will have a `README.md` that provides information relavent to that directory and/or its sub-directories.
GitHub renders these to HTML automatically, and so this document will point you to a lot of this type of content.

At the top-level of core-v-verif, there is a subdirectory for each supported core.
All of the verification code specific to that core will be in this directory.
Look at the README in `cv32e40p` to get a sense of the directory structure of the cv32e40p-specific testbenches.
The structure of the other cores will be similar, but need not be identical.

The cv32e40p sub-tree supports a simple "core" testbench and a complete UVM verification environment.
Partial instructions to run the core testbench are provided above; see the README at `$CORE_V_VERIF/cv32e40p/sim/core` for full details.
To run the CV32E40P UVM environment, go to `$CORE_V_VERIF/cv32e40p/sim/uvmt` and read the README.

This chapter uses the CV32E40P as its example, but there are equivalent READMEs in directories for the other supported cores.

Supported Simulators
~~~~~~~~~~~~~~~~~~~~

It is a goal of core-v-verif to support all known SystemVerilog 1800-2017 compliant simulators.
The Makefiles for the UVM environments have a variable `CV_SIMULATOR` which is used to select the simulator used to compile and run a testcase.
So you can run hello-world with Cadence Xcelium like this::

    $ make test TEST=hello-world CV_SIMULATOR=xrun

To run the same test with Metrics Dsim::

    $ make test TEST=hello-world CV_SIMULATOR=dsim

The variable is used to select one of a set of simulator-specific Makefiles that are located at `$CORE_V_VERIF/mk/uvmt <https://github.com/openhwgroup/core-v-verif/tree/master/mk/uvmt>`_.

Note that core-v-verif tries to support all simulators and this requires support from OpenHW Group members.
From time to time a Makefile for a specific simulator will not see a lot of use and will inevidibly suffer from bit-rot.
If you notice an issue with a simulator-specific Makefile, please either raise a GitHub issue, or better yet, a pull-request with a fix.

Verifying other Cores
~~~~~~~~~~~~~~~~~~~~~

At the time of this writting (2021-12-17), core-v-verif supports verification of multiple CORE-V cores:

* **CV32E40P**: UVM environment is stable and v1.0.0 is complete.  Work on v2.0.0 has started.  A simple "core" testbench which can be run with open-source tools is available.
* **CV32E40X**: UVM environment is stable, and verification is on-going.
* **CV32E40S**: UVM environment is stable, and verification is on-going.
* **CVA6**: UVM environment is in the early stages of development.
* **CVE2**: Coming soon!

CV32E40P Directory Tree (simplified)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Below $CORE_V_VERIF you will find a directory named *cv32e40p*.
This directory contains all of the CV32E40P-specific sources to compile and run simulations on the CV32E40P CORE-V core.
The tree below is a somewhat simplified expansion of the directory highlighting the names, locations and purposes of key directories and files.
Other cores, e.g. CV32E40X will implement a similar directory tree.
::

  cv32e40p
    ├── bsp                                         // Board-support Package
    ├── docs
    │   └── VerifPlans
    ├── env                                         // UVM environment
    │   ├── corev-dv
    │   └── uvme
    │       ├── cov
    │       └── vseq
    ├── regress                                     // Regression configurations
    ├── sim
    │   ├── README.md
    │   ├── Common.mk
    │   ├── core                                    // Place to run simulations of the "core" testbench
    │   ├── TOOLCHAIN.md
    │   ├── tools
    │   └── uvmt                                    // Place to run simulations of the "uvm" environment
    │       ├── Makefile
    │       └── README.md
    ├── tb
    │   ├── README.md
    │   ├── core                                    // the "core" testbench
    │   │   ├── dp_ram.sv
    │   │   ├── mm_ram.sv
    │   │   ├── tb_top.sv
    │   │   ├── tb_top_verilator.cpp
    │   │   └── tb_top_verilator.sv
    │   └── uvmt                                    // the UVM environment
    │       ├── uvmt_cv32e40p_constants.sv
    │       ├── uvmt_cv32e40p_tb.sv
    │       ├── ...
    │       └── uvmt_cv32e40p_pkg.sv
    ├── tests                                       // test-programs and UVM testcases.
    │   ├── cfg
    │   │   ├── default.yaml
    │   │   ├── no_pulp.yaml
    │   │   ├── num_mhpmcounter_29.yaml
    │   │   ├── ovpsim_no_pulp.ic
    │   │   └── pulp.yaml
    │   ├── programs
    │   │   ├── corev-dv                            // configurations for randomly generated test-programs
    │   │   │   ├── corev_rand_arithmetic_base_test
    │   │   │   │   ├── corev-dv.yaml
    │   │   │   │   └── test.yaml
    │   │   |   ├── ...
    │   │   |   |
    │   │   │   └── corev_rand_jump_stress_test
    │   │   │       ├── corev-dv.yaml
    │   │   │       └── test.yaml
    │   │   └── custom                              // "custom" (manually written) test-programs
    │   │       ├── hello-world
    │   │       │   ├── hello-world.c
    │   │       │   └── test.yaml
    │   │       ├── ...
    │   │       |
    │   │       └── debug_test
    │   │           ├── debug_test.c
    │   │           └── test.yaml
    │   └── uvmt                                    // UVM testcase(s) and virtual sequences
    │
    └── vendor_lib                                  // Libraries from third-parties
        ├── README.md
        ├── google
        ├── imperas
        ├── riscv
        └── verilab

