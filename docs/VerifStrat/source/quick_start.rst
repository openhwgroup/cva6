..
   Copyright (c) 2020, 2021 OpenHW Group

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

A good place to start is the CV32E40P core testbench since the CV32E40P is mature, and the core testbench is very simple.
You will need:

1. A Linux machine (core-v-verif has been successfully run under Ubuntu, Debian and CentOS)
2. Lots of python3 plug-ins.
3. A GCC cross-compiler (aka "the `Toolchain <https://github.com/openhwgroup/core-v-verif/blob/master/cv32e40p/sim/TOOLCHAIN.md#core-v-toolchain>`_")
4. `Verilator <https://veripool.org/guide/latest/install.html>`_.

Once the above is in place type the following::

    $ git clone https://github.com/openhwgroup/core-v-verif.git
    $ cd core-v-verif/cv32e40p/sim/core
    $ make

The above will clone a version of the CV32E40P core RTL from its repository, compile it and the core testbench using Verilator and run the 'hello-world' test-program.
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

As core-v-verif is a repository for multiple CORE-V cores, you will not find the RTL here.
Each CORE-V core is managed in its own repository, and is cloned into $PROJ_ROOT/cores/<core_name> by the Makefiles.


Doing More in CORE-V-VERIF
--------------------------

As far as is practical, core-v-verif maintains "in place" documentation.
That is, most directries will have a `README.md` that provides information relavent to that directory and/or its sub-directories.
GitHub renders these to HTML automatically, and so this section of the Verification Strategy will point you to a lot of this type of content.

At the top-level of core-v-verif, there is a subdirectory for each supported core.
All of the verification code specific to that core will be in this directory.
Look at the README in `cv32e40p` to get a sense of the directory structure of the cv32e40p-specific testbenches.
The structure of the other cores will be similar, but need not be identical.

The cv32e40p sub-tree supports a simple "core" testbench and a complete UVM verification environment.
Partial instructions to run the core testbench are provided above; see the README at `cv32e40p/sim/core` for full details.
To run the CV32E40P UVM environment, go to `cv32e40p/sim/uvmt` and read the README.

This chapter uses the CV32E40P as its example, but there are equivalent READMEs in directories for the other supported cores.

Supported Simulators
~~~~~~~~~~~~~~~~~~~~

It is a goal of core-v-verif to support all known SystemVerilog 1800-2017 compliant simulators.
The Makefiles for the UVM environments have a variable `SIMULATOR` which is used to select the simulator used to compile and run a testcase.
So you can run hello-world with Cadence Xcelium like this::

    $ make test TEST=hello-world SIMULATOR=xrun

To run the same test with Metrics Dsim::

    $ make test TEST=hello-world SIMULATOR=dsim

The variable is used to select one of a set of simulator-specific Makefiles that are located at `$PROJ_ROOT/mk/uvmt <https://github.com/openhwgroup/core-v-verif/tree/master/mk/uvmt>`_.

Note that core-v-verif tries to support all simulators and this requires support from OpenHW Group members.
From time to time a Makefile for a specific simulator will not see a lot of use and will inevidibly suffer from bit-rot.
If you notice an issue with a simulator-specific Makefile, please do raise an issue.

CV32E40P Directory Tree (simplified)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

For example only::

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
    ├── tests                                       // test-programs and testcases.
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
    │   │   │   ├── corev_rand_debug
    │   │   │   │   ├── corev-dv.yaml
    │   │   │   │   └── test.yaml
    │   │   │   └── corev_rand_jump_stress_test
    │   │   │       ├── corev-dv.yaml
    │   │   │       └── test.yaml
    │   │   └── custom                              // "custom" (manually written) test-programs
    │   │       ├── hello-world
    │   │       │   ├── hello-world.c
    │   │       │   └── test.yaml
    │   │       ├── ...
    │   │       └── debug_test
    │   │           ├── debugger_exception.S
    │   │           ├── debugger.S
    │   │           ├── debug_test.c
    │   │           ├── handlers.S
    │   │           ├── single_step.S
    │   │           ├── test.yaml
    │   │           └── trigger_code.S
    │   └── uvmt                                    // UVM testcase(s) and virtual sequences
    │       ├── base-tests
    │       │   ├── uvmt_cv32e40p_base_test.sv
    │       │   ├── uvmt_cv32e40p_base_test_workarounds.sv
    │       │   └── uvmt_cv32e40p_test_cfg.sv
    │       └── vseq
    │           └── uvmt_cv32e40p_vseq_lib.sv
    └── vendor_lib
        ├── README.md
        ├── google
        ├── imperas
        ├── riscv
        └── verilab

