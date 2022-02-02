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


Introduction
============

This document captures the methods, verification environment
architectures and tools used to verify the first two members CORE-V
family of RISC-V cores, the CV32E and CVA6.

The OpenHW Group will, together with its Member Companies, execute a
complete, industrial grade pre-silicon verification of the first
generation of CORE-V IP, the CV32E and CVA6 cores, including their
execution environment [1]_. Experience has shown that “complete”
verification requires the application of both dynamic (simulation, FPGA
prototyping, emulation) and static (formal) verification techniques. All
of these techniques will be applied to both CV32E and CVA6.

License
-------

Copyright 2020, 2021 OpenHW Group.

The document is licensed under the Solderpad Hardware License, Version
2.0 (the "License"); you may not use this document except in compliance
with the License. You may obtain a copy of the License at:

https://solderpad.org/licenses/SHL-2.0/

Unless required by applicable law or agreed to in writing, products
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.

See the License for the specific language governing permissions and
limitations under the License.

CORE-V Projects
---------------

The `core-v-verif <https://github.com/openhwgroup/core-v-verif>`_ project is being
developed to verify all CORE-V cores.  The cores themselves are in their own git
repositories.  Below are links to the RTL sources and documentation for CORE-V
cores currently in development:

- `CV32E40P RTL source <https://github.com/openhwgroup/cv32e40p>`_
- `CV32E40P user manual <https://cv32e40p.readthedocs.io/en/latest/>`_
- `CV32E40X RTL source <https://github.com/openhwgroup/cv32e40x>`_
- `CV32E40X user manual <https://cv32e40x.readthedocs.io/en/latest/>`_
- `CV32E40S RTL source <https://github.com/openhwgroup/cv32e40s>`_
- `CV32E40S user manual <https://cv32e40s.readthedocs.io/en/latest/>`_
- `CVA6 RTL source <https://github.com/openhwgroup/cva6>`_
- `CVA6 user manual <https://cva6.readthedocs.io/en/latest/intro.html>`_

The OpenHW Group also maintains the following repositories for stand-alone verification components:

- `FORCE-RISCV <https://github.com/openhwgroup/force-riscv>`_ Instruction stream generator denotated by Futurewei.

Definition of Terms
-------------------

+---------------+--------------------------------------------------------------------+
| Term          | Defintion                                                          |
+===============+====================================================================+
| BSP           | Board Support Package. A set of support files, such as a C         |
|               | runtime configuration (crt0.S), linker control script (link.ld),   |
|               | etc. that are used to define the software envrionment used by a    |
|               | test-program.                                                      |
+---------------+--------------------------------------------------------------------+
| Committer     | A Contributor who has privileges to approve and merge              |
|               | pull-requests into OpenHW Group GitHub repositories.               |
+---------------+--------------------------------------------------------------------+
| Contributor   | An employee of a Member Company that has been assigned to          |
|               | work on an OpenHW Group project.                                   |
+---------------+--------------------------------------------------------------------+
| CORE-V        | A family of RISC-V cores developed by the OpenHW Group.            |
+---------------+--------------------------------------------------------------------+
| ELF           | Executable and Linkable Format, is a common standard file          |
|               | format for executable files. The RISC-V GCC toolchain              |
|               | compiles C and/or RISC-V Assembly source files into ELF            |
|               | files.                                                             |
+---------------+--------------------------------------------------------------------+
| Instruction   | A behavioural model of a CPU. An ISS can execute the same          |
| Set           | code as a real CPU and will produce the same logical               |
| Simulator     | results as the real thing. Typically only “ISA visible”            |
| (ISS)         | state, such as GPRs and CSRs are modelled, and any                 |
|               | internal pipelines of the CPU are abstracted away.                 |
+---------------+--------------------------------------------------------------------+
| Member        | A company or organization that signs-on with the OpenHW            |
| Company       | Group and contributes resources (capital, people,                  |
| (MemberCo)    | infrastructure, software tools etc.) to the CORE-V                 |
|               | verification project.                                              |
+---------------+--------------------------------------------------------------------+
| Toolchain     | A set of software tools used to compile C and/or RISC-V            |
|               | assembler code into an executable format.                          |
+---------------+--------------------------------------------------------------------+
| Testbench     | In UVM verification environments, a testbench is a                 |
|               | SystemVerilog module that instantiates the device under            |
|               | test plus the SystemVerilog Interfaces that connect to the         |
|               | environment object. In common usage “testbench” can also           |
|               | have the same meaning as verification environment.                 |
+---------------+--------------------------------------------------------------------+
| Testcase      | In the context of the CORE-V UVM verification environment, a       |
|               | a testcase is distinct from a test-program.  A testcase is extended|
|               | from the `uvm_test` class and is used to control the the UVM       |
|               | environment at run-time.                                           |
|               |                                                                    |
|               | In core-v-verif a testcase _may_ be aware of the test-program.     |
+---------------+--------------------------------------------------------------------+
| Test-Program  | A software program, written in C or RISC-V assembly, that executes |
|               | on the simulated RTL model of a core.  Test-Programs may be        |
|               | manually written or machine generated (e.g. riscv-dv).             |
|               |                                                                    |
|               | In core-v-verif a test-program is not aware of the UVM testcase.   |
+---------------+--------------------------------------------------------------------+
| TPE           | Test-program Environment.  A less widely used term for BSP.        |
+---------------+--------------------------------------------------------------------+
| Verification  | An object constructed from a SystemVerilog class that is an        |
| Environment   | extension of `uvm_environment`.  In common usage "verification     |
|               | environment" can also mean the environment object plus all of its  |
|               | members.                                                           |
+---------------+--------------------------------------------------------------------+
| $CORE_V_VERIF | Local path of a cloned working directory of this GitHub repository.|
|               | An example to illustrate:                                          |
|               |                                                                    |
|               | [prompt]$ cd /wrk/rick/openhw                                      |
|               |                                                                    |
|               | [prompt]$ git clone https://github.com/openhwgroup/core-v-verif    |
|               |                                                                    |
|               | Here $CORE_V_VERIF is /wrk/rick/openhw/core-v-verif. Note          |
|               | that this is not a variable the user is required to set. Its use   |
|               | in this document is merely used as a reference point for an        |
|               | absolute path to your working directory.                           |
+---------------+--------------------------------------------------------------------+
| $COREV_CORE   | Shell and Make variable identifying a specific CORE-V core.        |
|               | The most often used example in this document is CV32E40P.          |
+---------------+--------------------------------------------------------------------+

Conventions Used in this Document
---------------------------------

**Bold** type is used for emphasis.

Filenames and filepaths are in italics: *./cv32e40p/README.md*.

CORE-V Genealogy
----------------

The first two projects within the OpenHW Group’s CORE-V family of RISC-V cores
are the CV32E40P and CVA6. Currently, two variants of the CV32E40P are
defined: the CV32E40X and CV32E40S. The OpenHW Group’s work builds on
several RISC-V open-source projects, particularly the RI5CY and Ariane
projects from PULP-Platform. CV32E40P is a derivation of the RI5CY
project [2]_, and CVA6 is derived from Ariane [3]_. In addition, the
verification environment for CORE-V leverages previous work done by
lowRISC and others for the Ibex project, which is a fork of the
PULP-Platform’s zero-riscy core.

This is germane to this discussion because the architecture and
implement of the verification environments for both CV32E40P and CVA6 are
strongly influenced by the development history of these cores. This is
discussed in more detailed in :ref:`pulp-verif`.


A Note About EDA Tools
----------------------

The CORE-V family of cores are open-source, under the terms of the
Solderpad Hardware License, Version 2.0. This does not imply that the
tools required to develop, verify and implement CORE-V cores are
themselves open-source. This applies to both the EDA tools such as
simulators, and specific verification components, such as Instruction
Set Simulators.

Often asked questions are “which tools does OpenHW support?”, or “can I
use an open-source simulator to compile/run a CORE-V testbench?”. The
short answer is that the CORE-V testbenches require the use of IEEE-1800
(2017) or newer SystemVerilog tools and that this almost certainly means
that non-commercial, open-source Verilog and SystemVerilog
compiler/simulators will not be able to compile/run a CORE-V testbench.

CORE-V verification projects are intended to meet the needs of
Industrial users and will therefore use the tools and methodologies
currently in wide-spread industrial use, such as the full SystemVerilog
language, UVM-1.2, SVA, plus code, functional and assertion coverage.
For these reasons users of CORE-V verification environments will need to
have access to commercial simulation and/or formal verification tools.

The “core” testbench of the CV32E40P can be compiled/simulated
using Verilator, an open-source software tool which translates a subset
of the SystemVerilog language to a C++ or SystemC cycle-accurate
behavioural model. Note that "core" testbench is not considered a production
verification environment that is capable of fully verifying the CORE-V cores.
The purpose of the "core" testbench is to support software teams wishing to
run test-programs in a simulation environment.


.. [1]
   Memory interfaces, Debug&Trace capability, Interrupts, etc.

.. [2]
   Note that CV32E40P is not a fork of RI5CY. Rather, the GitHub repository
   https://github.com/pulp-platform/riscv was moved to
   https://github.com/openhwgroup/core-v-cores.

.. [3]
   CVA6 is not a fork of the Ariane. The GitHub repository
   https://github.com/pulp-platform/ariane was moved to
   https://github.com/openhwgroup/cva6.

