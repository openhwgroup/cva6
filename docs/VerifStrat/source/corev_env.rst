..
   Copyright (c) 2020 OpenHW Group

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


.. _corev_env:

CORE-V Verification Environment
===============================

A goal of the core-v-verif project is to produce a unified
verification environment for all CORE-V cores supported by the OpenHW.  While
several of the chapters of this document focus on the specifics of a single
core, such as the CV32E40P, this chapter details how the components,
structure and organization of core-v-verif are used to implement and deploy a
complete simulation verification environment for any core in the CORE-V family.

**Note:** This chapter of the Verification Strategy is a work-in-progress.
It contains several forward looking statements about verification components that are defined, but yet to be implemented.

The core-v-verif project is not a single verification environment that is
capbable of supporting any-and-all CORE-V cores. Rather, core-v-verif supports
the verification of multiple cores by enablng the rapid creation of core-specific
verification environments.  There is no attempt to define a one-size-fits-all
environment as these inevitably lead to either bloated code, needless complexity
or both.  Instead, the idea is to create a toolkit that allows for the rapid
development of core-specific environments using a set of high-level reusable
components and a standard UVM framework.

UVM environments are often described as a hierarchy with the device-under-test
(the core) at the bottom and testcases at the top.  In between are various
components with increasing degress of abstraction as we go from the bottom
levels (the register-transfer level) to the middle layers (transaction-level)
to the top (tests).  The lower layers of the environment see the least amount
of re-use owing to the need to deal with core-specific issues.  Components at
this level are core-specific.  At the transaction level there can be
considerable amounts of re-use.  For example, it is eary to imagine a single UVM
Debug Agent serving the needs of any and all CORE-V cores.  The test level sees
a mix of re-usable tests (e.g. RV32IMAC compliance) and core-specific tests
(e.g. hardward loops in CV32E40P).

The core-v-verif project expliots this idea to maximize re-use across multiple
cores by striving to keep as much of the environment as possible independant of
the core's implementation.  Components such as the instruction generator,
reference model, CSR checkers can be made almost entirely independent of a
specific core because they can be based on the ISA alone.  Other components
such as the functional coverage model, debug and interrupt Agents and the
test-program environment can be implemented as a mix of re-usable
components and core-specific components.

Depending on the details of the top-level interfaces of individual cores, the
lowest layers of the core-v-verif environment may not be re-usable at all.


Environment Structure
---------------------

A CORE-V verification environment, built from the resources provided by
core-v-verif can be conceptually divided into four levels: Testbench
Layer, Translation Layer, Abstraction Layer and Test Layer.  Each of
these will be discussed in turn.

Testbench Layer
~~~~~~~~~~~~~~~

A CORE-V testbench layer is comprised of two SystemVerilog modules and a number
of SystemVerilog interfaces.  We will discuss the SystemVerilog interfaces
first, as this will make it easier to understand the structure and purpose of
the modules.

SystemVerilog Interfaces
^^^^^^^^^^^^^^^^^^^^^^^^

On any given CORE-V core, the top-level ports of the core can be categorized
as follows:

- Instruction and Data memory interface(s)
- Clocks and Resets
- Configuration
- Interrupts
- Trace
- Debug
- Special Status and Control

The Instruction and Data memory interface is listed first for a reason.  This
interface is generally the most core-specific.  For example, CV32E supports I&D
interfaces that are AHB-like while CVA6 supports AXI-like interfaces.  These
are significant difference and so the Testbench Layer deliberately hides this
interface from the higher-level layers.  This is done in the "DUT Wrapper"
module, see below.

The remaining interface categories can be defined as generic collections of
input or output signals whose operation can be defined by higher layers.  A few
examples should illustrate this point:

- Clocks and resets can be parameterized arrays of clock and reset signals. The
  upper layers of the environment will define the number of clocks and implement
  the appropriate frequency and phase relationships.  Resets are managed in the
  same manner.
- The Interrupts interface can also be implemented as parameterized array of
  bits.  The upper layers of the environment are responsible for asserting and
  deasserting these signals under direction of a UVM sequence and/or test.

Testbench Modules
^^^^^^^^^^^^^^^^^

The two modules of the Testbench Layer are the "DUT Wrapper" and the "Testbench".
The purpose of the wrapper is to conceal as many core-specific physical attributes
as possible.  As hinted at above this is done by keeping control of the core's
memory interface(s) and mapping all other ports to one of the non-memory
interface types.

The wrapper instantiates a memory model that connects directly to the core's
instruction and data interface(s). This memory model also supports a number of
memory mapped virtual peripherals. The core's memory interface is not "seen" by
any other part of the environment, so this interface (or these interfaces, as
the case may be) can be completely different from other cores and the only part
of the environment affected is the DUT wrapper, and its memory model.  The
address map of the modeled memory and peripherals is implemented to ensure
compatibility with the test-program environment (described later in this
chapter).

The Testbench module is mostly boiler-plate code that does the following:
- instaniates the wrapper
- push handles of the SV interfaces to the UVM configuration database
- invoke run_test()
- Implement a final code-block to display test pass/fail

The expection is that the DUT Wrapper module will be core-specific and will
need to be coded from scratch for each CORE-V core.  The Testbench module is
also expected to be core-specific, but can be easily created by copying and
modifying a Testbench module from a previous generation.   The SystemVerilog
interfaces for Clocks and Resets, Configuration, Interrupts, Trace, Debug,
plus Special Status and Control are generic enough to be fully re-used.

Repository Structure
--------------------

The top-level of the core-v-verif repository is specifically organized to
support multiple verification environments. The directory structure below
shows a version of core-v-verif that supports multiple CORE-V cores.  What
follows is a brief discription of the purpose of each top-level directory.
Refer to the README files at each of these locations for additional information.
If you read nothing else, *please* read *$CORE\_V\_VERIF/mk/uvmt/README.md*.

- **core-v-cores**: the the Makefiles in the <core>/sim directory will clone
  the RTL for <core> into core-v-cores/<core>/rtl.  This structure allows for
  the simulataneous verification of multiple cores from the same core-v-verif
  repostory.
- **<core>**: this directory contains the <core> specific environment, testbench,
  tests and simulation directories.
- **ci**: This directory supports common and core-specific scripts and
  configuration filesto support user-level regressions and the Metrics continuous
  integration flow.
- **lib**: This is where the bulk of the re-usable components and tests are
  maintained. This is where you will find the instruction generator, reference
  model, common functional coverage models, UVM Agents for clocks-and-resets,
  interrupts, status, etc.

::

  $CORE_V_VERIF
    ├── core-v-cores
    │   ├── <core1>
    │   ├── <core2>
    │   └── ...
    ├── <core>
    │   ├── env
    │   ├── sim
    │   ├── tb
    │   └── tests
    ├── ci
    │   ├── common
    │   ├── <core1>
    │   ├── <core1>
    │   └── ...
    └── lib
        ├── sim_libs
        ├── riscv_tests
        ├── uvm_tests
        ├── uvm_agents
        └── uvm_libs
