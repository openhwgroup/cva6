..
   Copyright (c) 2023 OpenHW Group
   Copyright (c) 2023 Thales DIS design services SAS

   SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1

.. Level 1
   =======

   Level 2
   -------

   Level 3
   ~~~~~~~

   Level 4
   ^^^^^^^

.. _cva6_user_guide:

OpenHW Group CVA6 User Manual
=============================
This is a template for the CVA6 user guide.

Changelog
---------
We start filling in the Changelog after the first “official” release of the user manual, at the end of step 2.

.. future file beak

Introduction
============

License
-------
Copyright 2022 OpenHW Group and Thales
SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1

Licensed under the Solderpad Hardware License v 2.1 (the “License”); you may not use this file except in compliance with the License, or, at your option, the Apache License version 2.0.
You may obtain a copy of the License at https://solderpad.org/licenses/SHL-2.1/.
Unless required by applicable law or agreed to in writing, any work distributed under the License is distributed on an “AS IS” BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and limitations under the License.

Work In Progress
----------------
The current limitation of documentation on CVA6 is well understood.
Rather than regretting this; the reader is encouraged to contribute to it to make CVA6 an even better core.
This document is a work in progress and the team currently drafting it focuses on its use for the “step 1” verification of the project.

Target Audience
---------------
The CVA6 user manual targets:
* SW programmers
* HW designers who integrate CVA6 into a SoC/ASIC/FPGA
* Architects who design a coprocessor for the CV-X-IF interface and who need to create SW to use it
* HW designers who synthetize/place&route/verify a design that embeds CVA6
* Verification engineers involved in the OpenHW Group’s CVA6 project who use this manual as a reference.

The user guide does not target people who dig into CVA6 design. No internal mechanisms are described here, except if the user has some sort of control on it; there is a separate design specification for this purpose.

CVA6 Overview
--------------
Jérôme will write it (mainly reusing the requirements specification).
CVA6 is an application core…
Scope of the IP…
We target all versions of the core

Compliance to Standards and Specifications
------------------------------------------
Reuse the references from the requirement specification (Jérôme can do it).
CVA6 is a RISC-V processor core. It is compatible with the following specifications:
(Insert there the list of RISC-V, AMBA, CV-X-IF, TRI… specifications.

.. future file beak

Programmer’s View
=================
In each section, we must make clear when a feature is variable upon parameters

RISC-V Extensions
-----------------
Need for step1 verification.
As CVA6 implements specified RISC-V extensions, this will be a short section, where we mention which extensions are always present or optional.

RISC-V Privileges
-----------------
Need for step1 verification.
We identify the supported RISC-V privileges

RISC-V Virtual Memory
---------------------
Need for step1 verification (MMU by 10xEngineers).
We identify the supported RISC-V virtual memories

Memory Alignment
----------------
CVA6 does not support non-aligned memory accesses.

.. future file beak

Custom RISC-V instructions
==========================
Desired for step2 verification.
This is mostly for FENCE.T.

.. future file beak

PMA
===
Gap for step1 verification. Reuse DVplan from CV32E40S? Mike will reach out to some people who could help.

.. future file beak

PMP
===
Gap for step1 verification. Reuse DVplan from CV32E40S? Mike will reach out to some people who could help.
Refer to RISC-V specs and focus on the parameters (regions, granularity)

.. future file beak

Traps, Interrupts, Exceptions
=============================
Gap for step1 verification. Reuse DVplan from E4? Jean-Roch will check with André. Mike will reach out to some people who could help.
We expect this section to be 1 page.

.. future file beak

Compiler command lines
======================
Add GCC and LLVM command lines, compiler versions, options that work well with CVA6.
Going further to fine tune the compiler options for performance, benchmarking, code density is not the scope here and would call for a white paper.

.. future file beak

RISC-V Instructions
===================
URGENT NEED FOR VERIFICATION. TSS will lead.
Jean-Roch suggests to reuse https://github.com/openhwgroup/cva6/blob/master/docs/03_cv32a6_design/source/cv32a6_isa.rst.
Do we want to have this level of details in the user doc?

.. future file beak

Control and Status Registers (CV32A6)
=====================================
URGENT NEED FOR VERIFICATION. TSS will lead.
The CSR table generated by JADE (standalone file transferred from the design document).
Jea-Roch will ask Tamas if he can provide TSS with an evaluation license to maintain the file for step 1.

.. future file beak

Control and Status Registers (CV64A6)
=====================================
CSR table (CV64A6)
The CSR table generated by JADE (standalone file. Does it already exist?).

.. future file beak

CSR cache control
=================
Which cache controls are available to the user, what they do, how to use them.
Typical usage can also be mentioned.

.. future file beak

CSR performance counters control
================================
Focus on the way to use the performance counters.

.. future file beak

Parameters and Configuration
============================

Parameters
----------
We start with a table of parameters as they have an impact on almost all subsequent sections.
Suggestion to use the SystemVerilog names of the parameters (instead of another convention) as a reference. We need to make a link between parameters and their impact on the supported extensions.
Jean-Roch said he has something.

Configurations
--------------
A configuration is a fixed set of parameters.
We list the parameters of the configuration for which verification activities have started.
Give step 1 configuration (Jean-Roch?)

Interfaces
----------
List of interface signals
As in the RTL files.

AXI Interface
~~~~~~~~~~~~~
Need for step1 verification. Already written by MU Electronics.
Focus on the features used by the CVA6 and refer to ARM documentation for the AXI specification (e.g. do not draw the standard chronogram).
Features:
* See requirement specification
* Atomic transactions
* “USER” bus width extension
* Transaction ordering

Debug Interface
~~~~~~~~~~~~~~~
Desired for step1 verification, but we can likely reuse an E4 DVplan.
Remember: the debug module (DTM) is not in the scope, so we focus on the debug interrupt.
How to use the interface (HW/SW). We can refer to RISC-V specifications.
If the section is too heavy, promote it to a separate chapter.

Interrupt Interface
~~~~~~~~~~~~~~~~~~~
Desired for step1 verification, but we can likely reuse an E4 DVplan.
How to use the interface (HW/SW). We can refer to RISC-V specifications.
If the section is too heavy, promote it to a separate chapter.

TRI Interface
~~~~~~~~~~~~~
Refer to OpenPiton documents.

.. future file beak

Core Integration
================

RTL Integration
---------------
How to integrate CVA6 into a core complex/SoC
Instantiation template
As in https://docs.openhwgroup.org/projects/cv32e40p-user-manual/integration.html#instantiation-template
Specific constructs
Do we have specific constructs that we should mention for the implementation team:
* Non-reset signals, if any
* Internally controlled asynchronous reset (“SW reset”), if any
* Multi-cycle paths
* Clock gating

ASIC Specific Guidelines
------------------------

Suggested content:
~~~~~~~~~~~~~~~~~~
* How to handle the RAM cells for DFT.
* Typical critical paths in ASIC and suggestions for optimizations (e.g. suggestions for places where to apply regioning/partitioning…)
* We can also have typical command lines / settings for various ASIC tools

FPGA specific guidelines
------------------------
Desired for step1 (we expect prototyping at this stage).

Suggested content:
~~~~~~~~~~~~~~~~~~
* Typical critical paths in FPGA and suggestions for optimizations
* We can also have typical command lines / settings for various FPGA tools

.. future file beak

CV-X-IF Interface and Coprocessor
=================================

CV-X-IF interface specification
-------------------------------
Need to step1 verification. TSS/Guillaume will do.
Refer to the CV-X-IF specification, mention the 3 supported protocol interfaces, identify the CVA6 specific features.

How to use CV-X-IF with CVA6
----------------------------
We don’t commit yet to write this section. We expect the audience to be power users.
Use CVA6 without CV-X-IF interface
Use CVA6 with CV-X-IF interface
How to design a coprocessor for the CV-X-IF interface
How to program a CV-X-IF coprocessor

