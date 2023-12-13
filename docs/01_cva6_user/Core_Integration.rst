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

.. _cva6_core_integration:

*The team is looking for contributors for this chapter.*

Core Integration
================

RTL Integration
---------------
Suggested content:

How to integrate CVA6 into a core complex/SoC
Instantiation template as in https://docs.openhwgroup.org/projects/cv32e40p-user-manual/integration.html#instantiation-template
Do we have specific constructs that we should mention for the implementation team:

* Non-reset signals, if any
* Internally controlled asynchronous reset (“SW reset”), if any
* Multi-cycle paths
* Clock gating

ASIC Specific Guidelines
------------------------
Suggested content:

* How to handle the RAM cells for DFT.
* Typical critical paths in ASIC and suggestions for optimizations (e.g. suggestions for places where to apply regioning/partitioning…)
* We can also have typical command lines / settings for various ASIC tools

FPGA specific guidelines
------------------------
Also needed for prototyping of ASICs
Suggested content:

* Typical critical paths in FPGA and suggestions for optimizations
* We can also have typical command lines / settings for various FPGA tools
