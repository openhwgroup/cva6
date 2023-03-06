..
   Copyright 2022 Thales DIS design services SAS
   Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
   You may obtain a copy of the License at https://solderpad.org/licenses/

   Original Author: Jean-Roch COULON - Thales

.. _CV32A6_INTRO:

Introduction
=============

The OpenHW Group uses `semantic versioning <https://semver.org/>`_ to describe the release status of its IP.
This document describes v0.1.0 of the CV32A6.
This is not intended to be a formal release of CVA6.
Currently, the first planned release of CVA6 is the CV32A6 v0.2.0.

CVA6 is a 6-stage in-order and single issue processor core which implements the RISC-V instruction set.
CVA6 can be configured as a 32- or 64-bit core (RV32 or RV64), called CV32A6 or CV64A6.
This document describes an initial version (v0.1.0) of the CV32A6 processor configuration.

The objective of this document is to provide enough information to allow the RTL modification (by designers) and the RTL verification (by verificators).
This document is not dedicated to CVA6 users looking for information to develop software like instructions or registers.

The CVA6 architecture is illustrated in the following figure extracted from a paper written by F.Zaruba and L.Benini.

.. figure:: ../images/ariane_overview.png
   :name: CVA6 Architecute
   :align: center
   :alt:

   CVA6 Architecture


License
-------

| Copyright 2022 Thales
| Copyright 2018 ETH Zürich and University of Bologna
| SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
| Licensed under the Solderpad Hardware License v 2.1 (the “License”);
  you may not use this file except in compliance with the License, or,
  at your option, the Apache License version 2.0. You may obtain a copy
  of the License at https://solderpad.org/licenses/SHL-2.1/.
| Unless required by applicable law or agreed to in writing, any work
  distributed under the License is distributed on an “AS IS” BASIS,
  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
  implied. See the License for the specific language governing
  permissions and limitations under the License.


Standards Compliance
--------------------

To ease the reading, the reference to these specifications can be implicit in the requirements below. For the sake of precision, the requirements identify the versions of RISC-V extensions from these specifications.

* **[CVA6req]** “CVA6 requirement specification”, https://github.com/openhwgroup/cva6/blob/master/docs/specifications/cva6_requirement_specification.rst, HASH#767c465.
* **[RVunpriv]** “The RISC-V Instruction Set Manual, Volume I: User-Level ISA, Document Version 20191213”, Editors Andrew Waterman and Krste Asanović, RISC-V Foundation, December 13, 2019.
* **[RVpriv]** “The RISC-V Instruction Set Manual, Volume II: Privileged Architecture, Document Version 20211203”, Editors Andrew Waterman, Krste Asanović and John Hauser, RISC-V Foundation, December 4, 2021.
* **[RVdbg]** “RISC-V External Debug Support, Document Version 0.13.2”, Editors Tim Newsome and Megan Wachs, RISC-V Foundation, March 22, 2019.
* **[RVcompat]** “RISC-V Architectural Compatibility Test Framework”, https://github.com/riscv-non-isa/riscv-arch-test.
* **[AXI]** AXI Specification, https://developer.arm.com/documentation/ihi0022/hc.
* **[CV-X-IF]** Placeholder for the CV-X-IF coprocessor interface currently prepared at OpenHW Group; current version in https://docs.openhwgroup.org/projects/openhw-group-core-v-xif/.
* **[OpenPiton]** “OpenPiton Microarchitecture Specification”, Princeton University, https://parallel.princeton.edu/openpiton/docs/micro_arch.pdf.

CV32A6 is a standards-compliant 32-bit processor fully compliant with RISC-V specifications: [RVunpriv], [RVpriv] and [RVdbg] and passes [RVcompat] compatibility tests, as requested by [GEN-10] in [CVA6req].


Documentation framework
-----------------------

The framework of this document is inspired by the Common Criteria. The Common Criteria for Information Technology Security Evaluation (referred to as Common Criteria or CC) is an international standard (ISO/IEC 15408) for computer security certification.

Description of the framework:

* Processor is split into module corresponding to the main modules of the design
* Modules can contain several modules
* Each module is described in a chapter, which contains the following subchapters: *Description*, *Functionalities*, *Architecture and Modules* and *Registers* (if any)
* The subchapter *Description* describes the main features of the submodule, the interconnections between the current module and the others and the inputs/outputs interface.
* The subchapter *Functionality* lists in details the module functionalities. Please avoid using the RTL signal names to explain the functionalities.
* The subchapter *Architecture and Modules* provides a drawing to present the module hierarchy, then the functionalities covered by the module
* The subchapter *Registers* specifies the module registers if any


Contributors
------------

| Jean-Roch Coulon - Thales
| Ayoub Jalali
  (`ayoub.jalali@external.thalesgroup.com <mailto:ayoub.jalali@external.thalesgroup.com>`__)
| Alae Eddine Ezzejjari
  (`alae-eddine.ez-zejjari@external.thalesgroup.com <mailto:alae-eddine.ez-zejjari@external.thalesgroup.com>`__)

[TO BE COMPLETED]

