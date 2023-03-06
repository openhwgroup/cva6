
..
   Copyright 2022 Thales DIS design services SAS
   Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
   You may obtain a copy of the License at https://solderpad.org/licenses/

   Original Author: Jean-Roch COULON - Thales

.. _DVPLAN_INTRO:

Introduction
=============

The objective of this document is to describe what must be covered to verify CVA6 RISC-V processor.


License
-------

| Copyright 2022 Thales
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
* **[CVA6design]** “CVA6 design document”, TO BE COMPLETED
* **[RVunpriv]** “The RISC-V Instruction Set Manual, Volume I: User-Level ISA, Document Version 20191213”, Editors Andrew Waterman and Krste Asanović, RISC-V Foundation, December 13, 2019.
* **[RVpriv]** “The RISC-V Instruction Set Manual, Volume II: Privileged Architecture, Document Version 20211203”, Editors Andrew Waterman, Krste Asanović and John Hauser, RISC-V Foundation, December 4, 2021.
* **[RVdbg]** “RISC-V External Debug Support, Document Version 0.13.2”, Editors Tim Newsome and Megan Wachs, RISC-V Foundation, March 22, 2019.
* **[RVcompat]** “RISC-V Architectural Compatibility Test Framework”, https://github.com/riscv-non-isa/riscv-arch-test.
* **[AXI]** AXI Specification, https://developer.arm.com/documentation/ihi0022/hc.
* **[CV-X-IF]** Placeholder for the CV-X-IF coprocessor interface currently prepared at OpenHW Group; current version in https://docs.openhwgroup.org/projects/openhw-group-core-v-xif/.
* **[OpenPiton]** “OpenPiton Microarchitecture Specification”, Princeton University, https://parallel.princeton.edu/openpiton/docs/micro_arch.pdf.

CV32A6 is a 32-bit processor fully compliant with RISC-V specifications: [RVunpriv], [RVpriv] and [RVdbg] and passes [RVcompat] compatibility tests, as requested by [GEN-10] in [CVA6req].


Getting start verification
--------------------------

[TO BE COMPLETED]


Documentation framework
-----------------------

The framework of this document is aligned with the CVA6 design document [CVA6design].

Description of the framework:

* Processor is a subsystem
* Processor subsystems are split into several modules
* Modules are verified separately


Contributors
------------

| Jean-Roch Coulon - Thales

[TO BE COMPLETED]

