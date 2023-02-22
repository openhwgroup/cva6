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

.. _cva6_user_guide_introduction:

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

