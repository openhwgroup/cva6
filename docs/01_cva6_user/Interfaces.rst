..
   Copyright (c) 2023 OpenHW Group
   Copyright (c) 2023 Thales

   SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1

.. Level 1
   =======

   Level 2
   -------

   Level 3
   ~~~~~~~

   Level 4
   ^^^^^^^

.. _cva6_interfaces:

Interfaces
==========

AXI Interface
-------------
Need for step1 verification. Already written by MU Electronics.
Focus on the features used by the CVA6 and refer to ARM documentation for the AXI specification (e.g. do not draw the standard chronogram).
Features:
* See requirement specification
* Atomic transactions
* “USER” bus width extension
* Transaction ordering

Debug Interface
---------------
Desired for step1 verification, but we can likely reuse an E4 DVplan.
Remember: the debug module (DTM) is not in the scope, so we focus on the debug interrupt.
How to use the interface (HW/SW). We can refer to RISC-V specifications.
If the section is too heavy, promote it to a separate chapter.

Interrupt Interface
-------------------
Desired for step1 verification, but we can likely reuse an E4 DVplan.
How to use the interface (HW/SW). We can refer to RISC-V specifications.
If the section is too heavy, promote it to a separate chapter.

TRI Interface
-------------
Refer to OpenPiton documents.
