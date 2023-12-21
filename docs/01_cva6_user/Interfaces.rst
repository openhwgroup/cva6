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
The AXI interface is described in a separate chapter.

*Applicability to configurations:*

.. csv-table::
   :widths: auto
   :align: left
   :header: "Configuration", "Implementation"

   "CV32A60AX", "AXI implemented"
   "CV32A60X", "AXI implemented"

Debug Interface
---------------
  The team is looking for a contributor for this section.
  We can likely reuse an E4 DVplan.
  Remember: the debug module (DTM) is not in the scope, so we focus on the debug interrupt.
  How to use the interface (HW/SW). We can refer to RISC-V specifications.
  If the section is too heavy, promote it to a separate chapter.

*Applicability to configurations:*

.. csv-table::
   :widths: auto
   :align: left
   :header: "Configuration", "Implementation"

   "CV32A60AX", "Debug interface implemented"
   "CV32A60X", "No debug interface"

Interrupt Interface
-------------------
  The team is looking for a contributor for this section.
  We can likely reuse an E4 DVplan.
  How to use the interface (HW/SW). We can refer to RISC-V specifications.
  If the section is too heavy, promote it to a separate chapter.

*The interrupt interface is applicable to all configurations.*

TRI Interface
-------------
The TRI interface is exclusive of the AXI interface.

For more information, refer to OpenPiton documents.

*Applicability to configurations:*

.. csv-table::
   :widths: auto
   :align: left
   :header: "Configuration", "Implementation"

   "CV32A60AX", "No TRI interface"
   "CV32A60X", "No TRI interface"
