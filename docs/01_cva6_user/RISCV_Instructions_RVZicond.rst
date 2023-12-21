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

.. _cva6_riscv_instructions_RVZicond:

*Applicability of this chapter to configurations:*

.. csv-table::
   :widths: auto
   :align: left
   :header: "Configuration", "Implementation"

   "CV32A60AX", "Implemented extension"
   "CV32A60X", "Not implemented extension"

**Note**: RV32Zicond and RV64Zicond are identical.


RVZicond Integer Conditional operations
-------------------------------------------

The instructions follow the format for R-type instructions with 3 operands (i.e., 2 source operands and 1 destination operand). Using these instructions, branchless sequences can be implemented (typically in two-instruction sequences) without the need for instruction fusion, special provisions during the decoding of architectural instructions, or other microarchitectural provisions.

- **CZERO.EQZ**: Conditional zero, if condition is equal to zero

    **Format**: czero.eqz rd, rs1, rs2

    **Description**: This instruction behaves as if there is a conditional branch dependent on rs2 being equal to zero, wherein it branches to code that writes a 0 into rd when the equivalence is true, and otherwise falls through to code that moves rs1 into rd.

    **Pseudocode**: if (x[rs2] == 0) x[rd] = 0 else x[rs1]

    **Invalid values**: NONE

    **Exception raised**: NONE

- **CZERO.NEZ**: Conditional zero, if condition is nonzero

    **Format**: czero.nez rd, rs1, rs2

    **Description**: This instruction behaves as if there is a conditional branch dependent on rs2 being not equal to zero, wherein it branches to code that writes a 0 into rd when the equivalence is true, and otherwise falls through to code that moves rs1 into rd

    **Pseudocode**: if (x[rs2] != 0) x[rd] = 0 else x[rs1]

    **Invalid values**: NONE

    **Exception raised**: NONE

