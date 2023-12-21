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

.. _cva6_riscv_instructions_RV32M:

*Applicability of this chapter to configurations:*

This chapter is applicable to all CV32A6 configurations.

.. csv-table::
   :widths: auto
   :align: left
   :header: "Configuration", "Implementation"

   "CV32A60AX", "Implemented extension"
   "CV32A60X", "Implemented extension"

**Note**: CV64A6 implements RV64M that includes additional instructions.


RV32M Multiplication and Division Instructions
------------------------------------------------------

This chapter describes the standard integer multiplication and division instruction extension, which
is named “M” and contains instructions that multiply or divide values held in two integer registers.

Multiplication Operations
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

- **MUL**: Multiplication

    **Format**: mul rd, rs1, rs2

    **Description**: performs a 32-bit × 32-bit multiplication and places the lower 32 bits in the destination register (Both rs1 and rs2 treated as signed numbers).

    **Pseudocode**: x[rd] = x[rs1] * x[rs2]

    **Invalid values**: NONE

    **Exception raised**: NONE

- **MULH**: Multiplication Higher

    **Format**: mulh rd, rs1, rs2

    **Description**: performs a 32-bit × 32-bit multiplication and places the upper 32 bits in the destination register of the 64-bit product (Both rs1 and rs2 treated as signed numbers).

    **Pseudocode**: x[rd] = (x[rs1] s*s x[rs2]) >>s 32

    **Invalid values**: NONE

    **Exception raised**: NONE

- **MULHU**: Multiplication Higher Unsigned

    **Format**: mulhu rd, rs1, rs2

    **Description**: performs a 32-bit × 32-bit multiplication and places the upper 32 bits in the destination register of the 64-bit product (Both rs1 and rs2 treated as unsigned numbers).

    **Pseudocode**: x[rd] = (x[rs1] u*u x[rs2]) >>u 32

    **Invalid values**: NONE

    **Exception raised**: NONE

- **MULHSU**: Multiplication Higher Signed Unsigned

    **Format**: mulhsu rd, rs1, rs2

    **Description**: performs a 32-bit × 32-bit multiplication and places the upper 32 bits in the destination register of the 64-bit product (rs1 treated as signed number, rs2 treated as unsigned number).

    **Pseudocode**: x[rd] = (x[rs1] s*u x[rs2]) >>s 32

    **Invalid values**: NONE

    **Exception raised**: NONE

Division Operations
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

- **DIV**: Division

    **Format**: div rd, rs1, rs2

    **Description**: perform signed integer division of 32 bits by 32 bits (rounding towards zero).

    **Pseudocode**: x[rd] = x[rs1] /s x[rs2]

    **Invalid values**: NONE

    **Exception raised**: NONE

- **DIVU**: Division Unsigned

    **Format**: divu rd, rs1, rs2

    **Description**: perform unsigned integer division of 32 bits by 32 bits (rounding towards zero).

    **Pseudocode**: x[rd] = x[rs1] /u x[rs2]

    **Invalid values**: NONE

    **Exception raised**: NONE

- **REM**: Remain

    **Format**: rem rd, rs1, rs2

    **Description**: provide the remainder of the corresponding division operation DIV (the sign of rd equals the sign of rs1).

    **Pseudocode**: x[rd] = x[rs1] %s x[rs2]

    **Invalid values**: NONE

    **Exception raised**: NONE

- **REMU**: Remain Unsigned

    **Format**: rem rd, rs1, rs2

    **Description**: provide the remainder of the corresponding division operation DIVU.

    **Pseudocode**: x[rd] = x[rs1] %u x[rs2]

    **Invalid values**: NONE

    **Exception raised**: NONE

