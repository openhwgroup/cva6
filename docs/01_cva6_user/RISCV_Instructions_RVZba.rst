..
   Copyright (c) 2023 OpenHW Group
   Copyright (c) 2023 10xEngineers

   SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1

.. Level 1
   =======

   Level 2
   -------

   Level 3
   ~~~~~~~

   Level 4
   ^^^^^^^

.. _cva6_riscv_instructions_RV32Zba:

*Applicability of this chapter to configurations:*

.. csv-table::
   :widths: auto
   :align: left
   :header: "Configuration", "Implementation"

   "CV32A60AX", "Implemented extension"
   "CV32A60X", "Implemented extension"

   
======================================
RVZba: Address generation instructions
======================================
The Zba instructions can be used to accelerate the generation of addresses that index into arrays of basic types (halfword, word, doubleword) using both unsigned word-sized and XLEN-sized indices: a shifted index is added to a base address.

The shift and add instructions do a left shift of 1, 2, or 3 because these are commonly found in real-world code and because they can be implemented with a minimal amount of additional hardware beyond that of the simple adder. This avoids lengthening the critical path in implementations.

While the shift and add instructions are limited to a maximum left shift of 3, the slli instruction (from the base ISA) can be used to perform similar shifts for indexing into arrays of wider elements. The slli.uw — added in this extension — can be used when the index is to be interpreted as an unsigned word.

The following instructions (and pseudoinstructions) comprise the Zba extension:

+-----------+-----------+-----------------------+
| RV32      | RV64      | Mnemonic              |
+===========+===========+=======================+
|           | ✔         | add.uw rd, rs1, rs2   |
+-----------+-----------+-----------------------+
| ✔         | ✔         | sh1add rd, rs1, rs2   |
+-----------+-----------+-----------------------+
|           | ✔         | sh1add.uw rd, rs1, rs2|
+-----------+-----------+-----------------------+
| ✔         | ✔         | sh2add rd, rs1, rs2   |
+-----------+-----------+-----------------------+
|           | ✔         | sh2add.uw rd, rs1, rs2|
+-----------+-----------+-----------------------+
| ✔         | ✔         | sh3add rd, rs1, rs2   |
+-----------+-----------+-----------------------+
|           | ✔         | sh3add.uw rd, rs1, rs2|
+-----------+-----------+-----------------------+
|           | ✔         | slli.uw rd, rs1, imm  |
+-----------+-----------+-----------------------+

RV32 and RV64 Instructions
--------------------------


- **SH1ADD**: Shift left by 1 and add

    **Format**: sh1add rd, rs1, rs2

    **Description**: This instruction shifts rs1 to the left by 1 bit and adds it to rs2.

    **Pseudocode**: X(rd) = X(rs2) + (X(rs1) << 1)

    **Invalid values**: NONE

    **Exception raised**: NONE

- **SH2ADD**: Shift left by 2 and add

    **Format**: sh2add rd, rs1, rs2

    **Description**: This instruction shifts rs1 to the left by 2 bit and adds it to rs2.

    **Pseudocode**: X(rd) = X(rs2) + (X(rs1) << 2)

    **Invalid values**: NONE

    **Exception raised**: NONE

- **SH3ADD**: Shift left by 3 and add

    **Format**: sh3add rd, rs1, rs2

    **Description**: This instruction shifts rs1 to the left by 3 bit and adds it to rs2.

    **Pseudocode**: X(rd) = X(rs2) + (X(rs1) << 3)

    **Invalid values**: NONE

    **Exception raised**: NONE    


RV64 specific instructions
--------------------------

- **ADD.UW**: Add unsigned word

    **Format**: add.uw rd, rs1, rs2

    **Description**: This instruction performs an XLEN-wide addition between rs2 and the zero-extended least-significant word of rs1.

    **Pseudocode**: X(rd) = rs2 + EXTZ(X(rs1)[31..0])

    **Invalid values**: NONE

    **Exception raised**: NONE

- **SH1ADD.UW**: Shift unsigned word left by 1 and add

    **Format**: sh1add.uw rd, rs1, rs2

    **Description**: This instruction performs an XLEN-wide addition of two addends. The first addend is rs2. The second addend is the unsigned value formed by extracting the least-significant word of rs1 and shifting it left by 1 place.

    **Pseudocode**: X(rd) = rs2 + (EXTZ(X(rs1)[31..0]) << 1)

    **Invalid values**: NONE

    **Exception raised**: NONE

- **SH2ADD.UW**: Shift unsigned word left by 2 and add

    **Format**: sh2add.uw rd, rs1, rs2

    **Description**: This instruction performs an XLEN-wide addition of two addends. The first addend is rs2. The second addend is the unsigned value formed by extracting the least-significant word of rs1 and shifting it left by 2 places.

    **Pseudocode**: X(rd) = rs2 + (EXTZ(X(rs1)[31..0]) << 2)

    **Invalid values**: NONE

    **Exception raised**: NONE

- **SH3ADD.UW**: Shift unsigned word left by 3 and add

    **Format**: sh3add.uw rd, rs1, rs2

    **Description**: This instruction performs an XLEN-wide addition of two addends. The first addend is rs2. The second addend is the unsigned value formed by extracting the least-significant word of rs1 and shifting it left by 3 places.

    **Pseudocode**: X(rd) = rs2 + (EXTZ(X(rs1)[31..0]) << 3)

    **Invalid values**: NONE

    **Exception raised**: NONE

- **SLLI.UW**: Shift-left unsigned word (Immediate)

    **Format**: slli.uw rd, rs1, imm

    **Description**: This instruction takes the least-significant word of rs1, zero-extends it, and shifts it left by the immediate.

    **Pseudocode**: X(rd) = (EXTZ(X(rs)[31..0]) << imm)

    **Invalid values**: NONE

    **Exception raised**: NONE   
