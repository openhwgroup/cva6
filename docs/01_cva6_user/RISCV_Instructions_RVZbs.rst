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

.. _cva6_riscv_instructions_RV32Zbs:

*Applicability of this chapter to configurations:*

.. csv-table::
   :widths: auto
   :align: left
   :header: "Configuration", "Implementation"

   "CV32A60AX", "Implemented extension"
   "CV32A60X", "Implemented extension"

   
==============================
RVZbs: Single-bit instructions
==============================
The single-bit instructions provide a mechanism to set, clear, invert, or extract a single bit in a register. The bit is specified by its index.

The following instructions (and pseudoinstructions) comprise the Zbs extension:

+-----------+-----------+-----------------------+
| RV32      | RV64      | Mnemonic              |
+===========+===========+=======================+
| ✔         | ✔         | bclr rd, rs1, rs2     |
+-----------+-----------+-----------------------+
| ✔         | ✔         | bclri rd, rs1, imm    |
+-----------+-----------+-----------------------+
| ✔         | ✔         | bext rd, rs1, rs2     |
+-----------+-----------+-----------------------+
| ✔         | ✔         | bexti rd, rs1, imm    |
+-----------+-----------+-----------------------+
| ✔         | ✔         | binv rd, rs1, rs2     |
+-----------+-----------+-----------------------+
| ✔         | ✔         | binvi rd, rs1, imm    |
+-----------+-----------+-----------------------+
| ✔         | ✔         | bset rd, rs1, rs2     |
+-----------+-----------+-----------------------+
| ✔         | ✔         | bseti rd, rs1, imm    |
+-----------+-----------+-----------------------+

RV32 and RV64 Instructions
--------------------------

- **BCLR**: Single-Bit Clear (Register)

    **Format**: bclr rd, rs1, rs2

    **Description**: This instruction returns rs1 with a single bit cleared at the index specified in rs2. The index is read from the lower log2(XLEN) bits of rs2.

    **Pseudocode**: X(rd) = X(rs1) & ~(1 << (X(rs2) & (XLEN - 1)))

    **Invalid values**: NONE

    **Exception raised**: NONE

- **BCLRI**: Single-Bit Clear (Immediate)

    **Format**: bclri rd, rs1, shamt

    **Description**: This instruction returns rs1 with a single bit cleared at the index specified in shamt. The index is read from the lower log2(XLEN) bits of shamt. For RV32, the encodings corresponding to shamt[5]=1 are reserved.

    **Pseudocode**: X(rd) = X(rs1) & ~(1 << (shamt & (XLEN - 1)))

    **Invalid values**: NONE

    **Exception raised**: NONE

- **BEXT**: Single-Bit Extract (Register)

    **Format**: bext rd, rs1, rs2

    **Description**: This instruction returns a single bit extracted from rs1 at the index specified in rs2. The index is read from the lower log2(XLEN) bits of rs2.

    **Pseudocode**: X(rd) = (X(rs1) >> (X(rs2) & (XLEN - 1))) & 1

    **Invalid values**: NONE

    **Exception raised**: NONE

- **BEXTI**: Single-Bit Extract (Immediate)

    **Format**: bexti rd, rs1, shamt

    **Description**: This instruction returns a single bit extracted from rs1 at the index specified in rs2. The index is read from the lower log2(XLEN) bits of shamt. For RV32, the encodings corresponding to shamt[5]=1 are reserved.

    **Pseudocode**: X(rd) = (X(rs1) >> (shamt & (XLEN - 1))) & 1

    **Invalid values**: NONE

    **Exception raised**: NONE

- **BINV**: Single-Bit Invert (Register)

    **Format**: binv rd, rs1, rs2

    **Description**: This instruction returns rs1 with a single bit inverted at the index specified in rs2. The index is read from the lower log2(XLEN) bits of rs2.

    **Pseudocode**: X(rd) = X(rs1) ^ (1 << (X(rs2) & (XLEN - 1)))

    **Invalid values**: NONE

    **Exception raised**: NONE

- **BINVI**: Single-Bit Invert (Immediate)

    **Format**: binvi rd, rs1, shamt

    **Description**: This instruction returns rs1 with a single bit inverted at the index specified in shamt. The index is read from the lower log2(XLEN) bits of shamt. For RV32, the encodings corresponding to shamt[5]=1 are reserved.

    **Pseudocode**: X(rd) = X(rs1) ^ (1 << (shamt & (XLEN - 1)))

    **Invalid values**: NONE

    **Exception raised**: NONE    

- **BSET**: Single-Bit Set (Register)

    **Format**: bset rd, rs1, rs2

    **Description**: This instruction returns rs1 with a single bit set at the index specified in rs2. The index is read from the lower log2(XLEN) bits of rs2.

    **Pseudocode**: X(rd) = X(rs1) | (1 << (X(rs2) & (XLEN - 1)))

    **Invalid values**: NONE

    **Exception raised**: NONE

- **BSETI**: Single-Bit Set (Immediate)

    **Format**: bseti rd, rs1, shamt

    **Description**: This instruction returns rs1 with a single bit set at the index specified in shamt. The index is read from the lower log2(XLEN) bits of shamt. For RV32, the encodings corresponding to shamt[5]=1 are reserved.

    **Pseudocode**: X(rd) = X(rs1) | (1 << (shamt & (XLEN - 1)))

    **Invalid values**: NONE

    **Exception raised**: NONE     

    

