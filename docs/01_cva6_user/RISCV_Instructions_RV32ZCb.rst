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

.. _cva6_riscv_instructions_RV32Zcb:

*Applicability of this chapter to configurations:*

.. csv-table::
   :widths: auto
   :align: left
   :header: "Configuration", "Implementation"

   "CV32A60AX", "Implemented extension"
   "CV32A60X", "Implemented extension"

**Note**: This chapter is specific to CV32A6 configurations. CV64A6 configurations implement as an option RV64Zcb, that includes one additional instruction.
   

RV32Zcb Code Size Reduction Instructions
-----------------------------------------

Zcb belongs to group of extensions called RISC-V Code Size Reduction Extension (Zc*). Zc* has become the superset of Standard C extension adding more 16-bit instructions to the ISA. Zcb includes 16-bit version of additional Integer (I), Multiply (M) and Bit-Manipulation (Zbb) Instructions. 
All the Zcb instructions require at least standard C extension support as pre-requisite, along with M and Zbb extensions for 16-bit version of the respective instructions.

- **C.ZEXT.B**: Compressed Zero Extend Byte

    **Format**: c.zext.b rd'

    **Description**: This instruction takes a single source/destination operand. It zero-extends the least-significant byte of the operand by inserting zeros into all of the bits more significant than 7.

    **Pseudocode**: x[8 + rd'] = zext(x[8 + rd'][7:0])

    **Invalid values**: NONE

    **Exception raised**: NONE

- **C.SEXT.B**: Compressed Sign Extend Byte

    **Format**: c.sext.b rd'

    **Description**: This instruction takes a single source/destination operand. It sign-extends the least-significant byte in the operand by copying the most-significant bit in the byte (i.e., bit 7) to all of the more-significant bits. It also requires Bit-Manipulation (Zbb) extension support.

    **Pseudocode**: x[8 + rd'] = sext(x[8 + rd'][7:0])

    **Invalid values**: NONE

    **Exception raised**: NONE

- **C.ZEXT.H**: Compressed Zero Extend Halfword

    **Format**: c.zext.h rd'

    **Description**: This instruction takes a single source/destination operand. It zero-extends the least-significant halfword of the operand by inserting zeros into all of the bits more significant than 15. It also requires Bit-Manipulation (Zbb) extension support.

    **Pseudocode**: x[8 + rd'] = zext(x[8 + rd'][15:0])

    **Invalid values**: NONE

    **Exception raised**: NONE

- **C.SEXT.H**: Compressed Sign Extend Halfword

    **Format**: c.sext.h rd'

    **Description**: This instruction takes a single source/destination operand. It sign-extends the least-significant halfword in the operand by copying the most-significant bit in the halfword (i.e., bit 15) to all of the more-significant bits.  It also requires Bit-Manipulation (Zbb) extension support.

    **Pseudocode**: x[8 + rd'] = sext(x[8 + rd'][15:0])

    **Invalid values**: NONE

    **Exception raised**: NONE

- **C.NOT**: Compressed Bitwise NOT

    **Format**: c.not rd'

    **Description**: This instruction takes the one’s complement of rd'/rs1' and writes the result to the same register.

    **Pseudocode**: x[8 + rd'] = x[8 + rd'] ^ -1

    **Invalid values**: NONE

    **Exception raised**: NONE

- **C.MUL**: Compressed Multiply

    **Format**: c.mul rd', rs2'

    **Description**: performs a 32-bit × 32-bit multiplication and places the lower 32 bits in the destination register (Both rd' and rs2' treated as signed numbers). It also requires M extension support.

    **Pseudocode**: x[8 + rd'] = (x[8 + rd'] * x[8 + rs2'])[31:0]

    **Invalid values**: NONE

    **Exception raised**: NONE

- **C.LHU**: Compressed Load Halfword Unsigned

    **Format**: c.lhu rd', uimm(rs1')

    **Description**: This instruction loads a halfword from the memory address formed by adding rs1' to the zero extended immediate uimm. The resulting halfword is zero extended and is written to rd'.

    **Pseudocode**: x[8+rd'] = zext(M[x[8+rs1'] + zext(uimm[1])][15:0])

    **Invalid values**: NONE

    **Exception raised**: an exception raised if the memory address isn't aligned (2-byte boundary).

- **C.LH**: Compressed Load Halfword

    **Format**: c.lh rd', uimm(rs1')

    **Description**: This instruction loads a halfword from the memory address formed by adding rs1' to the zero extended immediate uimm. The resulting halfword is sign extended and is written to rd'.

    **Pseudocode**: x[8+rd'] = sext(M[x[8+rs1'] + zext(uimm[1])][15:0])

    **Invalid values**: NONE

    **Exception raised**: an exception raised if the memory address isn't aligned (2-byte boundary).

- **C.LBU**: Compressed Load Byte Unsigned

    **Format**: c.lbu rd', uimm(rs1')

    **Description**: This instruction loads a byte from the memory address formed by adding rs1' to the zero extended immediate uimm. The resulting byte is zero extended and is written to rd'.

    **Pseudocode**: x[8+rd'] = zext(M[x[8+rs1'] + zext(uimm[1:0])][7:0])

    **Invalid values**: NONE

    **Exception raised**: NONE

- **C.SH**: Compressed Store Halfword

    **Format**: c.sh rs2', uimm(rs1')

    **Description**: This instruction stores the least significant halfword of rs2' to the memory address formed by adding rs1' to the zero extended immediate uimm.

    **Pseudocode**: M[x[8+rs1'] + zext(uimm[1])][15:0] = x[8+rs2']

    **Invalid values**: NONE

    **Exception raised**: an exception raised if the memory address isn't aligned (2-byte boundary).

- **C.SB**: Compressed Store Byte

    **Format**: c.sb rs2', uimm(rs1')

    **Description**: This instruction stores the least significant byte of rs2' to the memory address formed by adding rs1' to the zero extended immediate uimm.

    **Pseudocode**: M[x[8+rs1'] + zext(uimm[1:0])][7:0] = x[8+rs2']

    **Invalid values**: NONE

    **Exception raised**: NONE
	