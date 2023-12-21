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

.. _cva6_riscv_instructions_RV32C:

*Applicability of this chapter to configurations:*

.. csv-table::
   :widths: auto
   :align: left
   :header: "Configuration", "Implementation"

   "CV32A60AX", "Implemented extension"
   "CV32A60X", "Implemented extension"

**Note**: This chapter is specific to CV32A6 configurations. CV64A6 configurations implement as an option RV64C, that includes a different list of instructions.
   

RV32C Compressed Instructions
-----------------------------

RVC uses a simple compression scheme that offers shorter 16-bit versions of common 32-bit RISC-V
instructions when:

    • the immediate or address offset is small;
    • one of the registers is the zero register (x0), the ABI link register (x1), or the ABI stack pointer (x2);
    • the destination register and the first source register are identical;
    • the registers used are the 8 most popular ones.

The C extension is compatible with all other standard instruction extensions. The C extension
allows 16-bit instructions to be freely intermixed with 32-bit instructions, with the latter now able
to start on any 16-bit boundary. With the addition of the C extension, JAL and JALR instructions
will no longer raise an instruction misaligned exception.

Integer Computational Instructions
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

- **C.LI**: Compressed Load Immediate

    **Format**: c.li rd, imm[5:0]

    **Description**: loads the sign-extended 6-bit immediate, imm, into register rd.

    **Pseudocode**: x[rd] = sext(imm[5:0])

    **Invalid values**: rd = x0

    **Exception raised**: NONE

- **C.LUI**: Compressed Load Upper Immediate

    **Format**: c.lui rd, nzimm[17:12]

    **Description**: loads the non-zero 6-bit immediate field into bits 17–12 of the destination register, clears the bottom 12 bits, and sign-extends bit 17 into all higher bits of the destination.

    **Pseudocode**: x[rd] = sext(nzimm[17:12] << 12)

    **Invalid values**: rd = x0 & rd = x2 & nzimm = 0

    **Exception raised**: NONE

- **C.ADDI**: Compressed Addition Immediate

    **Format**: c.addi rd, nzimm[5:0]

    **Description**: adds the non-zero sign-extended 6-bit immediate to the value in register rd then writes the result to rd.

    **Pseudocode**: x[rd] = x[rd] + sext(nzimm[5:0])

    **Invalid values**: rd = x0 & nzimm = 0

    **Exception raised**: NONE

- **C.ADDI16SP**: Addition Immediate Scaled by 16, to Stack Pointer

    **Format**: c.addi16sp nzimm[9:4]

    **Description**: adds the non-zero sign-extended 6-bit immediate to the value in the stack pointer (sp=x2), where the immediate is scaled to represent multiples of 16 in the range (-512,496). C.ADDI16SP is used to adjust the stack pointer in procedure prologues and epilogues. C.ADDI16SP shares the opcode with C.LUI, but has a destination field of x2.

    **Pseudocode**: x[2] = x[2] + sext(nzimm[9:4])

    **Invalid values**: rd != x2 & nzimm = 0

    **Exception raised**: NONE

- **C.ADDI4SPN**: Addition Immediate Scaled by 4, to Stack Pointer

    **Format**: c.addi4spn rd', nzimm[9:2]

    **Description**: adds a zero-extended non-zero immediate, scaled by 4, to the stack pointer, x2, and writes the result to rd'. This instruction is used to generate pointers to stack-allocated variables.

    **Pseudocode**: x[8 + rd'] = x[2] + zext(nzimm[9:2])

    **Invalid values**: nzimm = 0

    **Exception raised**: NONE

- **C.SLLI**: Compressed Shift Left Logic Immediate

    **Format**: c.slli rd, uimm[5:0]

    **Description**: performs a logical left shift (zeros are shifted into the lower bits).

    **Pseudocode**: x[rd] = x[rd] << uimm[5:0]

    **Invalid values**: rd = x0 & uimm[5] = 0

    **Exception raised**: NONE

- **C.SRLI**: Compressed Shift Right Logic Immediate

    **Format**: c.srli rd', uimm[5:0]

    **Description**: performs a logical right shift (zeros are shifted into the upper bits).

    **Pseudocode**: x[8 + rd'] = x[8 + rd'] >> uimm[5:0]

    **Invalid values**: uimm[5] = 0

    **Exception raised**: NONE

- **C.SRAI**: Compressed Shift Right Arithmetic Immediate

    **Format**: c.srai rd', uimm[5:0]

    **Description**: performs an arithmetic right shift (sign bits are shifted into the upper bits).

    **Pseudocode**: x[8 + rd'] = x[8 + rd'] >>s uimm[5:0]

    **Invalid values**: uimm[5] = 0

    **Exception raised**: NONE

- **C.ANDI**: Compressed AND Immediate

    **Format**: c.andi rd', imm[5:0]

    **Description**: computes the bitwise AND of the value in register rd', and the sign-extended 6-bit immediate, then writes the result to rd'.

    **Pseudocode**: x[8 + rd'] = x[8 + rd'] & sext(imm[5:0])

    **Invalid values**: NONE

    **Exception raised**: NONE

- **C.ADD**: Compressed Addition

    **Format**: c.add rd, rs2

    **Description**: adds the values in registers rd and rs2 and writes the result to register rd.

    **Pseudocode**: x[rd] = x[rd] + x[rs2]

    **Invalid values**: rd = x0 & rs2 = x0

    **Exception raised**: NONE

- **C.MV**: Move

    **Format**: c.mv rd, rs2

    **Description**: copies the value in register rs2 into register rd.

    **Pseudocode**: x[rd] = x[rs2]

    **Invalid values**: rd = x0 & rs2 = x0

    **Exception raised**: NONE

- **C.AND**: Compressed AND

    **Format**: c.and rd', rs2'

    **Description**: computes the bitwise AND of of the value in register rd', and register rs2', then writes the result to rd'.

    **Pseudocode**: x[8 + rd'] = x[8 + rd'] & x[8 + rs2']

    **Invalid values**: NONE

    **Exception raised**: NONE

- **C.OR**: Compressed OR

    **Format**: c.or rd', rs2'

    **Description**: computes the bitwise OR of of the value in register rd', and register rs2', then writes the result to rd'.

    **Pseudocode**: x[8 + rd'] = x[8 + rd'] | x[8 + rs2']

    **Invalid values**: NONE

    **Exception raised**: NONE

- **C.XOR**: Compressed XOR

    **Format**: c.and rd', rs2'

    **Description**: computes the bitwise XOR of of the value in register rd', and register rs2', then writes the result to rd'.

    **Pseudocode**: x[8 + rd'] = x[8 + rd'] ^ x[8 + rs2']

    **Invalid values**: NONE

    **Exception raised**: NONE

- **C.SUB**: Compressed Subtraction

    **Format**: c.sub rd', rs2'

    **Description**: subtracts the value in registers rs2' from value in rd' and writes the result to register rd'.

    **Pseudocode**: x[8 + rd'] = x[8 + rd'] - x[8 + rs2']

    **Invalid values**: NONE

    **Exception raised**: NONE

- **C.EBREAK**: Compressed Ebreak

    **Format**: c.ebreak

    **Description**: cause control to be transferred back to the debugging environment.

    **Pseudocode**: RaiseException(Breakpoint)

    **Invalid values**: NONE

    **Exception raised**: Raise a Breakpoint exception.

Control Transfer Instructions
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

- **C.J**: Compressed Jump

    **Format**: c.j imm[11:1]

    **Description**: performs an unconditional control transfer. The offset is sign-extended and added to the pc to form the jump target address.

    **Pseudocode**: pc += sext(imm[11:1])

    **Invalid values**: NONE

    **Exception raised**: jumps to an unaligned address (4-byte or 2-byte boundary) will usually raise an exception.

- **C.JAL**: Compressed Jump and Link

    **Format**: c.jal imm[11:1]

    **Description**: performs the same operation as C.J, but additionally writes the address of the instruction following the jump (pc+2) to the link register, x1.

    **Pseudocode**: x[1] = pc+2; pc += sext(imm[11:1])

    **Invalid values**: NONE

    **Exception raised**: jumps to an unaligned address (4-byte or 2-byte boundary) will usually raise an exception.

- **C.JR**: Compressed Jump Register

    **Format**: c.jr rs1

    **Description**: performs an unconditional control transfer to the address in register rs1.

    **Pseudocode**: pc = x[rs1]

    **Invalid values**: rs1 = x0

    **Exception raised**: jumps to an unaligned address (4-byte or 2-byte boundary) will usually raise an exception.

- **C.JALR**: Compressed Jump and Link Register

    **Format**: c.jalr rs1

    **Description**: performs the same operation as C.JR, but additionally writes the address of the instruction following the jump (pc+2) to the link register, x1.

    **Pseudocode**: t = pc+2; pc = x[rs1]; x[1] = t

    **Invalid values**: rs1 = x0

    **Exception raised**: jumps to an unaligned address (4-byte or 2-byte boundary) will usually raise an exception.

- **C.BEQZ**: Branch if Equal Zero

    **Format**: c.beqz rs1', imm[8:1]

    **Description**: performs conditional control transfers. The offset is sign-extended and added to the pc to form the branch target address. C.BEQZ takes the branch if the value in register rs1' is zero.

    **Pseudocode**: if (x[8+rs1'] == 0) pc += sext(imm[8:1])

    **Invalid values**: NONE

    **Exception raised**: no instruction fetch misaligned exception is generated for a conditional branch that is not taken. An Instruction address misaligned exception is raised if the target address is not aligned on 4-byte or 2-byte boundary, because the core supports compressed instructions.

- **C.BNEZ**: Branch if Not Equal Zero

    **Format**: c.bnez rs1', imm[8:1]

    **Description**: performs conditional control transfers. The offset is sign-extended and added to the pc to form the branch target address. C.BEQZ takes the branch if the value in register rs1' isn't zero.

    **Pseudocode**: if (x[8+rs1'] != 0) pc += sext(imm[8:1])

    **Invalid values**: NONE

    **Exception raised**: no instruction fetch misaligned exception is generated for a conditional branch that is not taken. An Instruction address misaligned exception is raised if the target address is not aligned on 4-byte or 2-byte boundary, because the core supports compressed instructions.

Load and Store Instructions
^^^^^^^^^^^^^^^^^^^^^^^^^^^

- **C.LWSP**: Load Word Stack-Pointer

    **Format**: c.lwsp rd, uimm(x2)

    **Description**: loads a 32-bit value from memory into register rd. It computes an effective address by adding the zero-extended offset, scaled by 4, to the stack pointer, x2.

    **Pseudocode**: x[rd] = M[x[2] + zext(uimm[7:2])][31:0]

    **Invalid values**: rd = x0

    **Exception raised**: loads with a destination of x0 must still raise any exceptions, also an exception if the memory address isn't aligned (4-byte boundary).

- **C.SWSP**: Store Word Stack-Pointer

    **Format**: c.swsp rd, uimm(x2)

    **Description**: stores a 32-bit value in register rs2 to memory. It computes an effective address by adding the zero-extended offset, scaled by 4, to the stack pointer, x2.

    **Pseudocode**: M[x[2] + zext(uimm[7:2])][31:0] = x[rs2]

    **Invalid values**: NONE

    **Exception raised**: an exception raised if the memory address isn't aligned (4-byte boundary).

- **C.LW**: Compressed Load Word

    **Format**: c.lw rd', uimm(rs1')

    **Description**: loads a 32-bit value from memory into register rd'. It computes an effective address by adding the zero-extended offset, scaled by 4, to the base address in register rs1'.

    **Pseudocode**: x[8+rd'] = M[x[8+rs1'] + zext(uimm[6:2])][31:0])

    **Invalid values**: NONE

    **Exception raised**: an exception raised if the memory address isn't aligned (4-byte boundary).

- **C.SW**: Compressed Store Word

    **Format**: c.sw rs2', uimm(rs1')

    **Description**: stores a 32-bit value from memory into register rd'. It computes an effective address by adding the zero-extended offset, scaled by 4, to the base address in register rs1'.

    **Pseudocode**: M[x[8+rs1'] + zext(uimm[6:2])][31:0] = x[8+rs2']

    **Invalid values**: NONE

    **Exception raised**: an exception raised if the memory address isn't aligned (4-byte boundary).

