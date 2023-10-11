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

.. _cva6_riscv_instructions:

RISC-V Instructions
===================

Introduction
------------------

In this document, we present ISA (Instruction Set Architecture) for C32VA6_v5.0.0, illustrating different supported instructions, the Base Integer Instruction set RV32I, and also other instructions in some extensions supported by the core as:

* RV32M        – Standard Extension for Integer Multiplication and Division Instructions
* RV32A        – Standard Extension for Atomic Instructions
* RV32C        – Standard Extension for Compressed Instructions
* RV32Zicsr    – Standard Extension for CSR Instructions
* RV32Zifencei – Standard Extension for Instruction-Fetch Fence
* RV32Zicond   – Standard Extension for Integer Conditional Operations

The base RISC-V ISA has fixed-length 32-bit instructions or 16-bit instructions (the C32VA6_v5.0.0 support C extension), so that must be naturally aligned on 4-byte boundary or 2-byte boundary.
The C32VA6_v5.0.0 supports:

* Only 1 hart,
* No misaligned memory accesses.

General purpose registers
--------------------------

As shown in the Table 1.1, there are 31 general-purpose registers x1–x31, which hold integer values. Register x0 is hardwired to the constant 0. There is no hardwired subroutine return address link register, but the standard software calling convention uses register x1 to hold the return address on a call. For C32VA6_v5.0.0, the x registers are 32 bits wide. There is one additional register also 32 bits wide: the program counter pc holds the address of the current instruction.

Table 1.1 shows the general-purpose registers :

.. list-table::
   :widths: 20 20 15 15 20
   :header-rows: 1

   * - **5-bit Encoding (rx)**
     - **3-bit Compressed Encoding (rx')**
     - **Register (ISA name)**
     - **Register (ABI name)**
     - **Description**
   * - 0
     -
     - x0
     - zero
     - Hardwired zero
   * - 1
     -
     - x1
     - ra
     - Return address (link register)
   * - 2
     -
     - x2
     - sp
     - Stack pointer
   * - 3
     -
     - x3
     - gp
     - Global pointer
   * - 4
     -
     - x4
     - tp
     - Thread pointer
   * - 5
     -
     - x5
     - t0
     - Temporaries/alternate link register
   * - 6 - 7
     -
     - x6 - x7
     - t1 - t2
     - Temporaries
   * - 8
     - 0
     - x8
     - s0/fp
     - Saved register/frame pointer
   * - 9
     - 1
     - x9
     - s1
     - Saved registers
   * - 10 - 11
     - 2 - 3
     - x10 - x11
     - a0 - a1
     - Function arguments/return value
   * - 12 - 15
     - 4 - 7
     - x12 - x15
     - a2 - a5
     - Function arguments
   * - 16 - 17
     -
     - x16 - x17
     - a6 - a7
     - Function arguments
   * - 18 - 27
     -
     - x18 - x27
     - s2 - s11
     - Saved registers
   * - 28 - 31
     -
     - x28 - x31
     - t3 - t6
     - Temporaries

Conventions and Terminology
-----------------------------

- **sext(val)**: Sign Extension is the operation of increasing the number of bits of a binary number while preserving the number's sign (positive(0)/negative(1)) and value. this is done by appending digits to the most significant side of the number.

- **zext(val)**: Zero Extension is the operation of increasing the number of bits of a binary number with zeros. this is done by appending digits to the most significant side of the number.

- **<u**: Comparison operation (less than) of 2 unsigned values.

- **>>s**: Right shift of 2 signed values.

- **>>u**: Right shift of 2 unsigned values.

- **M[address]**: Value existe in the address of the memory.

- **/s**: Division of 2 signed values.

- **/u**: Division of 2 unsigned values.

- **%s**: Remainder of the Division of 2 signed values.

- **%u**: Remainder of the Division of 2 unsigned values.

- **AMO32**: Atomic Memory Operation (word).

- **rx'**: rd', rs1' or rs2', stand for the 3-bit Compressed Encoding registers.

RV32I Base Integer Instruction Set
-----------------------------------

This section describes the RV32I base integer instruction set.

Integer Register-Immediate Instructions
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

- **ADDI**: Add Immediate

    **Format**: addi rd, rs1, imm[11:0]

    **Description**: add sign-extended 12-bit immediate to register rs1, and store the result in register rd.

    **Pseudocode**: x[rd] = x[rs1] + sext(imm[11:0])

    **Invalid values**: NONE

    **Exception raised**: NONE

- **ANDI**: AND Immediate

    **Format**: andi rd, rs1, imm[11:0]

    **Description**: perform bitwise AND on register rs1 and the sign-extended 12-bit immediate and place the result in rd.

    **Pseudocode**: x[rd] = x[rs1] & sext(imm[11:0])

    **Invalid values**: NONE

    **Exception raised**: NONE

- **ORI**: OR Immediate

    **Format**: ori rd, rs1, imm[11:0]

    **Description**: perform bitwise OR on register rs1 and the sign-extended 12-bit immediate and place the result in rd.

    **Pseudocode**: x[rd] = x[rs1] | sext(imm[11:0])

    **Invalid values**: NONE

    **Exception raised**: NONE

- **XORI**: XOR Immediate

    **Format**: xori rd, rs1, imm[11:0]

    **Description**: perform bitwise XOR on register rs1 and the sign-extended 12-bit immediate and place the result in rd.

    **Pseudocode**: x[rd] = x[rs1] ^ sext(imm[11:0])

    **Invalid values**: NONE

    **Exception raised**: NONE

- **SLTI**: Set Less Then Immediate

    **Format**: slti rd, rs1, imm[11:0]

    **Description**: set register rd to 1 if register rs1 is less than the sign extended immediate when both are treated as signed numbers, else 0 is written to rd.

    **Pseudocode**: if (x[rs1] < sext(imm[11:0]) x[rd] = 1 else x[rd] = 0

    **Invalid values**: NONE

    **Exception raised**: NONE

- **SLTIU**: Set Less Then Immediate Unsigned

    **Format**: sltiu rd, rs1, imm[11:0]

    **Description**: set register rd to 1 if register rs1 is less than the sign extended immediate when both are treated as unsigned numbers, else 0 is written to rd.

    **Pseudocode**: if (x[rs1] <u sext(imm[11:0]) x[rd] = 1 else x[rd] = 0

    **Invalid values**: NONE

    **Exception raised**: NONE

- **SLLI**: Shift Left Logic Immediate

    **Format**: slli rd, rs1, imm[4:0]

    **Description**: logical left shift (zeros are shifted into the lower bits).

    **Pseudocode**: x[rd] = x[rs1] << imm[4:0]

    **Invalid values**: NONE

    **Exception raised**: NONE

- **SRLI**: Shift Right Logic Immediate

    **Format**: srli rd, rs1, imm[4:0]

    **Description**: logical right shift (zeros are shifted into the upper bits).

    **Pseudocode**: x[rd] = x[rs1] >> imm[4:0]

    **Invalid values**: NONE

    **Exception raised**: NONE

- **SRAI**: Shift Right Arithmetic Immediate

    **Format**: srai rd, rs1, imm[4:0]

    **Description**: arithmetic right shift (the original sign bit is copied into the vacated upper bits).

    **Pseudocode**: x[rd] = x[rs1] >>s imm[4:0]

    **Invalid values**: NONE

    **Exception raised**: NONE

- **LUI**: Load Upper Immediate

    **Format**: lui rd, imm[19:0]

    **Description**: place the immediate value in the top 20 bits of the destination register rd, filling in the lowest 12 bits with zeros.

    **Pseudocode**: x[rd] = sext(imm[31:12] << 12)

    **Invalid values**: NONE

    **Exception raised**: NONE

- **AUIPC**: Add Upper Immediate to PC

    **Format**: auipc rd, imm[19:0]

    **Description**: form a 32-bit offset from the 20-bit immediate, filling in the lowest 12 bits with zeros, adds this offset to the pc, then place the result in register rd.

    **Pseudocode**: x[rd] = pc + sext(immediate[31:12] << 12)

    **Invalid values**: NONE

    **Exception raised**: NONE

Integer Register-Register Instructions
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

- **ADD**: Addition

    **Format**: add rd, rs1, rs2

    **Description**: add rs2 to register rs1, and store the result in register rd.

    **Pseudocode**: x[rd] = x[rs1] + x[rs2]

    **Invalid values**: NONE

    **Exception raised**: NONE

- **SUB**: Subtraction

    **Format**: sub rd, rs1, rs2

    **Description**: subtract rs2 from register rs1, and store the result in register rd.

    **Pseudocode**: x[rd] = x[rs1] - x[rs2]

    **Invalid values**: NONE

    **Exception raised**: NONE

- **AND**: AND logical operator

    **Format**: and rd, rs1, rs2

    **Description**: perform bitwise AND on register rs1 and rs2 and place the result in rd.

    **Pseudocode**: x[rd] = x[rs1] & x[rs2]

    **Invalid values**: NONE

    **Exception raised**: NONE

- **OR**: OR logical operator

    **Format**: or rd, rs1, rs2

    **Description**: perform bitwise OR on register rs1 and rs2 and place the result in rd.

    **Pseudocode**: x[rd] = x[rs1] | x[rs2]

    **Invalid values**: NONE

    **Exception raised**: NONE

- **XOR**: XOR logical operator

    **Format**: xor rd, rs1, rs2

    **Description**: perform bitwise XOR on register rs1 and rs2 and place the result in rd.

    **Pseudocode**: x[rd] = x[rs1] ^ x[rs2]

    **Invalid values**: NONE

    **Exception raised**: NONE

- **SLT**: Set Less Then

    **Format**: slt rd, rs1, rs2

    **Description**: set register rd to 1 if register rs1 is less than rs2 when both are treated as signed numbers, else 0 is written to rd.

    **Pseudocode**: if (x[rs1] < x[rs2]) x[rd] = 1 else x[rd] = 0

    **Invalid values**: NONE

    **Exception raised**: NONE

- **SLTU**: Set Less Then Unsigned

    **Format**: sltu rd, rs1, rs2

    **Description**: set register rd to 1 if register rs1 is less than rs2 when both are treated as unsigned numbers, else 0 is written to rd.

    **Pseudocode**: if (x[rs1] <u x[rs2]) x[rd] = 1 else x[rd] = 0

    **Invalid values**: NONE

    **Exception raised**: NONE

- **SLL**: Shift Left Logic

    **Format**: sll rd, rs1, rs2

    **Description**: logical left shift (zeros are shifted into the lower bits).

    **Pseudocode**: x[rd] = x[rs1] << x[rs2]

    **Invalid values**: NONE

    **Exception raised**: NONE

- **SRL**: Shift Right Logic

    **Format**: srl rd, rs1, rs2

    **Description**: logical right shift (zeros are shifted into the upper bits).

    **Pseudocode**: x[rd] = x[rs1] >> x[rs2]

    **Invalid values**: NONE

    **Exception raised**: NONE

- **SRA**: Shift Right Arithmetic

    **Format**: sra rd, rs1, rs2

    **Description**: arithmetic right shift (the original sign bit is copied into the vacated upper bits).

    **Pseudocode**: x[rd] = x[rs1] >>s x[rs2]

    **Invalid values**: NONE

    **Exception raised**: NONE

Control Transfer Instructions
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

**Unconditional Jumps**

- **JAL**: Jump and Link

    **Format**: jal rd, imm[20:1]

    **Description**: offset is sign-extended and added to the pc to form the jump target address (pc is calculated using signed arithmetic), then setting the least-significant bit of the result to zero, and store the address of instruction following the jump (pc+4) into register rd.

    **Pseudocode**: x[rd] = pc+4; pc += sext(imm[20:1])

    **Invalid values**: NONE

    **Exception raised**: jumps to an unaligned address (4-byte or 2-byte boundary) will usually raise an exception.

- **JALR**: Jump and Link Register

    **Format**: jalr rd, rs1, imm[11:0]

    **Description**: target address is obtained by adding the 12-bit signed immediate to the register rs1 (pc is calculated using signed arithmetic), then setting the least-significant bit of the result to zero, and store the address of instruction following the jump (pc+4) into register rd.

    **Pseudocode**: t = pc+4; pc = (x[rs1]+sext(imm[11:0]))&∼1 ; x[rd] = t

    **Invalid values**: NONE

    **Exception raised**: jumps to an unaligned address (4-byte or 2-byte boundary) will usually raise an exception.

**Conditional Branches**

- **BEQ**: Branch Equal

    **Format**: beq rs1, rs2, imm[12:1]

    **Description**: takes the branch (pc is calculated using signed arithmetic) if registers rs1 and rs2 are equal.

    **Pseudocode**: if (x[rs1] == x[rs2]) pc += sext({imm[12:1], 1’b0}) else pc += 4

    **Invalid values**: NONE

    **Exception raised**: no instruction fetch misaligned exception is generated for a conditional branch that is not taken. An Instruction address misaligned exception is raised if the target address is not aligned on 4-byte or 2-byte boundary, because the core supports compressed instructions.

- **BNE**: Branch Not Equal

    **Format**: bne rs1, rs2, imm[12:1]

    **Description**: takes the branch (pc is calculated using signed arithmetic) if registers rs1 and rs2 are not equal.

    **Pseudocode**: if (x[rs1] != x[rs2]) pc += sext({imm[12:1], 1’b0}) else pc += 4

    **Invalid values**: NONE

    **Exception raised**: no instruction fetch misaligned exception is generated for a conditional branch that is not taken. An Instruction address misaligned exception is raised if the target address is not aligned on 4-byte or 2-byte boundary, because the core supports compressed instructions.

- **BLT**: Branch Less Than

    **Format**: blt rs1, rs2, imm[12:1]

    **Description**: takes the branch (pc is calculated using signed arithmetic) if registers rs1 less than rs2 (using signed comparison).

    **Pseudocode**: if (x[rs1] < x[rs2]) pc += sext({imm[12:1], 1’b0}) else pc += 4

    **Invalid values**: NONE

    **Exception raised**: no instruction fetch misaligned exception is generated for a conditional branch that is not taken. An Instruction address misaligned exception is raised if the target address is not aligned on 4-byte or 2-byte boundary, because the core supports compressed instructions.

- **BLTU**: Branch Less Than Unsigned

    **Format**: bltu rs1, rs2, imm[12:1]

    **Description**: takes the branch (pc is calculated using signed arithmetic) if registers rs1 less than rs2 (using unsigned comparison).

    **Pseudocode**: if (x[rs1] <u x[rs2]) pc += sext({imm[12:1], 1’b0}) else pc += 4

    **Invalid values**: NONE

    **Exception raised**: no instruction fetch misaligned exception is generated for a conditional branch that is not taken. An Instruction address misaligned exception is raised if the target address is not aligned on 4-byte or 2-byte boundary, because the core supports compressed instructions.

- **BGE**: Branch Greater or Equal

    **Format**: bge rs1, rs2, imm[12:1]

    **Description**: takes the branch (pc is calculated using signed arithmetic) if registers rs1 is greater than or equal rs2 (using signed comparison).

    **Pseudocode**: if (x[rs1] >= x[rs2]) pc += sext({imm[12:1], 1’b0}) else pc += 4

    **Invalid values**: NONE

    **Exception raised**: no instruction fetch misaligned exception is generated for a conditional branch that is not taken. An Instruction address misaligned exception is raised if the target address is not aligned on 4-byte or 2-byte boundary, because the core supports compressed instructions.

- **BGEU**: Branch Greater or Equal Unsigned

    **Format**: bgeu rs1, rs2, imm[12:1]

    **Description**: takes the branch (pc is calculated using signed arithmetic) if registers rs1 is greater than or equal rs2 (using unsigned comparison).

    **Pseudocode**: if (x[rs1] >=u x[rs2]) pc += sext({imm[12:1], 1’b0}) else pc += 4

    **Invalid values**: NONE

    **Exception raised**: no instruction fetch misaligned exception is generated for a conditional branch that is not taken. An Instruction address misaligned exception is raised if the target address is not aligned on 4-byte or 2-byte boundary, because the core supports compressed instructions.

Load and Store Instructions
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

- **LB**: Load Byte

    **Format**: lb rd, imm(rs1)

    **Description**: loads a 8-bit value from memory, then sign-extends to 32-bit before storing in rd (rd is calculated using signed arithmetic), the effective address is obtained by adding register rs1 to the sign-extended 12-bit offset.

    **Pseudocode**: x[rd] = sext(M[x[rs1] + sext(imm[11:0])][7:0])

    **Invalid values**: NONE

    **Exception raised**: loads with a destination of x0 must still raise any exceptions and action any other side effects even though the load value is discarded.

- **LH**: Load Halfword

    **Format**: lh rd, imm(rs1)

    **Description**: loads a 16-bit value from memory, then sign-extends to 32-bit before storing in rd (rd is calculated using signed arithmetic), the effective address is obtained by adding register rs1 to the sign-extended 12-bit offset.

    **Pseudocode**: x[rd] = sext(M[x[rs1] + sext(imm[11:0])][15:0])

    **Invalid values**: NONE

    **Exception raised**: loads with a destination of x0 must still raise any exceptions and action any other side effects even though the load value is discarded, also an exception is raised if the memory address isn't aligned (2-byte boundary).

- **LW**: Load Word

    **Format**: lw rd, imm(rs1)

    **Description**: loads a 32-bit value from memory, then storing in rd (rd is calculated using signed arithmetic). The effective address is obtained by adding register rs1 to the sign-extended 12-bit offset.

    **Pseudocode**: x[rd] = sext(M[x[rs1] + sext(imm[11:0])][31:0])

    **Invalid values**: NONE

    **Exception raised**: loads with a destination of x0 must still raise any exceptions and action any other side effects even though the load value is discarded, also an exception is raised if the memory address isn't aligned (4-byte boundary).

- **LBU**: Load Byte Unsigned

    **Format**: lbu rd, imm(rs1)

    **Description**: loads a 8-bit value from memory, then zero-extends to 32-bit before storing in rd (rd is calculated using unsigned arithmetic), the effective address is obtained by adding register rs1 to the sign-extended 12-bit offset.

    **Pseudocode**: x[rd] = zext(M[x[rs1] + sext(imm[11:0])][7:0])

    **Invalid values**: NONE

    **Exception raised**: loads with a destination of x0 must still raise any exceptions and action any other side effects even though the load value is discarded.

- **LHU**: Load Halfword Unsigned

    **Format**: lhu rd, imm(rs1)

    **Description**: loads a 16-bit value from memory, then zero-extends to 32-bit before storing in rd (rd is calculated using unsigned arithmetic), the effective address is obtained by adding register rs1 to the sign-extended 12-bit offset.

    **Pseudocode**: x[rd] = zext(M[x[rs1] + sext(imm[11:0])][15:0])

    **Invalid values**: NONE

    **Exception raised**: loads with a destination of x0 must still raise any exceptions and action any other side effects even though the load value is discarded, also an exception is raised if the memory address isn't aligned (2-byte boundary).

- **SB**: Store Byte

    **Format**: sb rs2, imm(rs1)

    **Description**: stores a 8-bit value from the low bits of register rs2 to memory, the effective address is obtained by adding register rs1 to the sign-extended 12-bit offset.

    **Pseudocode**: M[x[rs1] + sext(imm[11:0])][7:0] = x[rs2][7:0]

    **Invalid values**: NONE

    **Exception raised**: NONE

- **SH**: Store Halfword

    **Format**: sh rs2, imm(rs1)

    **Description**: stores a 16-bit value from the low bits of register rs2 to memory, the effective address is obtained by adding register rs1 to the sign-extended 12-bit offset.

    **Pseudocode**: M[x[rs1] + sext(imm[11:0])][15:0] = x[rs2][15:0]

    **Invalid values**: NONE

    **Exception raised**: an exception is raised if the memory address isn't aligned (2-byte boundary).

- **SW**: Store Word

    **Format**: sw rs2, imm(rs1)

    **Description**: stores a 32-bit value from register rs2 to memory, the effective address is obtained by adding register rs1 to the sign-extended 12-bit offset.

    **Pseudocode**: M[x[rs1] + sext(imm[11:0])][31:0] = x[rs2][31:0]

    **Invalid values**: NONE

    **Exception raised**: an exception is raised if the memory address isn't aligned (4-byte boundary).

Memory Ordering
^^^^^^^^^^^^^^^^^^

- **FENCE**: Fence Instruction

    **Format**: fence pre, succ

    **Description**: order device I/O and memory accesses as viewed by other RISC-V harts and external devices or coprocessors. Any combination of device input (I), device output (O), memory reads (R), and memory writes (W) may be ordered with respect to any combination of the same. Informally, no other RISC-V hart or external device can observe any operation in the successor set following a FENCE before any operation in the predecessor set preceding the FENCE, as the core support 1 hart, the fence instruction has no effect so we can considerate it as a nop instruction.

    **Pseudocode**: No operation (nop)

    **Invalid values**: NONE

    **Exception raised**: NONE

Environment Call and Breakpoints
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

- **ECALL**: Environment Call

    **Format**: ecall

    **Description**: make a request to the supporting execution environment, which is usually an operating system. The ABI for the system will define how parameters for the environment request are passed, but usually these will be in defined locations in the integer register file.

    **Pseudocode**: RaiseException(EnvironmentCall)

    **Invalid values**: NONE

    **Exception raised**: Raise an Environment Call exception.

- **EBREAK**:Environment Break

    **Format**: ebreak

    **Description**: cause control to be transferred back to a debugging environment.

    **Pseudocode**: RaiseException(Breakpoint)

    **Invalid values**: NONE

    **Exception raised**: Raise a Breakpoint exception.

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


RV32A Atomic Instructions
--------------------------------

The standard atomic instruction extension is denoted by instruction subset name “A”, and contains instructions that atomically read-modify-write memory to support synchronization between
multiple RISC-V harts running in the same memory space. The two forms of atomic instruction
provided are load-reserved/store-conditional instructions and atomic fetch-and-op memory instructions. Both types of atomic instruction support various memory consistency orderings including
unordered, acquire, release, and sequentially consistent semantics.

Load-Reserved/Store-Conditional Instructions
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

- **LR.W**: Load-Reserved Word

    **Format**: lr.w rd, (rs1)

    **Description**: LR loads a word from the address in rs1, places the sign-extended value in rd, and registers a reservation on the memory address.

    **Pseudocode**: x[rd] = LoadReserved32(M[x[rs1]])

    **Invalid values**: NONE

    **Exception raised**: If the address is not naturally aligned (4-byte boundary), a Load/AMO address misaligned exception will be generated.

- **SC.W**: Store-Conditional Word

    **Format**: sc.w rd, rs2, (rs1)

    **Description**: SC writes a word in rs2 to the address in rs1, provided a valid reservation still exists on that address. SC writes zero to rd on success or a nonzero code on failure.

    **Pseudocode**: x[rd] = StoreConditional32(M[x[rs1]], x[rs2])

    **Invalid values**: NONE

    **Exception raised**: If the address is not naturally aligned (4-byte boundary), a Store/AMO address misaligned exception will be generated.

Atomic Memory Operations
^^^^^^^^^^^^^^^^^^^^^^^^^^

- **AMOADD.W**: Atomic Memory Operation: Add Word

    **Format**: amoadd.w rd, rs2, (rs1)

    **Description**: AMOADD.W atomically loads a data value from the address in rs1, places the value into register rd, then adds the loaded value and the original value in rs2, then stores the result back to the address in rs1.

    **Pseudocode**: x[rd] = AMO32(M[x[rs1]] + x[rs2])

    **Invalid values**: NONE

    **Exception raised**: If the address is not naturally aligned (4-byte boundary), a misaligned address exception will be generated.

- **AMOAND.W**: Atomic Memory Operation: And Word

    **Format**: amoand.w rd, rs2, (rs1)

    **Description**: AMOAND.W atomically loads a data value from the address in rs1, places the value into register rd, then performs an AND between the loaded value and the original value in rs2, then stores the result back to the address in rs1.

    **Pseudocode**: x[rd] = AMO32(M[x[rs1]] & x[rs2])

    **Invalid values**: NONE

    **Exception raised**: If the address is not naturally aligned (4-byte boundary), a misaligned address exception will be generated.

- **AMOOR.W**: Atomic Memory Operation: Or Word

    **Format**: amoor.w rd, rs2, (rs1)

    **Description**: AMOOR.W atomically loads a data value from the address in rs1, places the value into register rd, then performs an OR between the loaded value and the original value in rs2, then stores the result back to the address in rs1.

    **Pseudocode**: x[rd] = AMO32(M[x[rs1]] | x[rs2])

    **Invalid values**: NONE

    **Exception raised**: If the address is not naturally aligned (4-byte boundary), a misaligned address exception will be generated.

- **AMOXOR.W**: Atomic Memory Operation: Xor Word

    **Format**: amoxor.w rd, rs2, (rs1)

    **Description**: AMOXOR.W atomically loads a data value from the address in rs1, places the value into register rd, then performs a XOR between the loaded value and the original value in rs2, then stores the result back to the address in rs1.

    **Pseudocode**: x[rd] = AMO32(M[x[rs1]] ^ x[rs2])

    **Invalid values**: NONE

    **Exception raised**: If the address is not naturally aligned (4-byte boundary), a misaligned address exception will be generated.

- **AMOSWAP.W**: Atomic Memory Operation: Swap Word

    **Format**: amoswap.w rd, rs2, (rs1)

    **Description**: AMOSWAP.W atomically loads a data value from the address in rs1, places the value into register rd, then performs a SWAP between the loaded value and the original value in rs2, then stores the result back to the address in rs1.

    **Pseudocode**: x[rd] = AMO32(M[x[rs1]] SWAP x[rs2])

    **Invalid values**: NONE

    **Exception raised**: If the address is not naturally aligned (4-byte boundary), a misaligned address exception will be generated.

- **AMOMIN.W**: Atomic Memory Operation: Minimum Word

    **Format**: amomin.d rd, rs2, (rs1)

    **Description**: AMOMIN.W atomically loads a data value from the address in rs1, places the value into register rd, then choses the minimum between the loaded value and the original value in rs2, then stores the result back to the address in rs1.

    **Pseudocode**: x[rd] = AMO32(M[x[rs1]] MIN x[rs2])

    **Invalid values**: NONE

    **Exception raised**: If the address is not naturally aligned (4-byte boundary), a misaligned address exception will be generated.

- **AMOMINU.W**: Atomic Memory Operation: Minimum Word, Unsigned

    **Format**: amominu.d rd, rs2, (rs1)

    **Description**: AMOMINU.W atomically loads a data value from the address in rs1, places the value into register rd, then choses the minimum (the values treated as unsigned) between the loaded value and the original value in rs2, then stores the result back to the address in rs1.

    **Pseudocode**: x[rd] = AMO32(M[x[rs1]] MINU x[rs2])

    **Invalid values**: NONE

    **Exception raised**: If the address is not naturally aligned (4-byte boundary), a misaligned address exception will be generated.

- **AMOMAX.W**: Atomic Memory Operation: Maximum Word, Unsigned

    **Format**: amomax.d rd, rs2, (rs1)

    **Description**: AMOMAX.W atomically loads a data value from the address in rs1, places the value into register rd, then choses the maximum between the loaded value and the original value in rs2, then stores the result back to the address in rs1.

    **Pseudocode**: x[rd] = AMO32(M[x[rs1]] MAX x[rs2])

    **Invalid values**: NONE

    **Exception raised**: If the address is not naturally aligned (4-byte boundary), a misaligned address exception will be generated.

- **AMOMAXU.W**: Atomic Memory Operation: Maximum Word, Unsigned

    **Format**: amomaxu.d rd, rs2, (rs1)

    **Description**: AMOMAXU.W atomically loads a data value from the address in rs1, places the value into register rd, then choses the maximum (the values treated as unsigned) between the loaded value and the original value in rs2, then stores the result back to the address in rs1.

    **Pseudocode**: x[rd] = AMO32(M[x[rs1]] MAXU x[rs2])

    **Invalid values**: NONE

    **Exception raised**: If the address is not naturally aligned (4-byte boundary), a misaligned address exception will be generated.

RV32C Compressed Instructions
--------------------------------

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
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

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
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

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
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

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

RV32Zicsr Control and Status Register Instructions
---------------------------------------------------

All CSR instructions atomically read-modify-write a single CSR, whose CSR specifier is encoded in the 12-bit csr field of the instruction held in bits 31–20. The immediate forms use a 5-bit zero-extended immediate encoded in the rs1 field.

- **CSRRW**: Control and Status Register Read and Write

    **Format**: csrrw rd, csr, rs1

    **Description**: reads the old value of the CSR, zero-extends the value to 32 bits, then writes it to integer register rd, the initial value in rs1 is written to the CSR. If rd=x0, then the instruction shall not read the CSR and shall not cause any of the side-effects that might occur on a CSR read.

    **Pseudocode**: t = CSRs[csr]; CSRs[csr] = x[rs1]; x[rd] = t

    **Invalid values**: NONE

    **Exception raised**: attempts to access a non-existent CSR raise an illegal instruction exception, attempts to access a CSR without appropriate privilege level or to write a read-only register also raise illegal instruction exceptions.

- **CSRRS**: Control and Status Register Read and Set

    **Format**: csrrs rd, csr, rs1

    **Description**: reads the value of the CSR, zero-extends the value to 32 bits, and writes it to integer register rd, the initial value in integer register rs1 is treated as a bit mask that specifies bit positions to be set in the CSR. Any bit that is high in rs1 will cause the corresponding bit to be set in the CSR, if that CSR bit is writable. Other bits in the CSR are unaffected (though CSRs might have side effects when written), if rs1=x0, then the instruction will not write to the CSR at all, and so shall not cause any of the side effects that might otherwise occur on a CSR write, such as raising illegal instruction exceptions on accesses to read-only CSRs.

    **Pseudocode**: t = CSRs[csr]; CSRs[csr] = t | x[rs1]; x[rd] = t

    **Invalid values**: NONE

    **Exception raised**: attempts to access a non-existent CSR raise an illegal instruction exception, attempts to access a CSR without appropriate privilege level or to write a read-only register also raise illegal instruction exceptions.

- **CSRRC**: Control and Status Register Read and Clear

    **Format**: csrrc rd, csr, rs1

    **Description**: reads the value of the CSR, zero-extends the value to 32 bits, and writes it to integer register rd, the initial value in integer register rs1 is treated as a bit mask that specifies bit positions to be cleared in the CSR. Any bit that is high in rs1 will cause the corresponding bit to be set in the CSR, if that CSR bit is writable. Other bits in the CSR are unaffected (though CSRs might have side effects when written), if rs1=x0, then the instruction will not write to the CSR at all, and so shall not cause any of the side effects that might otherwise occur on a CSR write, such as raising illegal instruction exceptions on accesses to read-only CSRs.

    **Pseudocode**: t = CSRs[csr]; CSRs[csr] = t & ∼x[rs1]; x[rd] = t

    **Invalid values**: NONE

    **Exception raised**: attempts to access a non-existent CSR raise an illegal instruction exception, attempts to access a CSR without appropriate privilege level or to write a read-only register also raise illegal instruction exceptions.

- **CSRRWI**: Control and Status Register Read and Write Immediate

    **Format**: csrrwi rd, csr, uimm[4:0]

    **Description**: reads the old value of the CSR, zero-extends the value to 32 bits, then writes it to integer register rd. The zero-extends immediate is written to the CSR. If rd=x0, then the instruction shall not read the CSR and shall not cause any of the side-effects that might occur on a CSR read.

    **Pseudocode**: x[rd] = CSRs[csr]; CSRs[csr] = zext(uimm[4:0])

    **Invalid values**: NONE

    **Exception raised**: attempts to access a non-existent CSR raise an illegal instruction exception, attempts to access a CSR without appropriate privilege level or to write a read-only register also raise illegal instruction exceptions.

- **CSRRSI**: Control and Status Register Read and Set Immediate

    **Format**: csrrsi rd, csr, uimm[4:0]

    **Description**: reads the value of the CSR, zero-extends the value to 32 bits, and writes it to integer register rd. The zero-extends immediate value is treated as a bit mask that specifies bit positions to be set in the CSR. Any bit that is high in zero-extends immediate will cause the corresponding bit to be set in the CSR, if that CSR bit is writable. Other bits in the CSR are unaffected (though CSRs might have side effects when written), if the uimm[4:0] field is zero, then these instructions will not write to the CSR, and shall not cause any of the side effects that might otherwise occur on a CSR write.

    **Pseudocode**: t = CSRs[csr]; CSRs[csr] = t | zext(uimm[4:0]); x[rd] = t

    **Invalid values**: NONE

    **Exception raised**: attempts to access a non-existent CSR raise an illegal instruction exception, attempts to access a CSR without appropriate privilege level or to write a read-only register also raise illegal instruction exceptions.

- **CSRRCI**: Control and Status Register Read and Clear Immediate

    **Format**: csrrci rd, csr, uimm[4:0]

    **Description**: reads the value of the CSR, zero-extends the value to 32 bits, and writes it to integer register rd. The zero-extends immediate value is treated as a bit mask that specifies bit positions to be cleared in the CSR. Any bit that is high in zero-extends immediate will cause the corresponding bit to be set in the CSR, if that CSR bit is writable. Other bits in the CSR are unaffected (though CSRs might have side effects when written), if the uimm[4:0] field is zero, then these instructions will not write to the CSR, and shall not cause any of the side effects that might otherwise occur on a CSR write.

    **Pseudocode**: t = CSRs[csr]; CSRs[csr] = t & ∼zext(uimm[4:0]); x[rd] = t

    **Invalid values**: NONE

    **Exception raised**: attempts to access a non-existent CSR raise an illegal instruction exception, attempts to access a CSR without appropriate privilege level or to write a read-only register also raise illegal instruction exceptions.

RV32Zifencei Instruction-Fetch Fence
--------------------------------------

- **FENCE.I**: Fence Instruction

    **Format**: fence.i

    **Description**: The FENCE.I instruction is used to synchronize the instruction and data streams. RISC-V does not guarantee that stores to instruction memory will be made visible to instruction fetches on the same RISC-V hart until a FENCE.I instruction is executed. A FENCE.I instruction only ensures that a subsequent instruction fetch on a RISC-V hart will see any previous data stores already visible to the same RISC-V hart.

    **Pseudocode**: Fence(Store, Fetch)

    **Invalid values**: NONE

    **Exception raised**: NONE

RV32Zicond Integer Conditional operations
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

Illegal Instruction
---------------------------

This section describe all kind of Illegal Instruction, in this case the Core generate an illegal instruction exception.

- **ILLEGAL OPCODE**: any instruction (compressed or not compressed) with a non supported opcode is an illegal instruction

- **ILLEGAL FUNCT2**: any instruction (R4type) with a non supported FUNCT2 is an illegal instruction

- **ILLEGAL FUNCT3**: any instruction (Rtype, R4type, Itype, Stype or Atype) with a non supported FUNCT3 is an illegal instruction

- **ILLEGAL FUNCT5**: any instruction (Atype) with a non supported FUNCT5 is an illegal instruction

- **ILLEGAL FUNCT7**: any instruction (Rtype) with a non supported FUNCT7 is an illegal instruction

- **ILLEGAL CSR**: any CSR instruction attempts to access a non-existent is an illegal instruction

- **ILLEGAL PRIVILEGE LEVEL**: any CSR instruction attempts to access a CSR without appropriate privilege level is an illegal instruction

- **ILLEGAL ACCESS TYPE CSR**: any CSR instruction attempts to write a read-only CSR a non-existent is an illegal instruction
