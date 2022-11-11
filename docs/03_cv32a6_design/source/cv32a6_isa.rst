RV32 Instructions
=================

Introduction
------------------

In this section, we present ISA (Instruction Set Architecture) for C32VA6_v0.1.0, illustrating different supported instructions, the base RISC-V ISA has fixed-length 32-bit instructions that must be naturally aligned on 32-bit boundaries.

General purpose registers
--------------------------

As shown in the Table 1.1, There are 31 general-purpose registers x1–x31, which hold integer values. Register x0 is hardwired to the constant 0. There is no hardwired subroutine return address link register, but the standard software calling convention uses register x1 to hold the return address on a call. For C32VA6_v0.1.0, the x registers are 32 bits wide. There is one additional register also 32 bits wide: the program counter pc holds the address of the current instruction.

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
     - Zero
     - Hardwired zero  
   * - 1
     - 
     - x1
     - ra
     - Return address
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

    **Description**:  logical left shift (zeros are shifted into the lower bits).

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

    **Exception raised**: Jumps to an incorrect instruction address will usually quickly raise an exception.

- **JALR**: Jump and Link Register

    **Format**: jalr rd, rs1, imm[11:0]

    **Description**: target address is obtained by adding the 12-bit signed immediate to the register rs1 (pc is calculated using signed arithmetic), then setting the least-significant bit of the result to zero, and store the address of instruction following the jump (pc+4) into register rd.

    **Pseudocode**: t = pc+4; pc = (x[rs1]+sext(imm[11:0]))&∼1 ; x[rd] = t

    **Invalid values**: NONE

    **Exception raised**: Jumps to an incorrect instruction address will usually quickly raise an exception.

**Conditional Branches**

- **BEQ**: Branch Equal

    **Format**: beq rs1, rs2, imm[12:1]

    **Description**: take the branch (pc is calculated using signed arithmetic) if registers rs1 and rs2 are equal.

    **Invalid values**: NONE

    **Pseudocode**: if (x[rs1] == x[rs2]) pc += sext({imm[12:1], 1’b0}) else pc += 4

    **Exception raised**: No instruction fetch misaligned exception is generated for a conditional branch that is not taken.

- **BNE**: Branch Not Equal

    **Format**: bne rs1, rs2, imm[12:1]

    **Description**: take the branch (pc is calculated using signed arithmetic) if registers rs1 and rs2 are not equal.

    **Invalid values**: NONE

    **Pseudocode**: if (x[rs1] != x[rs2]) pc += sext({imm[12:1], 1’b0}) else pc += 4

    **Exception raised**: No instruction fetch misaligned exception is generated for a conditional branch that is not taken.

- **BLT**: Branch Less Than

    **Format**: blt rs1, rs2, imm[12:1]

    **Description**: take the branch (pc is calculated using signed arithmetic) if registers rs1 less than rs2 (using signed comparison).

    **Invalid values**: NONE

    **Pseudocode**: if (x[rs1] < x[rs2]) pc += sext({imm[12:1], 1’b0}) else pc += 4

    **Exception raised**: No instruction fetch misaligned exception is generated for a conditional branch that is not taken.

- **BLTU**: Branch Less Than Unsigned

    **Format**: bltu rs1, rs2, imm[12:1]

    **Description**: take the branch (pc is calculated using signed arithmetic) if registers rs1 less than rs2 (using unsigned comparison).

    **Invalid values**: NONE

    **Pseudocode**: if (x[rs1] <u x[rs2]) pc += sext({imm[12:1], 1’b0}) else pc += 4

    **Exception raised**: No instruction fetch misaligned exception is generated for a conditional branch that is not taken.

- **BGE**: Branch Greater or Equal

    **Format**: bge rs1, rs2, imm[12:1]

    **Description**: take the branch (pc is calculated using signed arithmetic) if registers rs1 is greater than or equal rs2 (using signed comparison).

    **Pseudocode**: if (x[rs1] >= x[rs2]) pc += sext({imm[12:1], 1’b0}) else pc += 4

    **Invalid values**: NONE

    **Exception raised**: No instruction fetch misaligned exception is generated for a conditional branch that is not taken.

- **BGEU**: Branch Greater or Equal Unsigned

    **Format**: bgeu rs1, rs2, imm[12:1]

    **Description**: takes the branch (pc is calculated using signed arithmetic) if registers rs1 is greater than or equal rs2 (using unsigned comparison).

    **Pseudocode**: if (x[rs1] >=u x[rs2]) pc += sext({imm[12:1], 1’b0}) else pc += 4

    **Exception raised**: No instruction fetch misaligned exception is generated for a conditional branch that is not taken.

Load and Store Instructions
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

- **LB**: Load Byte

    **Format**: lb rd, rs1, imm[11:0]

    **Description**: loads a 8-bit value from memory, then sign-extends to 32-bit before storing in rd (rd is calculated using signed arithmetic). The effective address is obtained by adding register rs1 to the sign-extended 12-bit offset.

    **Pseudocode**: x[rd] = sext(M[x[rs1] + sext(imm[11:0])][7:0])

    **Invalid values**: NONE

    **Exception raised**: Loads with a destination of x0 must still raise any exceptions.

- **LH**: Load Halfword

    **Format**: lh rd, rs1, imm[11:0]

    **Description**: loads a 16-bit value from memory, then sign-extends to 32-bit before storing in rd (rd is calculated using signed arithmetic). The effective address is obtained by adding register rs1 to the sign-extended 12-bit offset.

    **Pseudocode**: x[rd] = sext(M[x[rs1] + sext(imm[11:0])][15:0])

    **Invalid values**: NONE

    **Exception raised**: Loads with a destination of x0 must still raise any exceptions, also an exception if the memory address isn't aligned (2-byte boundary).

- **LW**: Load Word

    **Format**: lw rd, rs1, imm[11:0]

    **Description**: loads a 32-bit value from memory, then storing in rd (rd is calculated using signed arithmetic). The effective address is obtained by adding register rs1 to the sign-extended 12-bit offset.

    **Invalid values**: NONE

    **Pseudocode**: x[rd] = sext(M[x[rs1] + sext(imm[11:0])][31:0])

    **Exception raised**: Loads with a destination of x0 must still raise any exceptions, also an exception if the memory address isn't aligned (4-byte boundary).

- **LBU**: Load Byte Unsigned

    **Format**: lbu rd, rs1, imm[11:0]

    **Description**: loads a 8-bit value from memory, then zero-extends to 32-bit before storing in rd (rd is calculated using unsigned arithmetic). The effective address is obtained by adding register rs1 to the sign-extended 12-bit offset.

    **Pseudocode**: x[rd] = Zext(M[x[rs1] + sext(imm[11:0])][7:0])

    **Invalid values**: NONE

    **Exception raised**: Loads with a destination of x0 must still raise any exceptions.

- **LHU**: Load Halfword Unsigned

    **Format**: lhu rd, rs1, imm[11:0]

    **Description**: loads a 16-bit value from memory, then zero-extends to 32-bit before storing in rd (rd is calculated using unsigned arithmetic). The effective address is obtained by adding register rs1 to the sign-extended 12-bit offset.

    **Pseudocode**: x[rd] = Zext(M[x[rs1] + sext(imm[11:0])][7:0])

    **Invalid values**: NONE

    **Exception raised**: Loads with a destination of x0 must still raise any exceptions, also an exception if the memory address isn't aligned (2-byte boundary).

- **SB**: Store Byte

    **Format**: sb rs1, rs2, imm[11:0]

    **Description**: stores a 8-bit value from the low bits of register rs2 to memory. The effective address is obtained by adding register rs1 to the sign-extended 12-bit offset.

    **Pseudocode**: M[x[rs1] + sext(imm[11:0])][7:0] = x[rs2][7:0]

    **Invalid values**: NONE

    **Exception raised**: NONE

- **SH**: Store Halfword

    **Format**: sh rs1, rs2, imm[11:0]

    **Description**: stores a 16-bit value from the low bits of register rs2 to memory. The effective address is obtained by adding register rs1 to the sign-extended 12-bit offset.

    **Pseudocode**: M[x[rs1] + sext(imm[11:0])][15:0] = x[rs2][15:0]

    **Invalid values**: NONE

    **Exception raised**: An exception raised if the memory address isn't aligned (2-byte boundary).

- **SW**: Store Word

    **Format**: sw rs1, rs2, imm[11:0]

    **Description**: stores a 32-bit value from register rs2 to memory. The effective address is obtained by adding register rs1 to the sign-extended 12-bit offset.

    **Pseudocode**: M[x[rs1] + sext(imm[11:0])][31:0] = x[rs2][31:0]

    **Invalid values**: NONE

    **Exception raised**: An exception raised if the memory address isn't aligned (4-byte boundary).

Memory Ordering
^^^^^^^^^^^^^^^^^^

- **FENCE**: Fence Instruction

    **Format**: fence pre, succ

    **Description**: order device I/O and memory accesses as viewed by other RISC-V harts and external devices or coprocessors. Any combination of device input (I), device output (O), memory reads (R), and memory writes (W) may be ordered with respect to any combination of the same. Informally, no other RISC-V hart or external device can observe any operation in the successor set following a FENCE before any operation in the predecessor set preceding the FENCE.

    **Pseudocode**: Fence(pred, succ)

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

    **Exception raised**:  If the address is not naturally aligned (4-byte boundary), a misaligned address exception will be generated.

- **LR.W**: Store-Conditional Word

    **Format**: sc.w rd, rs2, (rs1)

    **Description**: SC writes a word in rs2 to the address in rs1, provided a valid reservation still exists on that address. SC writes zero to rd on success or a nonzero code on failure.

    **Pseudocode**: x[rd] = StoreConditional32(M[x[rs1]], x[rs2])

    **Invalid values**: NONE

    **Exception raised**:  If the address is not naturally aligned (4-byte boundary), a misaligned address exception will be generated.

Atomic Memory Operations
^^^^^^^^^^^^^^^^^^^^^^^^^^

- **AMOADD.W**: Atomic Memory Operation: Add Word

    **Format**: amoadd.w rd, rs2, (rs1)

    **Description**: The atomic memory operation (AMO) instructions perform read-modify-write operations for multiprocessor synchronization and are encoded with an R-type instruction format. These AMO instructions atomically load a data value from the address in rs1, place the value into register rd, then add the loaded value and the original value in rs2, then store the result back to the address in rs1. 32-bit AMOs always sign-extend the value placed in rd.

    **Pseudocode**: x[rd] = AMO32(M[x[rs1]] + x[rs2])

    **Invalid values**: NONE

    **Exception raised**:  If the address is not naturally aligned (4-byte boundary), a misaligned address exception will be generated.

- **AMOAND.W**: Atomic Memory Operation: And Word

    **Format**: amoand.w rd, rs2, (rs1)

    **Description**: The atomic memory operation (AMO) instructions perform read-modify-write operations for multiprocessor synchronization and are encoded with an R-type instruction format. These AMO instructions atomically load a data value from the address in rs1, place the value into register rd, apply a AND operator to the loaded value and the original value in rs2, then store the result back to the address in rs1. 32-bit AMOs always sign-extend the value placed in rd.

    **Pseudocode**: x[rd] = AMO32(M[x[rs1]] & x[rs2])

    **Invalid values**: NONE

    **Exception raised**:  If the address is not naturally aligned (4-byte boundary), a misaligned address exception will be generated.

- **AMOOR.W**: Atomic Memory Operation: Or Word

    **Format**: amoor.w rd, rs2, (rs1)

    **Description**: The atomic memory operation (AMO) instructions perform read-modify-write operations for multiprocessor synchronization and are encoded with an R-type instruction format. These AMO instructions atomically load a data value from the address in rs1, place the value into register rd, apply a OR operator to the loaded value and the original value in rs2, then store the result back to the address in rs1. 32-bit AMOs always sign-extend the value placed in rd.

    **Pseudocode**: x[rd] = AMO32(M[x[rs1]] | x[rs2])

    **Invalid values**: NONE

    **Exception raised**:  If the address is not naturally aligned (4-byte boundary), a misaligned address exception will be generated.

- **AMOXOR.W**: Atomic Memory Operation: Xor Word

    **Format**: amoxor.w rd, rs2, (rs1)

    **Description**: The atomic memory operation (AMO) instructions perform read-modify-write operations for multiprocessor synchronization and are encoded with an R-type instruction format. These AMO instructions atomically load a data value from the address in rs1, place the value into register rd, apply a XOR operator to the loaded value and the original value in rs2, then store the result back to the address in rs1. 32-bit AMOs always sign-extend the value placed in rd.

    **Pseudocode**: x[rd] = AMO32(M[x[rs1]] ^ x[rs2])

    **Invalid values**: NONE

    **Exception raised**:  If the address is not naturally aligned (4-byte boundary), a misaligned address exception will be generated.

- **AMOSWAP.W**: Atomic Memory Operation: Swap Word

    **Format**: amoswap.w rd, rs2, (rs1)

    **Description**: The atomic memory operation (AMO) instructions perform read-modify-write operations for multiprocessor synchronization and are encoded with an R-type instruction format. These AMO instructions atomically load a data value from the address in rs1, place the value into register rd, then SWAP the loaded value and the original value in rs2, then store the result back to the address in rs1. 32-bit AMOs always sign-extend the value placed in rd.

    **Pseudocode**: x[rd] = AMO32(M[x[rs1]] SWAP x[rs2])

    **Invalid values**: NONE

    **Exception raised**:  If the address is not naturally aligned (4-byte boundary), a misaligned address exception will be generated.

- **AMOMIN.W**: Atomic Memory Operation: Minimum Word

    **Format**: amomin.d rd, rs2, (rs1)

    **Description**: The atomic memory operation (AMO) instructions perform read-modify-write operations for multiprocessor synchronization and are encoded with an R-type instruction format. These AMO instructions atomically load a data value from the address in rs1, place the value into register rd, we take the minimum between the loaded value and the original value in rs2, then store the result back to the address in rs1. 32-bit AMOs always sign-extend the value placed in rd.

    **Pseudocode**: x[rd] = AMO32(M[x[rs1]] MIN x[rs2])

    **Invalid values**: NONE

    **Exception raised**:  If the address is not naturally aligned (4-byte boundary), a misaligned address exception will be generated.

- **AMOMINU.W**: Atomic Memory Operation: Minimum Word, Unsigned

    **Format**: amominu.d rd, rs2, (rs1)

    **Description**: The atomic memory operation (AMO) instructions perform read-modify-write operations for multiprocessor synchronization and are encoded with an R-type instruction format. These AMO instructions atomically load a data value from the address in rs1, place the value into register rd, we take the minimum between the loaded value and the original value in rs2, then store the result back to the address in rs1. 32-bit AMOs always sign-extend the value placed in rd (the values treated as unsigned). 

    **Pseudocode**: x[rd] = AMO32(M[x[rs1]] MINU x[rs2])

    **Invalid values**: NONE

    **Exception raised**:  If the address is not naturally aligned (4-byte boundary), a misaligned address exception will be generated.

- **AMOMAX.W**: Atomic Memory Operation: Maximum Word, Unsigned

    **Format**: amomax.d rd, rs2, (rs1)

    **Description**: The atomic memory operation (AMO) instructions perform read-modify-write operations for multiprocessor synchronization and are encoded with an R-type instruction format. These AMO instructions atomically load a data value from the address in rs1, place the value into register rd, we take the maximum between the loaded value and the original value in rs2, then store the result back to the address in rs1. 32-bit AMOs always sign-extend the value placed in rd.

    **Pseudocode**: x[rd] = AMO32(M[x[rs1]] MAX x[rs2])

    **Invalid values**: NONE

    **Exception raised**:  If the address is not naturally aligned (4-byte boundary), a misaligned address exception will be generated.

- **AMOMAXU.W**: Atomic Memory Operation: Maximum Word, Unsigned

    **Format**: amomaxu.d rd, rs2, (rs1)

    **Description**: The atomic memory operation (AMO) instructions perform read-modify-write operations for multiprocessor synchronization and are encoded with an R-type instruction format. These AMO instructions atomically load a data value from the address in rs1, place the value into register rd, we take the maximum between the loaded value and the original value in rs2, then store the result back to the address in rs1. 32-bit AMOs always sign-extend the value placed in rd (the values treated as unsigned). 

    **Pseudocode**: x[rd] = AMO32(M[x[rs1]] MAXU x[rs2])

    **Invalid values**: NONE

    **Exception raised**:  If the address is not naturally aligned (4-byte boundary), a misaligned address exception will be generated.

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

    **Format**: c.addi4spn nzimm[9:2]

    **Description**: adds a zero-extended non-zero immediate, scaled by 4, to the stack pointer, x2, and writes the result to rd'. This instruction is used to generate pointers to stack-allocated variables.

    **Pseudocode**: x[8 + rd'] = x[2] + Zext(nzimm[9:2])

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

    **Description**: performs a logical Right shift (zeros are shifted into the upper bits).

    **Pseudocode**: x[8 + rd'] = x[8 + rd'] >> uimm[5:0]

    **Invalid values**: uimm[5] = 0

    **Exception raised**: NONE

- **C.SRAI**: Compressed Shift Right Arithmetic Immediate

    **Format**: c.srai rd', uimm[5:0]

    **Description**: performs an Arithmetic Right shift (sign bits are shifted into the upper bits).

    **Pseudocode**: x[8 + rd'] = x[8 + rd'] >> uimm[5:0]

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

    **Invalid values**: rd = x0 & rs1 = x0

    **Exception raised**: NONE

- **C.MV**: Move

    **Format**: c.mv rd, rs2

    **Description**: copies the value in register rs2 into register rd.

    **Pseudocode**: x[rd] = x[rs2]

    **Invalid values**: rd = x0 & rs1 = x0

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

    **Pseudocode**: pc += sext(imm)

    **Invalid values**: NONE

    **Exception raised**: Jumps to an incorrect instruction address will usually quickly raise an exception.

- **C.JAL**: Compressed Jump and Link

    **Format**: c.jal imm[11:1]

    **Description**: performs the same operation as C.J, but additionally writes the address of the instruction following the jump (pc+2) to the link register, x1.

    **Pseudocode**: x[1] = pc+2; pc += sext(offset)

    **Invalid values**: NONE

    **Exception raised**: Jumps to an incorrect instruction address will usually quickly raise an exception.

- **C.JR**: Compressed Jump Register

    **Format**: c.jr rs1

    **Description**: performs an unconditional control transfer to the address in register rs1.

    **Pseudocode**: pc = x[rs1]

    **Invalid values**: rs1 = x0

    **Exception raised**: Jumps to an incorrect instruction address will usually quickly raise an exception.

- **C.JALR**: Compressed Jump and Link Register

    **Format**: c.jalr imm[11:1]

    **Description**: performs the same operation as C.JR, but additionally writes the address of the instruction following the jump (pc+2) to the link register, x1.

    **Pseudocode**: t = pc+2; pc = x[rs1]; x[1] = t

    **Invalid values**: rs1 = x0

    **Exception raised**: Jumps to an incorrect instruction address will usually quickly raise an exception.

- **C.BEQZ**: Branch if Equal Zero

    **Format**: c.beqz rs1', imm[8:1]

    **Description**: performs conditional control transfers. The offset is sign-extended and added to the pc to form the branch target address. C.BEQZ takes the branch if the value in register rs1' is zero.

    **Pseudocode**: if (x[8+rs1'] == 0) pc += sext(imm)

    **Invalid values**: NONE

    **Exception raised**: No instruction fetch misaligned exception is generated for a conditional branch that is not taken.

- **C.BNEZ**: Branch if Not Equal Zero

    **Format**: c.bnez rs1', imm[8:1]

    **Description**: performs conditional control transfers. The offset is sign-extended and added to the pc to form the branch target address. C.BEQZ takes the branch if the value in register rs1' isn't zero.

    **Pseudocode**: if (x[8+rs1'] != 0) pc += sext(imm)

    **Invalid values**: NONE

    **Exception raised**: No instruction fetch misaligned exception is generated for a conditional branch that is not taken.

Load and Store Instructions
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

- **C.LWSP**: Load Word Stack-Pointer

    **Format**: c.lwsp rd, uimm(x2)

    **Description**: loads a 32-bit value from memory into register rd. It computes an effective address by adding the zero-extended offset, scaled by 4, to the stack pointer, x2.

    **Pseudocode**: x[rd] = sext(M[x[2] + uimm][31:0])

    **Invalid values**: rd = x0

    **Exception raised**: Loads with a destination of x0 must still raise any exceptions, also an exception if the memory address isn't aligned (4-byte boundary).

- **C.SWSP**: Store Word Stack-Pointer

    **Format**: c.lwsp rd, uimm(x2)

    **Description**: stores a 32-bit value in register rs2 to memory. It computes an effective address by adding the zero-extended offset, scaled by 4, to the stack pointer, x2.

    **Pseudocode**: M[x[2] + uimm][31:0] = x[rs2]

    **Invalid values**: NONE

    **Exception raised**: An exception raised if the memory address isn't aligned (4-byte boundary).

- **C.LW**: Compressed Load Word

    **Format**: c.lw rd', uimm(rs1')

    **Description**: loads a 32-bit value from memory into register rd'.It computes an effective address by adding the zero-extended offset, scaled by 4, to the base address in register rs1'.

    **Pseudocode**: x[8+rd'] = sext(M[x[8+rs1'] + uimm][31:0])

    **Invalid values**: NONE

    **Exception raised**: An exception raised if the memory address isn't aligned (4-byte boundary).

- **C.SW**: Compressed Store Word

    **Format**: c.sw rs2', uimm(rs1')

    **Description**: stores a 32-bit value from memory into register rd'.It computes an effective address by adding the zero-extended offset, scaled by 4, to the base address in register rs1'.

    **Pseudocode**: M[x[8+rs1'] + uimm][31:0] = x[8+rs2']

    **Invalid values**: NONE

    **Exception raised**: An exception raised if the memory address isn't aligned (4-byte boundary).

RV32Zicsr Control and Status Register Instructions
---------------------------------------------------

SYSTEM instructions are used to access system functionality that might require privileged access
and are encoded using the I-type instruction format. These can be divided into two main classes:
those that atomically read-modify-write control and status registers (CSRs), and all other potentially privileged instructions.

- **CSRRW**: Control and Status Register Read and Write

    **Format**: csrrw rd, rs1, csr

    **Description**: reads the old value of the CSR, zero-extends the value to 32 bits, then writes it to integer register rd. The initial value in rs1 is written to the CSR. If rd=x0, then the instruction shall not read the CSR and shall not cause any of the side-effects that might occur on a CSR read.

    **Pseudocode**: t = CSRs[csr]; CSRs[csr] = x[rs1]; x[rd] = t

    **Invalid values**: NONE

    **Exception raised**: Attempts to access a non-existent CSR raise an illegal instruction exception.

- **CSRRS**: Control and Status Register Read and Set

    **Format**: csrrs rd, rs1, csr

    **Description**: reads the value of the CSR, zero-extends the value to 32 bits, and writes it to integer register rd. The initial value in integer register rs1 is treated as a bit mask that specifies bit positions to be set in the CSR. Any bit that is high in rs1 will cause the corresponding bit to be set in the CSR, if that CSR bit is writable. Other bits in the CSR are unaffected (though CSRs might have side effects when written).

    **Pseudocode**: t = CSRs[csr]; CSRs[csr] = t | x[rs1]; x[rd] = t

    **Invalid values**: NONE

    **Exception raised**: Attempts to access a non-existent CSR raise an illegal instruction exception.

- **CSRRC**:Control and Status Register Read and Clear

    **Format**: csrrc rd, rs1, csr

    **Description**: reads the value of the CSR, zero-extends the value to 32 bits, and writes it to integer register rd. The initial value in integer register rs1 is treated as a bit mask that specifies bit positions to be cleared in the CSR. Any bit that is high in rs1 will cause the corresponding bit to be cleared in the CSR, if that CSR bit is writable. Other bits in the CSR are unaffected.

    **Pseudocode**: t = CSRs[csr]; CSRs[csr] = t & ∼x[rs1]; x[rd] = t

    **Invalid values**: NONE

    **Exception raised**: Attempts to access a non-existent CSR raise an illegal instruction exception.

- **CSRRWI**: Control and Status Register Read and Write Immediate

    **Format**: csrrwi rd, imm[4:0], csr

    **Description**: reads the old value of the CSR, zero-extends the value to 32 bits, then writes it to integer register rd. The zero-extends immediate is written to the CSR. If rd=x0, then the instruction shall not read the CSR and shall not cause any of the side-effects that might occur on a CSR read.

    **Pseudocode**: x[rd] = CSRs[csr]; CSRs[csr] = zimm

    **Invalid values**: NONE

    **Exception raised**: Attempts to access a non-existent CSR raise an illegal instruction exception.

- **CSRRSI**:Control and Status Register Read and Set Immediate

    **Format**: csrrsi rd, imm[4:0], csr

    **Description**: reads the value of the CSR, zero-extends the value to 32 bits, and writes it to integer register rd. The zero-extends immediate value is treated as a bit mask that specifies bit positions to be set in the CSR. Any bit that is high in zero-extends immediate will cause the corresponding bit to be set in the CSR, if that CSR bit is writable. Other bits in the CSR are unaffected (though CSRs might have side effects when written).

    **Pseudocode**: t = CSRs[csr]; CSRs[csr] = t | zimm; x[rd] = t

    **Invalid values**: NONE

    **Exception raised**: Attempts to access a non-existent CSR raise an illegal instruction exception.

- **CSRRCI**:Control and Status Register Read and Clear Immediate

    **Format**: csrrci rd, imm[4:0], csr

    **Description**: reads the value of the CSR, zero-extends the value to 32 bits, and writes it to integer register rd. The zero-extends immediate value is treated as a bit mask that specifies bit positions to be cleared in the CSR. Any bit that is high in The zero-extends immediate will cause the corresponding bit to be cleared in the CSR, if that CSR bit is writable. Other bits in the CSR are unaffected.

    **Pseudocode**: t = CSRs[csr]; CSRs[csr] = t & ∼zimm; x[rd] = t

    **Invalid values**: NONE

    **Exception raised**: Attempts to access a non-existent CSR raise an illegal instruction exception.

RV32Zifence Instruction
-------------------------

- **FENCE.I**:Fence Instruction

    **Format**: fence.i

    **Description**: The FENCE.I instruction is used to synchronize the instruction and data streams.RISC-V does not guarantee that stores to instruction memory will be made visible to instruction fetches on the same RISC-V hart until a FENCE.I instruction is executed. A FENCE.I instruction only ensures that a subsequent instruction fetch on a RISC-V hart will see any previous data stores already visible to the same RISC-V hart.

    **Pseudocode**: Fence(Store, Fetch)

    **Invalid values**: NONE

    **Exception raised**: NONE
