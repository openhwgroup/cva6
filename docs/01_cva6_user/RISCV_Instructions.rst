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

*This chapter is applicable to all configurations.*

CVA6 RISC-V Instructions
========================

Introduction
------------------

In the next pages, the ISA (Instruction Set Architecture) for various CVA6 configurations is presented, illustrating different supported instructions, the Base Integer Instruction set RV32I or RV64I, and also other instructions in some extensions supported by the core as:

* RV32M        – Standard Extension for Integer Multiplication and Division Instructions
* RV32A        – Standard Extension for Atomic Instructions
* RV32C        – Standard Extension for Compressed Instructions
* RVZba        - Standard Extension for Bit Manipulation: Address generation instructions (RV32 and RV64)
* RVZbb        - Standard Extension for Bit Manipulation: Basic bit manipulation (RV32 and RV64)
* RVZbc        - Standard Extension for Bit Manipulation: Carry-less multiplication (RV32 and RV64)
* RVZbs        - Standard Extension for Bit Manipulation: Single-bit instructions (RV32 and RV64)
* RV32Zcb      – Standard Extension for Code Size Reduction
* RVZcmp       – Standard Extension for Code Size Reduction (RV32 and RV64)
* RVZicsr      – Standard Extension for CSR Instructions
* RVZifencei   – Standard Extension for Instruction-Fetch Fence
* RVZicond     – Standard Extension for Integer Conditional Operations

The base RISC-V ISA (RV32I or RV64I) has fixed-length 32-bit instructions or 16-bit instructions, so that must be naturally aligned on 2-byte boundary.
If 16-bit instructions are not implemented (RVC, RVZcb, RVZcmp), then instructions must be naturally aligned on 4-byte boundary.

All CVA6 configurations support:

* Only 1 hart,
* No misaligned memory accesses.

General purpose registers
--------------------------

As shown in the Table 1.1, there are 31 general-purpose registers x1–x31, which hold integer values. Register x0 is hardwired to the constant 0. There is no hardwired subroutine return address link register, but the standard software calling convention uses register x1 to hold the return address on a call.

In CV32A6 configurations, the x registers are 32-bit wide. There is one additional register also 32 bits wide: the program counter PC that holds the address of the current instruction.

In CV64A6 configurations, the x registers and the PC are 64-bit wide.

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

RISC-V Extensions
-----------------

The following pages detail the instructions of the RISC-V extensions that are included in each CVA6 configuration.

Some extensions that are supported by CVA6, but not yet included in any verified CVA6 configuration, might not yet have a such a detailed description. Contributors are welcome to complete these extensions.


Conventions and Terminology
-----------------------------

The notations below are used in the description of instructions.

- **sext(val)**: Sign Extension is the operation of increasing the number of bits of a binary number while preserving the number's sign (positive(0)/negative(1)) and value. this is done by appending digits to the most significant side of the number.

- **zext(val)**: Zero Extension is the operation of increasing the number of bits of a binary number with zeros. this is done by appending digits to the most significant side of the number.

- **<u**: Comparison operation (less than) of 2 unsigned values.

- **>>s**: Right shift of 2 signed values.

- **>>u**: Right shift of 2 unsigned values.

- **M[address]**: Value exists in the address of the memory.

- **/s**: Division of 2 signed values.

- **/u**: Division of 2 unsigned values.

- **%s**: Remainder of the Division of 2 signed values.

- **%u**: Remainder of the Division of 2 unsigned values.

- **AMO32**: Atomic Memory Operation (word).

- **rx'**: rd', rs1' or rs2', stand for the 3-bit Compressed Encoding registers.



Illegal Instructions
--------------------

This section describe all kind of Illegal Instructions. In this case the Core generate an illegal instruction exception.

- **ILLEGAL OPCODE**: any instruction (compressed or not compressed) with a non supported opcode is an illegal instruction

- **ILLEGAL FUNCT2**: any instruction (R4type) with a non supported FUNCT2 is an illegal instruction

- **ILLEGAL FUNCT3**: any instruction (Rtype, R4type, Itype, Stype or Atype) with a non supported FUNCT3 is an illegal instruction

- **ILLEGAL FUNCT5**: any instruction (Atype) with a non supported FUNCT5 is an illegal instruction

- **ILLEGAL FUNCT7**: any instruction (Rtype) with a non supported FUNCT7 is an illegal instruction

- **ILLEGAL CSR**: any CSR instruction attempts to access a non-existent is an illegal instruction

- **ILLEGAL PRIVILEGE LEVEL**: any CSR instruction attempts to access a CSR without appropriate privilege level is an illegal instruction

- **ILLEGAL ACCESS TYPE CSR**: any CSR instruction attempts to write a read-only CSR a non-existent is an illegal instruction
