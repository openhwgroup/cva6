# Ariane RISC-V CPU

This document describes the 5-stage, single issue Ariane CPU which implements the 64bit RISC-V instruction set. It is conformant to the I,M and C extensions as specified in Volume I: User-Level ISA V2.1 as well as the draft privilege extension 1.10. It implements three privilege levels M, S, U to fully support a Unix-like operating system.

## Scope and Purpose

The purpose of the core is to run a full OS at reasonable speed and IPC. To achieve the necessary speed (targeting 1.6ns cycle time in UMC65) the core features a 5-stage pipelined design. In order to increase the IPC the CPU features a scoreboarding technique that should hide the rather long latency to the data RAM (cache) by issuing independent instructions.
The instruction RAM has (or L1 instruction cache) an access latency of 1 cycle on a hit, while accesses to the data RAM (or L1 data cache) have a longer latency of 3 cycles on a hit.

![Ariane Block Diagram](fig/ariane_overview.png)

## Planned Limitations

Ariane is not going to support floating points and atomic operations.

## Instructions

- Integer computation (immediate-register): ADDI/SLTI[U], ANDI/ORI/XORI, SLLI/SRLI/SRAI
- Integer computation (register-register): ADD/SLT/SLTU, AND/OR/XOR, SLL/SRL, SUB/SRA, MUL/DIV/REM
- Operations on PC (PC-immediate): LUI, AUIPC
- Control Transfer: J, JAL, JALR
- Conditional Branches: BEQ/BNE, BLT[U], BGE[U]
- Load and Stores
- Memory instructions: FENCE.I (flush D$ and I$, kill pipeline), SFENCE.VM (flush TLB)
- System Instructions: CSRR[..], RDCYCLE, RDTIME, RDINSTRET, ECALL, EBREAK, WFI, MRET/SRET/URET

## ToDo Section:

Things that need to be done (in no particular order):

- Scoreboard testbench
- Branch prediction, detailed block diagram (support in scoreboard)
- Processor front-end, detailed design
- Commit stage, detailed design (especially concerning CSR register, APB interface)
- LSU detailed design
- Debug

## File Headers

For the time being everything is restricted with all rights reserved:

```
// Author: <name>, ETH Zurich
// Date: <date>
// Description: Lorem Impsum...
//
// Copyright (C) 2017 ETH Zurich, University of Bologna
// All rights reserved.
```
