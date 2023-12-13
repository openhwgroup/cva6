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

.. _cva6_riscv_instructions_RVZifencei:

*Applicability of this chapter to configurations:*

This chapter is applicable to all CVA6 configurations.

**Note**: RV32Zifencei and RV64Zifencei are identical.


RVZifencei Instruction-Fetch Fence
--------------------------------------

- **FENCE.I**: Fence Instruction

    **Format**: fence.i

    **Description**: The FENCE.I instruction is used to synchronize the instruction and data streams. RISC-V does not guarantee that stores to instruction memory will be made visible to instruction fetches on the same RISC-V hart until a FENCE.I instruction is executed. A FENCE.I instruction only ensures that a subsequent instruction fetch on a RISC-V hart will see any previous data stores already visible to the same RISC-V hart.

    **Pseudocode**: Fence(Store, Fetch)

    **Invalid values**: NONE

    **Exception raised**: NONE

