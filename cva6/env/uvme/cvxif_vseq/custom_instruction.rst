..
   Copyright (c) 2023 OpenHW Group

   Copyright (c) 2023 Thales DIS design services SAS


   SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1

..

Custom Instruction to challenge CV-X-IF protocol
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
This section describes some custom instruction, for stress or challenge the CV-X-IF protocol for the 3 implemented interfaces, it's just to interact with the cvxif agent.
All instructions use opcode `CUSTOM_3`(0x7b, 0b111_1011).

- **CUS_ADD**: Custom Add

    **Format**: cus_add rd, rs1, rs2 -> |0000000|rs2|rs1|001|rd|111_1011|

    **Description**: add register rs1 to rs2, and store the result in rd (works for all privilege modes).

    **Pseudocode**: x[rd] = x[rs1] + x[rs2]

    **Invalid values**: NONE

    **Exception raised**: Illegal instruction exception is raised if rs_valid != 2'b11 && rs_valid != 3'b111.

- **CUS_NOP**: Custom No Operation

    **Format**: cus_nop -> |0000000000000000000000000|111_1011|

    **Description**: do nothing, it's just a hint instruction.

    **Pseudocode**: cus_nop

    **Invalid values**: NONE

    **Exception raised**: NONE

- **CUS_ADD_RS3**: Custom Add

    **Format**: cus_add_rs3 rd, rs1, rs2, rs3 -> |rs3|01|rs2|rs1|000|rd|111_1011|

    **Description**: add register rs1 to rs2 then the result to rs3, and store the result in register rd (works for all privilege modes).

    **Pseudocode**: x[rd] = x[rs1] + x[rs2] + x[rs3]

    **Invalid values**: NONE

    **Exception raised**: Illegal instruction exception is raised if rs_valid != 3'b111.

- **CUS_S_ADD**: Custom Supervisor Add

    **Format**: add rd, rs1, rs2 -> |0000110|rs2|rs1|000|rd|111_1011|

    **Description**: add register rs1 to rs2, and store the result in register rd (works only in Supervisor mode).

    **Pseudocode**: x[rd] = x[rs1] + x[rs2]

    **Invalid values**: NONE

    **Exception raised**: Illegal instruction exception is raised if the privilege mode isn't Supervisor mode, or rs_valid != 2'b11 && rs_valid != 3'b111.

- **CUS_U_ADD**: Custom User Add

    **Format**: add rd, rs1, rs2 -> |0000010|rs2|rs1|000|rd|111_1011|

    **Description**: add register rs1 to rs2, and store the result in register rd (works only in User mode).

    **Pseudocode**: x[rd] = x[rs1] + x[rs2]

    **Invalid values**: NONE

    **Exception raised**: Illegal instruction exception is raised if the privilege mode isn't User mode, or rs_valid != 2'b11 && rs_valid != 3'b111.

- **CUS_ADD_MULTI**: Custom Multicycle Add

    **Format**: addi rd, rs1, rs2 -> |0001000|rs2|rs1|000|rd|111_1011|

    **Description**: add register rs1 to rs2, and store the result in rd (works for all privilege mode).

    **Pseudocode**: x[rd] = x[rs1] + x[rs2]

    **Invalid values**: NONE

    **Exception raised**: Illegal instruction exception is raised if rs_valid != 2'b11 && rs_valid != 3'b111.

- **CUS_EXC**: Custom Exception

    **Format**: cus_exc rs1 -> |1100000|00000|rs1|010|00000|111_1011|

    **Description**: raise an exception.

    **Pseudocode**: mcause[5:0] = rs1

    **Invalid values**: NONE

    **Exception raised**: raise an exception based on the rs1 register address.

When a CV-X-IF exception is raised, mcause[5:0] of the corresponding CORE-V hart is assumed set to exccode[5:0] of CV-X-IF.
