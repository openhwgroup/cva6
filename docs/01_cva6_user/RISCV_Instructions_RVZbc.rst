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

.. _cva6_riscv_instructions_RV32Zbc:

*Applicability of this chapter to configurations:*

.. csv-table::
   :widths: auto
   :align: left
   :header: "Configuration", "Implementation"

   "CV32A60AX", "Implemented extension"
   "CV32A60X", "Implemented extension"

   
=================================
RVZbc: Carry-less multiplication
=================================
Carry-less multiplication is the multiplication in the polynomial ring over GF(2).

clmul produces the lower half of the carry-less product and clmulh produces the upper half of the 2✕XLEN carry-less product.

clmulr produces bits 2✕XLEN−2:XLEN-1 of the 2✕XLEN carry-less product.

The following instructions (and pseudoinstructions) comprise the Zbc extension:

+-----------+-----------+-----------------------+
| RV32      | RV64      | Mnemonic              |
+===========+===========+=======================+
| ✔         | ✔         | clmul rd, rs1, rs2    |
+-----------+-----------+-----------------------+
| ✔         | ✔         | clmulh rd, rs1, rs2   |
+-----------+-----------+-----------------------+
| ✔         | ✔         | clmulr rd, rs1, rs2   |
+-----------+-----------+-----------------------+

RV32 and RV64 Instructions
--------------------------

- **CLMUL**: Carry-less multiply (low-part)

    **Format**: clmul rd, rs1, rs2

    **Description**: clmul produces the lower half of the 2.XLEN carry-less product.

    **Pseudocode**: foreach (i from 1 to xlen by 1) { output = if ((rs2 >> i) & 1) then output ^ (rs1 << i); else output; } 

    **Invalid values**: NONE

    **Exception raised**: NONE

- **CLMULH**: Carry-less multiply (high-part)

    **Format**: clmulh rd, rs1, rs2

    **Description**: clmulh produces the upper half of the 2.XLEN carry-less product.

    **Pseudocode**: foreach (i from 1 to xlen by 1) { output = if ((rs2_val >> i) & 1) then output ^ (rs1_val >> (xlen - i)) else output }

    **Invalid values**: NONE

    **Exception raised**: NONE

- **CLMULR**: Carry-less multiply (reversed)

    **Format**: clmulr rd, rs1, rs2

    **Description**: clmulr produces bits 2.XLEN-2:XLEN-1 of the 2.XLEN carry-less product.

    **Pseudocode**: foreach (i from 0 to (xlen - 1) by 1) { output = if ((rs2_val >> i) & 1) then output ^ (rs1_val >> (xlen - i - 1)) else output}

    **Invalid values**: NONE

    **Exception raised**: NONE








