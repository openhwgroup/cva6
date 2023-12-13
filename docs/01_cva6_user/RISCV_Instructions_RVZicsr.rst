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

.. _cva6_riscv_instructions_RVZicsr:

*Applicability of this chapter to configurations:*

This chapter is applicable to all CVA6 configurations.

**Note**: RV32Zicsr and RV64Zicsr are identical.

RVZicsr Control and Status Register Instructions
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
