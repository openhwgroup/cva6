.. Licensed under the Solderpad Hardware Licence, Version 2.1 (the "License");
.. you may not use this file except in compliance with the License.
.. SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
.. You may obtain a copy of the License at https://solderpad.org/licenses/

.. Author: Munail Waqar, 10xEngineers
.. Date: 03.05.2025
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

.. _cva6_riscv_instructions_RV32Zkne:

*Applicability of this chapter to configurations:*

.. csv-table::
   :widths: auto
   :align: left
   :header: "Configuration", "Implementation"

   "CV32A60AX", "Implemented extension"
   "CV64A6_MMU", "Implemented extension"

=============================
RVZkne: NIST Suite: AES Encryption
=============================

The following instructions comprise the Zkne extension:

Encryption instructions
--------------------
The Encryption instructions (Zkne) provide support and acceleration for AES encryption and key expansion.

+-----------+-----------+----------------------------+
| RV32      | RV64      | Mnemonic                   |
+===========+===========+============================+
| ✔         |           | aes32esi rd, rs1, rs2, bs  |
+-----------+-----------+----------------------------+
| ✔         |           | aes32esmi rd, rs1, rs2, bs |
+-----------+-----------+----------------------------+
|           | ✔         | aes64es rd, rs1, rs2       |
+-----------+-----------+----------------------------+
|           | ✔         | aes64esm rd, rs1, rs2      |
+-----------+-----------+----------------------------+

RV32 specific instructions
~~~~~~~~~~~~~~~~~~~~~~~~~~


- **AES32ESI**: AES final round encryption instruction for RV32

    **Format**: aes32esi rd, rs1, rs2, bs

    **Description**: This instruction sources a single byte from rs2 according to bs. To this it applies the forward AES SBox operation, before XORing the result with rs1.

    **Pseudocode**: X(rd) = X(rs1)[31..0] ^ rol32((0x000000 @ aes_sbox_fwd((X(rs2)[31..0] >> bs*8)[7..0])), unsigned(bs*8));

    **Invalid values**: NONE

    **Exception raised**: NONE

- **AES32ESMI**: AES middle round encryption instruction for RV32.

    **Format**: aes32esmi rd, rs1, rs2, bs

    **Description**: This instruction sources a single byte from rs2 according to bs. To this it applies the forward AES SBox operation, and a partial forward MixColumn, before XORing the result with rs1.

    **Pseudocode**: X(rd) = X(rs1)[31..0] ^ rol32(aes_mixcolumn_byte_fwd(aes_sbox_fwd((X(rs2)[31..0] >> bs*8)[7..0])), unsigned(bs*8));

    **Invalid values**: NONE

    **Exception raised**: NONE

RV64 specific instructions
~~~~~~~~~~~~~~~~~~~~~~~~~~	

- **AES64ES**: AES final round encryption instruction for RV64.

    **Format**: aes64es rd, rs1, rs2

    **Description**: Uses the two 64-bit source registers to represent the entire AES state, and produces half of the next round output, applying the ShiftRows and SubBytes steps.

    **Pseudocode**: X(rd) = aes_apply_fwd_sbox_to_each_byte(aes_rv64_shiftrows_fwd(X(rs2)[63..0], X(rs1)[63..0]));

    **Invalid values**: NONE

    **Exception raised**: NONE

- **AES64ESM**: AES middle round encryption instruction for RV64.

    **Format**: aes64esm rd, rs1, rs2

    **Description**: Uses the two 64-bit source registers to represent the entire AES state, and produces half of the next round output, applying the ShiftRows, SubBytes and MixColumns steps.

    **Pseudocode**: X(rd) = aes_mixcolumn_fwd(aes_apply_fwd_sbox_to_each_byte(aes_rv64_shiftrows_fwd(X(rs2)[63..0], X(rs1)[63..0]))[63..32])
                            @ 
                            aes_mixcolumn_fwd(aes_apply_fwd_sbox_to_each_byte(aes_rv64_shiftrows_fwd(X(rs2)[63..0], X(rs1)[63..0]))[31..0]);

    **Invalid values**: NONE

    **Exception raised**: NONE


Key Schedule instructions
--------------------------------

+-----------+-----------+-----------------------+
| RV32      | RV64      | Mnemonic              |
+===========+===========+=======================+
|           | ✔         | aes64ks1i rd, rs      |
+-----------+-----------+-----------------------+
|           | ✔         | aes64ks2 rd, rs       |
+-----------+-----------+-----------------------+

RV64 specific Instructions
~~~~~~~~~~~~~~~~~~~~~~~~~~

- **AES64KS1I**: This instruction implements part of the KeySchedule operation for the AES Block cipher involving the SBox operation.

    **Format**: aes64ks1i rd, rs1, rnum

    **Description**: This instruction implements the rotation, SubBytes and Round Constant addition steps of the AES block cipher Key Schedule. Note that rnum must be in the range 0x0..0xA.

    **Pseudocode**: if(unsigned(rnum) > A) {
                        X(rd) = 64'b0;
                    } else {
                        tmp = if (rnum ==0xA)
                                X(rs1)[63..32] 
                               else 
                                ror32(X(rs1)[63..32], 8)
                        X(rd) = (aes_subword_fwd(tmp) ^ aes_decode_rcon(rnum)) @ (aes_subword_fwd(tmp) ^ aes_decode_rcon(rnum));

    **Invalid values**: NONE

    **Exception raised**: NONE

- **AES64KS2**: This instruction implements part of the KeySchedule operation for the AES Block cipher.

    **Format**: aes64ks2 rd, rs1, rs2

    **Description**: This instruction implements the additional XORing of key words as part of the AES block cipher Key Schedule.

    **Pseudocode**: X(rd) = (X(rs1)[63..32] ^ X(rs2)[31..0] ^ X(rs2)[63..32]) @ (X(rs1)[63..32] ^ X(rs2)[31..0]);

    **Invalid values**: NONE

    **Exception raised**: NONE
