**ISA COVERAGE STATUS**
===============================

The table summarizes what’s missing in ISA functional coverage :

-  cva6 version : `8a9d7a832b7121dd6f9be61a380d1d89ebf2a5f3`

-  core-v-verid version : `f7bda8e953eb060085daa165e4d2af6865474257`

+----------------------+----------------------+------------------------------------+----------------------------------------+
| **ISA extension**    | **Cover group -      | **Missing bins/cover point**       | **Why ?**                              |
|                      | Instance**           |                                    |                                        |
+======================+======================+====================================+========================================+
|                      |                      |                                    |                                        |
|   RV32I              | rv32i_add_cg         | -  cp_rd_rs2_hazard                | -  Gcc optimization(1)                 |
|                      |                      |                                    |                                        |
|                      +----------------------+------------------------------------+----------------------------------------+
|                      |                      |                                    |                                        |
|                      | rv32i_addi_cg        | -  cp_rs1                          | -  Gcc optimization(1)                 |
|                      |                      |                                    |                                        |
|                      |                      | -  cp_rd_rs1_hazard                |                                        |
|                      |                      |                                    |                                        |
|                      |                      | -  cp_immi_value                   |                                        |
|                      |                      |                                    |                                        |
|                      |                      | -  cross_rs1_immi_value            |                                        |
|                      |                      |                                    |                                        |
|                      +----------------------+------------------------------------+----------------------------------------+
|                      |                      |                                    |                                        |
|                      | rv32i_jal_cg         | -  cp_rd_toggle                    | -  Cover pc addresses (pma)            |
|                      |                      |                                    |                                        |
|                      |                      | -  cp_immj_value                   | -  Enable interrupt tests              |
|                      |                      |                                    |                                        |
|                      +----------------------+------------------------------------+----------------------------------------+
|                      |                      |                                    |                                        |
|                      | rv32i_jalr_cg        | -  cp_rd_toggle                    | -  Cover pc addresses (pma)            |
|                      |                      |                                    |                                        |
|                      |                      | -  cp_rd_value                     | -  Cover pc addresses (pma)            |
|                      |                      |                                    |                                        |
|                      |                      | -  cp_rd_rs1_hazard                | -  Enable interrupt tests              |
|                      |                      |                                    |                                        |
|                      +----------------------+------------------------------------+----------------------------------------+
|                      |                      |                                    |                                        |
|                      | rv32i_lb_cg          | -  *.cp_rs1_value                  | -  Cover load addresses (pma)          |
|                      |                      |                                    |                                        |
|                      | rv32i_lh_cg          | -  *.cp_rs1                        |                                        |
|                      |                      |                                    |                                        |
|                      | rv32i_lbu_cg         | -  *.cp_rd_rs1_hazard              |                                        |
|                      |                      |                                    |                                        |
|                      | rv32i_lhu_cg         | -  *.cp_rs1_toggle                 |                                        |
|                      |                      |                                    |                                        |
|                      | rv32i_lw_cg          | -  *.cross_rs1_immi_value          |                                        |
|                      |                      |                                    |                                        |
|                      +----------------------+------------------------------------+----------------------------------------+
|                      |                      |                                    |                                        |
|                      | rv32i_sb_cg          | -  *.cp_rs1                        | -  Cover store addresses (pma)         |
|                      |                      |                                    |                                        |
|                      | rv32i_sh_cg          | -  *.cp_rs1_toggle                 |                                        |
|                      |                      |                                    |                                        |
|                      | rv32i_sw_cg          | -  *.cp_rd_rs1_hazard              |                                        |
|                      |                      |                                    |                                        |
|                      +----------------------+------------------------------------+----------------------------------------+
|                      |                      |                                    |                                        |
|                      | rv32i_wfi_cg         | -  cp_executed                     | -  Enable interrupt tests              |
|                      |                      |                                    |                                        |
+----------------------+----------------------+------------------------------------+----------------------------------------+
|                      |                      |                                    |                                        |
|   RV32C              | rv32c_j_cg           | -  *.cp_imm_value                  | -  Enable interrupt tests              |
|                      |                      |                                    |                                        |
|                      | rv32c_jal_cg         |                                    |                                        |
|                      |                      |                                    |                                        |
|                      +----------------------+------------------------------------+----------------------------------------+
|                      |                      |                                    |                                        |
|                      | rv32c_jr_cg          | -  *.cp_rs1_toggle                 | -  Cover pc addresses (pma)            |
|                      |                      |                                    |                                        |
|                      | rv32c_jalr_cg        |                                    |                                        |
|                      |                      |                                    |                                        |
|                      +----------------------+------------------------------------+----------------------------------------+
|                      |                      |                                    |                                        |
|                      | rv32c_lw_cg          | -  *.cp_rs1_value                  | -  Cover load addresses (pma)          |
|                      |                      |                                    |                                        |
|                      |                      | -  *.cp_rs1_toggle                 |                                        |
|                      |                      |                                    |                                        |
|                      +----------------------+------------------------------------+----------------------------------------+
|                      |                      |                                    |                                        |
|                      | rv32c_sw_cg          | -  *.cp_rs1_value                  | -  Cover store addresses (pma)         |
|                      |                      |                                    |                                        |
|                      |                      | -  *.cp_rs1_toggle                 |                                        |
|                      |                      |                                    |                                        |
+----------------------+----------------------+------------------------------------+----------------------------------------+
|                      |                      |                                    |                                        |
|   RV32Zcb            | rv32zcb_lbu_cg       | -  *.cp_rs1_value                  | -  Cover load addresses (pma)          |
|                      |                      |                                    |                                        |
|                      | rv32zcb_lhu_cg       | -  *.cp_rs1_toggle                 |                                        |
|                      |                      |                                    |                                        |
|                      | rv32zcb_lh_cg        |                                    |                                        |
|                      |                      |                                    |                                        |
|                      +----------------------+------------------------------------+----------------------------------------+
|                      |                      |                                    |                                        |
|                      | rv32zcb_sb_cg        | -  *.cp_rs1_value                  | -  Cover store addresses (pma)         |
|                      |                      |                                    |                                        |
|                      | rv32zcb_sh_cg        | -  *.cp_rs1_toggle                 |                                        |
|                      |                      |                                    |                                        |
+----------------------+----------------------+------------------------------------+----------------------------------------+
|                      |                      |                                    |                                        |
|   RV32Zbb            | rv32zbb_clz_cg       | -  *.cp_rd_toggle                  | -  Bug on the ISACOV coverage model    |
|                      |                      |                                    |                                        |
|                      | rv32zbb_cpop_cg      |                                    |                                        |
|                      |                      |                                    |                                        |
|                      | rv32zbb_ctz_cg       |                                    |                                        |
|                      |                      |                                    |                                        |
|                      +----------------------+------------------------------------+----------------------------------------+
|                      |                      |                                    |                                        |
|                      | rv32zbb_sext_b_cg    | -  *.cp_rd_rs_hazard               | -  Gcc optimization(1)                 |
|                      |                      |                                    |                                        |
|                      | rv32zbb_sext_h_cg    |                                    |                                        |
|                      |                      |                                    |                                        |
|                      +----------------------+------------------------------------+----------------------------------------+
|                      |                      |                                    |                                        |
|                      | rv32zbb_zext_h_cg    | -  cp_rd_rs_hazard                 | -  Gcc optimization(1)                 |
|                      |                      |                                    |                                        |
|                      |                      | -  cp_rd_toggle                    | -  Bug on the ISACOV coverage model    |
|                      |                      |                                    |                                        |
+----------------------+----------------------+------------------------------------+----------------------------------------+
|                      |                      |                                    |                                        |
|   RV32ZBC            | rv32zbc_clmulh_cg    | -  cp_rd_toggle                    | -  Need a test                         |
|                      |                      |                                    |                                        |
|                      |                      |                                    |                                        |
+----------------------+----------------------+------------------------------------+----------------------------------------+
|                      |                      |                                    |                                        |
|   RV32ZBS            | rv32zbs_bset_cg      | -  *.cp_rd_value                   | -  Instruction limitation              |
|                      |                      |                                    |                                        |
|                      | rv32zbs_bseti_cg     |                                    |                                        |
|                      |                      |                                    |                                        |
+----------------------+----------------------+------------------------------------+----------------------------------------+
|                      |                      |                                    |                                        |
|   Instruction        | rev32_seq_cg         | -  cross_seq*                      | -  Enable interrupt                    |
|   execution          |                      |                                    |                                        |
|   sequences          |                      |                                    | -  A lot of cross combination          |
|                      |                      |                                    |                                        |
+----------------------+----------------------+------------------------------------+----------------------------------------+


**Conventions and Terminology :**

*Gcc optimization(1)* : The gcc optimize the assembly code to reduce the code size, it changed the normal instructions to compressed ones if it possible.
