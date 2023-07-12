**ISACOV MISSING COVERAGE**
===============================

The table blow resume what’s missing in ISACOV agent fucntionnal coverage :

+----------------------+------------------------------------+----------------------------------------+
| **Cover group -      | **Missing bins/cover point**       | **Why ?**                              |
| Instance**           |                                    |                                        |
+======================+====================================+========================================+
| cg_executed_type     | -  rv32c_ebreak_cg.cp_executed     | -  RVFI limitation\*                   | 
|                      |                                    |                                        |
| -  rv32c_ebreak_cg   | -  rv32i_dret_cg.cp_executed       |                                        |
|                      |                                    |                                        |
| -  rv32i_dret_cg     | -  rv32i_ebreak_cg.cp_executed     |                                        |
|                      |                                    |                                        |
| -  rv32i_ebreak_cg   | -  rv32i_ecall_cg.cp_executed      |                                        |
|                      |                                    |                                        |
| -  rv32i_ecall_cg    | -  rv32i_wfi_cg.cp_executed        |                                        |
|                      |                                    |                                        |
| -  rv32i_wfi_cg      |                                    |                                        |
+----------------------+------------------------------------+----------------------------------------+
| cg_sequential        | -  cp_instr, cp_instr_prev_x2      | -  RVFI limitation\*                   | 
|                      |                                    |                                        |
|                      | -  cp_group, cp_group_pipe_x2      | -  RVFI limitation\*                   |
|                      |                                    |                                        |
|                      | -  cp_csr                          | -  RVFI limitation\*                   | 
|                      |                                    |                                        |
|                      | -  cross_seq_instr_x2              | -  RVFI limitation\*                   |
|                      |                                    |                                        |
|                      | -  cross_seq_group_x2              | -  RVFI limitation\*                   |
|                      |                                    |                                        |
|                      | -  cross_seq_gpr_raw_hazard        | -  RVFI limitation\*                   |        
|                      |                                    |                                        |
|                      | -  cross_seq_csr_hazard_x2         | -  RVFI limitation\*                   |
|                      |                                    |                                        |
+----------------------+------------------------------------+----------------------------------------+
| cg_csritype          | -  \*.cp_csr                       | -  Need CSR tests*\*                   |
|                      |                                    |                                        |
| -                    |                                    |                                        |
|  rv32zicsr_csrrwi_cg |                                    |                                        |
|                      |                                    |                                        |
| -                    |                                    |                                        |
|  rv32zicsr_csrrsi_cg |                                    |                                        |
|                      |                                    |                                        |
| -                    |                                    |                                        |
|  rv32zicsr_csrrci_cg |                                    |                                        |
+----------------------+------------------------------------+----------------------------------------+
| cg_cr_j              | -  rv32c_jalr_cg.cp_rs1_value      | -  boot_addr != 0x0                    |
|                      |                                    |                                        |
| -  rv32c_jalr_cg     | -  rv32c_jr_cg.cp_rs1_value        | -  boot_addr != 0x0                    |       
|                      |                                    |                                        |
| -  rv32c_jr_cg       | -  rv32c_jalr_cg.cp_rs1_toggle     | -  Tests needed**\*                    |
|                      |                                    |                                        |
|                      | -  rv32c_jr_cg.cp_rs1_toggle       | -  Tests needed**\*                    |
|                      |                                    |                                        |
+----------------------+------------------------------------+----------------------------------------+
| cg_csritype          | -  \*.cp_csr                       | -  Need CSR tests*\*                   |
|                      |                                    |                                        |
| -                    |                                    |                                        |
|   rv32zicsr_csrrw_cg |                                    |                                        |
|                      |                                    |                                        |
| -                    |                                    |                                        |
|   rv32zicsr_csrrs_cg |                                    |                                        |
|                      |                                    |                                        |
| -                    |                                    |                                        |
|   rv32zicsr_csrrc_cg |                                    |                                        |
+----------------------+------------------------------------+----------------------------------------+
| cg_cb_shift          | -  \*.cp_rs1                       | -  UVM_BUG #1425                       |
|                      |                                    |                                        |
| -  rv32c_srli_cg     |                                    |                                        |
|                      |                                    |                                        |
| -  rv32c_srai_cg     |                                    |                                        |
+----------------------+------------------------------------+----------------------------------------+
| cg_cj                | -  \*.cp_imm_value                 | -  imm = 0x0 (infinite loop)           |   
|                      |                                    |                                        |
| -  rv32c_j_cg        |                                    |                                        |
|                      |                                    |                                        |
| -  rv32c_jal_cg      |                                    |                                        |
+----------------------+------------------------------------+----------------------------------------+
| cg_itype_load        | -  rv32i_lbu_cg.cp_rd_toggle       | -  LBU,LHU limitation                  |
|                      |                                    |                                        |
| -  rv32i_lbu_cg      | -  rv32i_lhu_cg.cp_rd_toggle       |                                        |
|                      |                                    |                                        |
| -  rv32i_lhu_cg      |                                    |                                        |
+----------------------+------------------------------------+----------------------------------------+
| cg_jtype             | -  cp_immj_value                   | -  immj = 0x0 (infinite loop)          |      
|                      |                                    |                                        |
| -  rv32i_jal_cg      | -  cp_rd_toggle                    | -  Tests needed***\*                   |
+----------------------+------------------------------------+----------------------------------------+
| cg_cb_andi           | -  cp_rs1                          | -  UVM_BUG #1425                       |
|                      |                                    |                                        |
| -  rv32c_andi_cg     |                                    |                                        |
+----------------------+------------------------------------+----------------------------------------+
| cg_cr                | -  cp_rs1_toggle                   | -  c.mv should not have rs1 (UVM_BUG)  |                 
|                      |                                    |                                        |
| -  rv32c_mv_cg       |                                    |                                        |
+----------------------+------------------------------------+----------------------------------------+
| cg_utype             | -  rv32i_lui_cg.cp_immu_value      | -  Test needed**\*                     |
|                      |                                    |                                        |
| -  rv32i_auipc_cg    |                                    |                                        |
+----------------------+------------------------------------+----------------------------------------+
| cg_rtype_slt         | -  \*.cross_rd_rs1_rs2             | -  Test needed***\*                    |
|                      |                                    |                                        |
| -  rv32i_sltu_cg     |                                    |                                        |
|                      |                                    |                                        |
| -  rv32i_slt_cg      |                                    |                                        |
+----------------------+------------------------------------+----------------------------------------+
| cg_rtype_shift       | -  \*.cross_rd_rs1_rs2             | -  Test needed***\*                    |
|                      |                                    |                                        |
| -  rv32i_sra_cg      |                                    |                                        |
|                      |                                    |                                        |
| -  rv32i_srl_cg      |                                    |                                        |
|                      |                                    |                                        |
| -  rv32i_sll_cg      |                                    |                                        |
+----------------------+------------------------------------+----------------------------------------+
| cg_rtype             | -  \*.cross_rd_rs1_rs2             | -  Test needed***\*                    |
|                      |                                    |                                        |
| -  rv32i_add_cg      |                                    |                                        |
|                      |                                    |                                        |
| -  rv32i_sub_cg      |                                    |                                        |
|                      |                                    |                                        |
| -  rv32i_xor_cg      |                                    |                                        |
|                      |                                    |                                        |
| -  rv32i_and_cg      |                                    |                                        |
|                      |                                    |                                        |
| -  rv32i_or_cg       |                                    |                                        |
|                      |                                    |                                        |
| -  rv32m_mul_cg      |                                    |                                        |
|                      |                                    |                                        |
| -  rv32m_mulh_cg     |                                    |                                        |
|                      |                                    |                                        |
| -  rv32m_mulhu_cg    |                                    |                                        |
|                      |                                    |                                        |
| -  rv32m_mulhsu_cg   |                                    |                                        |
|                      |                                    |                                        |
| -  rv32m_rem_cg      |                                    |                                        |
|                      |                                    |                                        |
| -  rv32m_remu_cg     |                                    |                                        |
|                      |                                    |                                        |
| -  rv32m_div_cg      |                                    |                                        |
|                      |                                    |                                        |
| -  rv32m_divu_cg     |                                    |                                        | 
+----------------------+------------------------------------+----------------------------------------+            
| cg_itype             | -  rv32i_jalr_cg.cp_rs1            | -  Test needed**\*                     |
|                      |                                    |                                        |
| -  rv32i_jalr_cg     | -  rv32i_jalr_cg.cp_rd             | -  rd = 0x0 it’s a c.jalr (UVM_BUG)    |          
|                      |                                    |                                        |
| -  rv32i_andi_cg     | -  rv32i_jalr_cg.cp_rd_rs1_hazard  | -  imm = 0x0 for jalr infinite loop    |           
|                      |                                    |                                        |
| -  rv32i_ori_cg      | -  rv32i_jalr_cg.cp_rs1_value      | -  infinite loop                       |
|                      |                                    |                                        |
| -  rv32i_xori_cg     | -  rv32i_jalr_cg.cp_rd_value       |                                        |
|                      |                                    |                                        |
|                      | -  rv32i_jalr_cg.cp_rd_toggle      |                                        |
+----------------------+------------------------------------+----------------------------------------+            
| cg_btype             | -  \*.cross_rs1_rs2                | -  Test needed***\*                    |
|                      |                                    |                                        |
| -  rv32i_bge_cg      |                                    |                                        |
|                      |                                    |                                        |
| -  rv32i_bltu_cg     |                                    |                                        |
|                      |                                    |                                        |
| -  rv32i_beq_cg      |                                    |                                        |
|                      |                                    |                                        |
| -  rv32i_bne_cg      |                                    |                                        |
|                      |                                    |                                        |
| -  rv32i_blt_cg      |                                    |                                        |
|                      |                                    |                                        |
| -  rv32i_bgeu_cg     |                                    |                                        |
+----------------------+------------------------------------+----------------------------------------+
| cg_itype_slt         | -  cross_rs1_immi_value            | -  Test needed**\*                     |
|                      |                                    |                                        |
| -  rv32i_slti_cg     |                                    |                                        |
+----------------------+------------------------------------+----------------------------------------+
| cg_itype_shift       | -  rv32i_slli_cg.cp_rd_rs1_hazard  | -  Test needed**\*                     |
|                      |                                    |                                        |
| -  rv32i_slli_cg     | -  rv32i_srli_cg.cp_rd_rs1_hazard  |                                        |
|                      |                                    |                                        |
| -  rv32i_srli_cg     | -  rv32i_slli_cg.cross_rd_rs1      |                                        |
|                      |                                    |                                        |
| -  rv32i_srai_cg     | -  rv32i_srli_cg. cross_rd_rs1     |                                        |
+----------------------+------------------------------------+----------------------------------------+            

**Conventions and Terminology :**

*RVFI limitation\** : the RVFI in the CVA6 get his information from the commit stage, that mean the ISACOV can gat onlt information of valid instruction, so any instruction that raise an exception can’t be cover.

*Need CSR tests*\** : we can get what has been done in CSR verification task.

*Test needed*\*** : the test is feasible.

*Test needed*\**** : the test isn’t feasible, because it’s going to take a
lot of time to write (a lot of combination to cover).
