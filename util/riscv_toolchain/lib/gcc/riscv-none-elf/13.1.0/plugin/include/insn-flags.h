/* Generated automatically by the program `genflags'
   from the machine description file `md'.  */

#ifndef GCC_INSN_FLAGS_H
#define GCC_INSN_FLAGS_H

#define HAVE_addsf3 (TARGET_HARD_FLOAT || TARGET_ZFINX)
#define HAVE_adddf3 ((TARGET_HARD_FLOAT || TARGET_ZFINX) && (TARGET_DOUBLE_FLOAT || TARGET_ZDINX))
#define HAVE_addhf3 ((TARGET_HARD_FLOAT || TARGET_ZFINX) && (TARGET_ZFH || TARGET_ZHINX))
#define HAVE_addsi3 1
#define HAVE_adddi3 (TARGET_64BIT)
#define HAVE_subsf3 (TARGET_HARD_FLOAT || TARGET_ZFINX)
#define HAVE_subdf3 ((TARGET_HARD_FLOAT || TARGET_ZFINX) && (TARGET_DOUBLE_FLOAT || TARGET_ZDINX))
#define HAVE_subhf3 ((TARGET_HARD_FLOAT || TARGET_ZFINX) && (TARGET_ZFH || TARGET_ZHINX))
#define HAVE_subdi3 (TARGET_64BIT)
#define HAVE_subsi3 1
#define HAVE_negdi2 (TARGET_64BIT)
#define HAVE_negsi2 1
#define HAVE_mulsf3 ((TARGET_HARD_FLOAT  || TARGET_ZFINX) && (TARGET_HARD_FLOAT || TARGET_ZFINX))
#define HAVE_muldf3 ((TARGET_HARD_FLOAT  || TARGET_ZFINX) && (TARGET_DOUBLE_FLOAT || TARGET_ZDINX))
#define HAVE_mulhf3 ((TARGET_HARD_FLOAT  || TARGET_ZFINX) && (TARGET_ZFH || TARGET_ZHINX))
#define HAVE_mulsi3 (TARGET_ZMMUL || TARGET_MUL)
#define HAVE_muldi3 ((TARGET_ZMMUL || TARGET_MUL) && TARGET_64BIT)
#define HAVE_smuldi3_highpart ((TARGET_ZMMUL || TARGET_MUL) && TARGET_64BIT)
#define HAVE_umuldi3_highpart ((TARGET_ZMMUL || TARGET_MUL) && TARGET_64BIT)
#define HAVE_usmuldi3_highpart ((TARGET_ZMMUL || TARGET_MUL) && TARGET_64BIT)
#define HAVE_smulsi3_highpart ((TARGET_ZMMUL || TARGET_MUL) && !TARGET_64BIT)
#define HAVE_umulsi3_highpart ((TARGET_ZMMUL || TARGET_MUL) && !TARGET_64BIT)
#define HAVE_usmulsi3_highpart ((TARGET_ZMMUL || TARGET_MUL) && !TARGET_64BIT)
#define HAVE_divsi3 (TARGET_DIV)
#define HAVE_udivsi3 (TARGET_DIV)
#define HAVE_modsi3 (TARGET_DIV)
#define HAVE_umodsi3 (TARGET_DIV)
#define HAVE_divdi3 (TARGET_DIV && TARGET_64BIT)
#define HAVE_udivdi3 (TARGET_DIV && TARGET_64BIT)
#define HAVE_moddi3 (TARGET_DIV && TARGET_64BIT)
#define HAVE_umoddi3 (TARGET_DIV && TARGET_64BIT)
#define HAVE_divsf3 (((TARGET_HARD_FLOAT || TARGET_ZFINX) && TARGET_FDIV) && (TARGET_HARD_FLOAT || TARGET_ZFINX))
#define HAVE_divdf3 (((TARGET_HARD_FLOAT || TARGET_ZFINX) && TARGET_FDIV) && (TARGET_DOUBLE_FLOAT || TARGET_ZDINX))
#define HAVE_divhf3 (((TARGET_HARD_FLOAT || TARGET_ZFINX) && TARGET_FDIV) && (TARGET_ZFH || TARGET_ZHINX))
#define HAVE_sqrtsf2 (((TARGET_HARD_FLOAT || TARGET_ZFINX) && TARGET_FDIV) && (TARGET_HARD_FLOAT || TARGET_ZFINX))
#define HAVE_sqrtdf2 (((TARGET_HARD_FLOAT || TARGET_ZFINX) && TARGET_FDIV) && (TARGET_DOUBLE_FLOAT || TARGET_ZDINX))
#define HAVE_sqrthf2 (((TARGET_HARD_FLOAT || TARGET_ZFINX) && TARGET_FDIV) && (TARGET_ZFH || TARGET_ZHINX))
#define HAVE_fmasf4 (TARGET_HARD_FLOAT || TARGET_ZFINX)
#define HAVE_fmadf4 ((TARGET_HARD_FLOAT || TARGET_ZFINX) && (TARGET_DOUBLE_FLOAT || TARGET_ZDINX))
#define HAVE_fmahf4 ((TARGET_HARD_FLOAT || TARGET_ZFINX) && (TARGET_ZFH || TARGET_ZHINX))
#define HAVE_fmssf4 ((TARGET_HARD_FLOAT  || TARGET_ZFINX) && (TARGET_HARD_FLOAT || TARGET_ZFINX))
#define HAVE_fmsdf4 ((TARGET_HARD_FLOAT  || TARGET_ZFINX) && (TARGET_DOUBLE_FLOAT || TARGET_ZDINX))
#define HAVE_fmshf4 ((TARGET_HARD_FLOAT  || TARGET_ZFINX) && (TARGET_ZFH || TARGET_ZHINX))
#define HAVE_fnmssf4 ((TARGET_HARD_FLOAT  || TARGET_ZFINX) && (TARGET_HARD_FLOAT || TARGET_ZFINX))
#define HAVE_fnmsdf4 ((TARGET_HARD_FLOAT  || TARGET_ZFINX) && (TARGET_DOUBLE_FLOAT || TARGET_ZDINX))
#define HAVE_fnmshf4 ((TARGET_HARD_FLOAT  || TARGET_ZFINX) && (TARGET_ZFH || TARGET_ZHINX))
#define HAVE_fnmasf4 (TARGET_HARD_FLOAT || TARGET_ZFINX)
#define HAVE_fnmadf4 ((TARGET_HARD_FLOAT || TARGET_ZFINX) && (TARGET_DOUBLE_FLOAT || TARGET_ZDINX))
#define HAVE_fnmahf4 ((TARGET_HARD_FLOAT || TARGET_ZFINX) && (TARGET_ZFH || TARGET_ZHINX))
#define HAVE_abssf2 (TARGET_HARD_FLOAT || TARGET_ZFINX)
#define HAVE_absdf2 ((TARGET_HARD_FLOAT || TARGET_ZFINX) && (TARGET_DOUBLE_FLOAT || TARGET_ZDINX))
#define HAVE_abshf2 ((TARGET_HARD_FLOAT || TARGET_ZFINX) && (TARGET_ZFH || TARGET_ZHINX))
#define HAVE_copysignsf3 (TARGET_HARD_FLOAT || TARGET_ZFINX)
#define HAVE_copysigndf3 ((TARGET_HARD_FLOAT || TARGET_ZFINX) && (TARGET_DOUBLE_FLOAT || TARGET_ZDINX))
#define HAVE_copysignhf3 ((TARGET_HARD_FLOAT || TARGET_ZFINX) && (TARGET_ZFH || TARGET_ZHINX))
#define HAVE_negsf2 (TARGET_HARD_FLOAT || TARGET_ZFINX)
#define HAVE_negdf2 ((TARGET_HARD_FLOAT || TARGET_ZFINX) && (TARGET_DOUBLE_FLOAT || TARGET_ZDINX))
#define HAVE_neghf2 ((TARGET_HARD_FLOAT || TARGET_ZFINX) && (TARGET_ZFH || TARGET_ZHINX))
#define HAVE_fminsf3 (((TARGET_HARD_FLOAT || TARGET_ZFINX) && !HONOR_SNANS (SFmode)) && (TARGET_HARD_FLOAT || TARGET_ZFINX))
#define HAVE_fmindf3 (((TARGET_HARD_FLOAT || TARGET_ZFINX) && !HONOR_SNANS (DFmode)) && (TARGET_DOUBLE_FLOAT || TARGET_ZDINX))
#define HAVE_fminhf3 (((TARGET_HARD_FLOAT || TARGET_ZFINX) && !HONOR_SNANS (HFmode)) && (TARGET_ZFH || TARGET_ZHINX))
#define HAVE_fmaxsf3 (((TARGET_HARD_FLOAT || TARGET_ZFINX) && !HONOR_SNANS (SFmode)) && (TARGET_HARD_FLOAT || TARGET_ZFINX))
#define HAVE_fmaxdf3 (((TARGET_HARD_FLOAT || TARGET_ZFINX) && !HONOR_SNANS (DFmode)) && (TARGET_DOUBLE_FLOAT || TARGET_ZDINX))
#define HAVE_fmaxhf3 (((TARGET_HARD_FLOAT || TARGET_ZFINX) && !HONOR_SNANS (HFmode)) && (TARGET_ZFH || TARGET_ZHINX))
#define HAVE_sminsf3 (TARGET_HARD_FLOAT || TARGET_ZFINX)
#define HAVE_smindf3 ((TARGET_HARD_FLOAT || TARGET_ZFINX) && (TARGET_DOUBLE_FLOAT || TARGET_ZDINX))
#define HAVE_sminhf3 ((TARGET_HARD_FLOAT || TARGET_ZFINX) && (TARGET_ZFH || TARGET_ZHINX))
#define HAVE_smaxsf3 (TARGET_HARD_FLOAT || TARGET_ZFINX)
#define HAVE_smaxdf3 ((TARGET_HARD_FLOAT || TARGET_ZFINX) && (TARGET_DOUBLE_FLOAT || TARGET_ZDINX))
#define HAVE_smaxhf3 ((TARGET_HARD_FLOAT || TARGET_ZFINX) && (TARGET_ZFH || TARGET_ZHINX))
#define HAVE_andsi3 (!TARGET_64BIT)
#define HAVE_iorsi3 (!TARGET_64BIT)
#define HAVE_xorsi3 (!TARGET_64BIT)
#define HAVE_anddi3 (TARGET_64BIT)
#define HAVE_iordi3 (TARGET_64BIT)
#define HAVE_xordi3 (TARGET_64BIT)
#define HAVE_one_cmplsi2 (!TARGET_64BIT)
#define HAVE_one_cmpldi2 (TARGET_64BIT)
#define HAVE_truncdfsf2 (TARGET_DOUBLE_FLOAT || TARGET_ZDINX)
#define HAVE_truncsfhf2 (TARGET_ZFHMIN || TARGET_ZHINXMIN)
#define HAVE_truncdfhf2 ((TARGET_ZFHMIN && TARGET_DOUBLE_FLOAT) || \
   (TARGET_ZHINXMIN && TARGET_ZDINX))
#define HAVE_zero_extendqihi2 1
#define HAVE_zero_extendqisi2 1
#define HAVE_zero_extendqidi2 (TARGET_64BIT)
#define HAVE_extendsidi2 (TARGET_64BIT)
#define HAVE_extendhfsf2 (TARGET_ZFHMIN || TARGET_ZHINXMIN)
#define HAVE_extendsfdf2 (TARGET_DOUBLE_FLOAT || TARGET_ZDINX)
#define HAVE_extendhfdf2 ((TARGET_ZFHMIN && TARGET_DOUBLE_FLOAT) || \
   (TARGET_ZHINXMIN && TARGET_ZDINX))
#define HAVE_fix_truncsfsi2 (TARGET_HARD_FLOAT || TARGET_ZFINX)
#define HAVE_fix_truncsfdi2 ((TARGET_HARD_FLOAT || TARGET_ZFINX) && ((TARGET_64BIT) && (TARGET_HARD_FLOAT || TARGET_ZFINX)))
#define HAVE_fix_truncdfsi2 ((TARGET_HARD_FLOAT || TARGET_ZFINX) && (TARGET_DOUBLE_FLOAT || TARGET_ZDINX))
#define HAVE_fix_truncdfdi2 ((TARGET_HARD_FLOAT || TARGET_ZFINX) && ((TARGET_64BIT) && (TARGET_DOUBLE_FLOAT || TARGET_ZDINX)))
#define HAVE_fix_trunchfsi2 ((TARGET_HARD_FLOAT || TARGET_ZFINX) && (TARGET_ZFH || TARGET_ZHINX))
#define HAVE_fix_trunchfdi2 ((TARGET_HARD_FLOAT || TARGET_ZFINX) && ((TARGET_64BIT) && (TARGET_ZFH || TARGET_ZHINX)))
#define HAVE_fixuns_truncsfsi2 ((TARGET_HARD_FLOAT  || TARGET_ZFINX) && (TARGET_HARD_FLOAT || TARGET_ZFINX))
#define HAVE_fixuns_truncsfdi2 ((TARGET_HARD_FLOAT  || TARGET_ZFINX) && ((TARGET_64BIT) && (TARGET_HARD_FLOAT || TARGET_ZFINX)))
#define HAVE_fixuns_truncdfsi2 ((TARGET_HARD_FLOAT  || TARGET_ZFINX) && (TARGET_DOUBLE_FLOAT || TARGET_ZDINX))
#define HAVE_fixuns_truncdfdi2 ((TARGET_HARD_FLOAT  || TARGET_ZFINX) && ((TARGET_64BIT) && (TARGET_DOUBLE_FLOAT || TARGET_ZDINX)))
#define HAVE_fixuns_trunchfsi2 ((TARGET_HARD_FLOAT  || TARGET_ZFINX) && (TARGET_ZFH || TARGET_ZHINX))
#define HAVE_fixuns_trunchfdi2 ((TARGET_HARD_FLOAT  || TARGET_ZFINX) && ((TARGET_64BIT) && (TARGET_ZFH || TARGET_ZHINX)))
#define HAVE_floatsisf2 (TARGET_HARD_FLOAT || TARGET_ZFINX)
#define HAVE_floatdisf2 ((TARGET_HARD_FLOAT || TARGET_ZFINX) && ((TARGET_HARD_FLOAT || TARGET_ZFINX) && (TARGET_64BIT)))
#define HAVE_floatsidf2 ((TARGET_HARD_FLOAT || TARGET_ZFINX) && (TARGET_DOUBLE_FLOAT || TARGET_ZDINX))
#define HAVE_floatdidf2 ((TARGET_HARD_FLOAT || TARGET_ZFINX) && ((TARGET_DOUBLE_FLOAT || TARGET_ZDINX) && (TARGET_64BIT)))
#define HAVE_floatsihf2 ((TARGET_HARD_FLOAT || TARGET_ZFINX) && (TARGET_ZFH || TARGET_ZHINX))
#define HAVE_floatdihf2 ((TARGET_HARD_FLOAT || TARGET_ZFINX) && ((TARGET_ZFH || TARGET_ZHINX) && (TARGET_64BIT)))
#define HAVE_floatunssisf2 (TARGET_HARD_FLOAT || TARGET_ZFINX)
#define HAVE_floatunsdisf2 ((TARGET_HARD_FLOAT || TARGET_ZFINX) && ((TARGET_HARD_FLOAT || TARGET_ZFINX) && (TARGET_64BIT)))
#define HAVE_floatunssidf2 ((TARGET_HARD_FLOAT || TARGET_ZFINX) && (TARGET_DOUBLE_FLOAT || TARGET_ZDINX))
#define HAVE_floatunsdidf2 ((TARGET_HARD_FLOAT || TARGET_ZFINX) && ((TARGET_DOUBLE_FLOAT || TARGET_ZDINX) && (TARGET_64BIT)))
#define HAVE_floatunssihf2 ((TARGET_HARD_FLOAT || TARGET_ZFINX) && (TARGET_ZFH || TARGET_ZHINX))
#define HAVE_floatunsdihf2 ((TARGET_HARD_FLOAT || TARGET_ZFINX) && ((TARGET_ZFH || TARGET_ZHINX) && (TARGET_64BIT)))
#define HAVE_lrintsfsi2 (TARGET_HARD_FLOAT || TARGET_ZFINX)
#define HAVE_lroundsfsi2 (TARGET_HARD_FLOAT || TARGET_ZFINX)
#define HAVE_lrintsfdi2 ((TARGET_HARD_FLOAT || TARGET_ZFINX) && ((TARGET_64BIT) && (TARGET_HARD_FLOAT || TARGET_ZFINX)))
#define HAVE_lroundsfdi2 ((TARGET_HARD_FLOAT || TARGET_ZFINX) && ((TARGET_64BIT) && (TARGET_HARD_FLOAT || TARGET_ZFINX)))
#define HAVE_lrintdfsi2 ((TARGET_HARD_FLOAT || TARGET_ZFINX) && (TARGET_DOUBLE_FLOAT || TARGET_ZDINX))
#define HAVE_lrounddfsi2 ((TARGET_HARD_FLOAT || TARGET_ZFINX) && (TARGET_DOUBLE_FLOAT || TARGET_ZDINX))
#define HAVE_lrintdfdi2 ((TARGET_HARD_FLOAT || TARGET_ZFINX) && ((TARGET_64BIT) && (TARGET_DOUBLE_FLOAT || TARGET_ZDINX)))
#define HAVE_lrounddfdi2 ((TARGET_HARD_FLOAT || TARGET_ZFINX) && ((TARGET_64BIT) && (TARGET_DOUBLE_FLOAT || TARGET_ZDINX)))
#define HAVE_lrinthfsi2 ((TARGET_HARD_FLOAT || TARGET_ZFINX) && (TARGET_ZFH || TARGET_ZHINX))
#define HAVE_lroundhfsi2 ((TARGET_HARD_FLOAT || TARGET_ZFINX) && (TARGET_ZFH || TARGET_ZHINX))
#define HAVE_lrinthfdi2 ((TARGET_HARD_FLOAT || TARGET_ZFINX) && ((TARGET_64BIT) && (TARGET_ZFH || TARGET_ZHINX)))
#define HAVE_lroundhfdi2 ((TARGET_HARD_FLOAT || TARGET_ZFINX) && ((TARGET_64BIT) && (TARGET_ZFH || TARGET_ZHINX)))
#define HAVE_got_loadsi (Pmode == SImode)
#define HAVE_got_loaddi (Pmode == DImode)
#define HAVE_tls_add_tp_lesi (Pmode == SImode)
#define HAVE_tls_add_tp_ledi (Pmode == DImode)
#define HAVE_got_load_tls_gdsi (Pmode == SImode)
#define HAVE_got_load_tls_gddi (Pmode == DImode)
#define HAVE_got_load_tls_iesi (Pmode == SImode)
#define HAVE_got_load_tls_iedi (Pmode == DImode)
#define HAVE_auipcsi (Pmode == SImode)
#define HAVE_auipcdi (Pmode == DImode)
#define HAVE_fence 1
#define HAVE_fence_i (TARGET_ZIFENCEI)
#define HAVE_riscv_pause 1
#define HAVE_ashlsi3 1
#define HAVE_ashrsi3 1
#define HAVE_lshrsi3 1
#define HAVE_ashldi3 (TARGET_64BIT)
#define HAVE_ashrdi3 (TARGET_64BIT)
#define HAVE_lshrdi3 (TARGET_64BIT)
#define HAVE_zero_extendsidi2_shifted (TARGET_64BIT && !TARGET_ZBA \
   && ((INTVAL (operands[3]) >> INTVAL (operands[2])) == 0xffffffff))
#define HAVE_jump 1
#define HAVE_indirect_jumpsi (Pmode == SImode)
#define HAVE_indirect_jumpdi (Pmode == DImode)
#define HAVE_tablejumpsi 1
#define HAVE_tablejumpdi (TARGET_64BIT)
#define HAVE_blockage 1
#define HAVE_simple_return 1
#define HAVE_simple_return_internal 1
#define HAVE_eh_set_lr_si (! TARGET_64BIT)
#define HAVE_eh_set_lr_di (TARGET_64BIT)
#define HAVE_eh_return_internal 1
#define HAVE_sibcall_internal (SIBLING_CALL_P (insn))
#define HAVE_sibcall_value_internal (SIBLING_CALL_P (insn))
#define HAVE_call_internal 1
#define HAVE_call_value_internal 1
#define HAVE_nop 1
#define HAVE_trap 1
#define HAVE_gpr_save 1
#define HAVE_gpr_restore 1
#define HAVE_gpr_restore_return 1
#define HAVE_riscv_frflags (TARGET_HARD_FLOAT || TARGET_ZFINX)
#define HAVE_riscv_fsflags (TARGET_HARD_FLOAT || TARGET_ZFINX)
#define HAVE_riscv_mret 1
#define HAVE_riscv_sret 1
#define HAVE_riscv_uret 1
#define HAVE_stack_tiesi (!TARGET_64BIT)
#define HAVE_stack_tiedi (TARGET_64BIT)
#define HAVE_stack_protect_set_si 1
#define HAVE_stack_protect_set_di (TARGET_64BIT)
#define HAVE_stack_protect_test_si 1
#define HAVE_stack_protect_test_di (TARGET_64BIT)
#define HAVE_riscv_clean_si ((TARGET_ZICBOM) && (!TARGET_64BIT))
#define HAVE_riscv_clean_di ((TARGET_ZICBOM) && (TARGET_64BIT))
#define HAVE_riscv_flush_si ((TARGET_ZICBOM) && (!TARGET_64BIT))
#define HAVE_riscv_flush_di ((TARGET_ZICBOM) && (TARGET_64BIT))
#define HAVE_riscv_inval_si ((TARGET_ZICBOM) && (!TARGET_64BIT))
#define HAVE_riscv_inval_di ((TARGET_ZICBOM) && (TARGET_64BIT))
#define HAVE_riscv_zero_si ((TARGET_ZICBOZ) && (!TARGET_64BIT))
#define HAVE_riscv_zero_di ((TARGET_ZICBOZ) && (TARGET_64BIT))
#define HAVE_prefetch (TARGET_ZICBOP)
#define HAVE_riscv_prefetchi_si ((TARGET_ZICBOP) && (!TARGET_64BIT))
#define HAVE_riscv_prefetchi_di ((TARGET_ZICBOP) && (TARGET_64BIT))
#define HAVE_rotlsi3 (TARGET_ZBB || TARGET_ZBKB)
#define HAVE_rotldi3 (TARGET_64BIT && (TARGET_ZBB || TARGET_ZBKB))
#define HAVE_rotlsi3_sext (TARGET_64BIT && (TARGET_ZBB || TARGET_ZBKB))
#define HAVE_orcbsi2 ((TARGET_ZBB) && (!TARGET_64BIT))
#define HAVE_orcbdi2 ((TARGET_ZBB) && (TARGET_64BIT))
#define HAVE_sminsi3 ((TARGET_ZBB) && (!TARGET_64BIT))
#define HAVE_uminsi3 ((TARGET_ZBB) && (!TARGET_64BIT))
#define HAVE_smaxsi3 ((TARGET_ZBB) && (!TARGET_64BIT))
#define HAVE_umaxsi3 ((TARGET_ZBB) && (!TARGET_64BIT))
#define HAVE_smindi3 ((TARGET_ZBB) && (TARGET_64BIT))
#define HAVE_umindi3 ((TARGET_ZBB) && (TARGET_64BIT))
#define HAVE_smaxdi3 ((TARGET_ZBB) && (TARGET_64BIT))
#define HAVE_umaxdi3 ((TARGET_ZBB) && (TARGET_64BIT))
#define HAVE_riscv_brev8_si ((TARGET_ZBKB) && (!TARGET_64BIT))
#define HAVE_riscv_brev8_di ((TARGET_ZBKB) && (TARGET_64BIT))
#define HAVE_riscv_zip (TARGET_ZBKB && !TARGET_64BIT)
#define HAVE_riscv_unzip (TARGET_ZBKB && !TARGET_64BIT)
#define HAVE_riscv_pack_sihi ((TARGET_ZBKB) && (!TARGET_64BIT))
#define HAVE_riscv_pack_sisi ((TARGET_ZBKB) && (!TARGET_64BIT))
#define HAVE_riscv_pack_dihi ((TARGET_ZBKB) && (TARGET_64BIT))
#define HAVE_riscv_pack_disi ((TARGET_ZBKB) && (TARGET_64BIT))
#define HAVE_riscv_packh_si ((TARGET_ZBKB) && (!TARGET_64BIT))
#define HAVE_riscv_packh_di ((TARGET_ZBKB) && (TARGET_64BIT))
#define HAVE_riscv_packw (TARGET_ZBKB && TARGET_64BIT)
#define HAVE_riscv_clmul_si ((TARGET_ZBKC) && (!TARGET_64BIT))
#define HAVE_riscv_clmul_di ((TARGET_ZBKC) && (TARGET_64BIT))
#define HAVE_riscv_clmulh_si ((TARGET_ZBKC) && (!TARGET_64BIT))
#define HAVE_riscv_clmulh_di ((TARGET_ZBKC) && (TARGET_64BIT))
#define HAVE_riscv_xperm4_si ((TARGET_ZBKX) && (!TARGET_64BIT))
#define HAVE_riscv_xperm4_di ((TARGET_ZBKX) && (TARGET_64BIT))
#define HAVE_riscv_xperm8_si ((TARGET_ZBKX) && (!TARGET_64BIT))
#define HAVE_riscv_xperm8_di ((TARGET_ZBKX) && (TARGET_64BIT))
#define HAVE_riscv_aes32dsi (TARGET_ZKND && !TARGET_64BIT)
#define HAVE_riscv_aes32dsmi (TARGET_ZKND && !TARGET_64BIT)
#define HAVE_riscv_aes64ds (TARGET_ZKND && TARGET_64BIT)
#define HAVE_riscv_aes64dsm (TARGET_ZKND && TARGET_64BIT)
#define HAVE_riscv_aes64im (TARGET_ZKND && TARGET_64BIT)
#define HAVE_riscv_aes64ks1i ((TARGET_ZKND || TARGET_ZKNE) && TARGET_64BIT)
#define HAVE_riscv_aes64ks2 ((TARGET_ZKND || TARGET_ZKNE) && TARGET_64BIT)
#define HAVE_riscv_aes32esi (TARGET_ZKNE && !TARGET_64BIT)
#define HAVE_riscv_aes32esmi (TARGET_ZKNE && !TARGET_64BIT)
#define HAVE_riscv_aes64es (TARGET_ZKNE && TARGET_64BIT)
#define HAVE_riscv_aes64esm (TARGET_ZKNE && TARGET_64BIT)
#define HAVE_riscv_sha256sig0_si ((TARGET_ZKNH) && (!TARGET_64BIT))
#define HAVE_riscv_sha256sig0_di ((TARGET_ZKNH) && (TARGET_64BIT))
#define HAVE_riscv_sha256sig1_si ((TARGET_ZKNH) && (!TARGET_64BIT))
#define HAVE_riscv_sha256sig1_di ((TARGET_ZKNH) && (TARGET_64BIT))
#define HAVE_riscv_sha256sum0_si ((TARGET_ZKNH) && (!TARGET_64BIT))
#define HAVE_riscv_sha256sum0_di ((TARGET_ZKNH) && (TARGET_64BIT))
#define HAVE_riscv_sha256sum1_si ((TARGET_ZKNH) && (!TARGET_64BIT))
#define HAVE_riscv_sha256sum1_di ((TARGET_ZKNH) && (TARGET_64BIT))
#define HAVE_riscv_sha512sig0h (TARGET_ZKNH && !TARGET_64BIT)
#define HAVE_riscv_sha512sig0l (TARGET_ZKNH && !TARGET_64BIT)
#define HAVE_riscv_sha512sig1h (TARGET_ZKNH && !TARGET_64BIT)
#define HAVE_riscv_sha512sig1l (TARGET_ZKNH && !TARGET_64BIT)
#define HAVE_riscv_sha512sum0r (TARGET_ZKNH && !TARGET_64BIT)
#define HAVE_riscv_sha512sum1r (TARGET_ZKNH && !TARGET_64BIT)
#define HAVE_riscv_sha512sig0 (TARGET_ZKNH && TARGET_64BIT)
#define HAVE_riscv_sha512sig1 (TARGET_ZKNH && TARGET_64BIT)
#define HAVE_riscv_sha512sum0 (TARGET_ZKNH && TARGET_64BIT)
#define HAVE_riscv_sha512sum1 (TARGET_ZKNH && TARGET_64BIT)
#define HAVE_riscv_sm3p0_si ((TARGET_ZKSH) && (!TARGET_64BIT))
#define HAVE_riscv_sm3p0_di ((TARGET_ZKSH) && (TARGET_64BIT))
#define HAVE_riscv_sm3p1_si ((TARGET_ZKSH) && (!TARGET_64BIT))
#define HAVE_riscv_sm3p1_di ((TARGET_ZKSH) && (TARGET_64BIT))
#define HAVE_riscv_sm4ed_si ((TARGET_ZKSED) && (!TARGET_64BIT))
#define HAVE_riscv_sm4ed_di ((TARGET_ZKSED) && (TARGET_64BIT))
#define HAVE_riscv_sm4ks_si ((TARGET_ZKSED) && (!TARGET_64BIT))
#define HAVE_riscv_sm4ks_di ((TARGET_ZKSED) && (TARGET_64BIT))
#define HAVE_mem_thread_fence_1 1
#define HAVE_atomic_storesi (TARGET_ATOMIC)
#define HAVE_atomic_storedi ((TARGET_ATOMIC) && (TARGET_64BIT))
#define HAVE_atomic_addsi (TARGET_ATOMIC)
#define HAVE_atomic_orsi (TARGET_ATOMIC)
#define HAVE_atomic_xorsi (TARGET_ATOMIC)
#define HAVE_atomic_andsi (TARGET_ATOMIC)
#define HAVE_atomic_adddi ((TARGET_ATOMIC) && (TARGET_64BIT))
#define HAVE_atomic_ordi ((TARGET_ATOMIC) && (TARGET_64BIT))
#define HAVE_atomic_xordi ((TARGET_ATOMIC) && (TARGET_64BIT))
#define HAVE_atomic_anddi ((TARGET_ATOMIC) && (TARGET_64BIT))
#define HAVE_atomic_fetch_addsi (TARGET_ATOMIC)
#define HAVE_atomic_fetch_orsi (TARGET_ATOMIC)
#define HAVE_atomic_fetch_xorsi (TARGET_ATOMIC)
#define HAVE_atomic_fetch_andsi (TARGET_ATOMIC)
#define HAVE_atomic_fetch_adddi ((TARGET_ATOMIC) && (TARGET_64BIT))
#define HAVE_atomic_fetch_ordi ((TARGET_ATOMIC) && (TARGET_64BIT))
#define HAVE_atomic_fetch_xordi ((TARGET_ATOMIC) && (TARGET_64BIT))
#define HAVE_atomic_fetch_anddi ((TARGET_ATOMIC) && (TARGET_64BIT))
#define HAVE_atomic_exchangesi (TARGET_ATOMIC)
#define HAVE_atomic_exchangedi ((TARGET_ATOMIC) && (TARGET_64BIT))
#define HAVE_atomic_cas_value_strongsi (TARGET_ATOMIC)
#define HAVE_atomic_cas_value_strongdi ((TARGET_ATOMIC) && (TARGET_64BIT))
#define HAVE_th_fmv_hw_w_x (!TARGET_64BIT && TARGET_XTHEADFMV)
#define HAVE_th_fmv_x_w (!TARGET_64BIT && TARGET_XTHEADFMV)
#define HAVE_th_fmv_x_hw (!TARGET_64BIT && TARGET_XTHEADFMV)
#define HAVE_vundefinedvnx1qi (TARGET_VECTOR)
#define HAVE_vundefinedvnx2qi (TARGET_VECTOR)
#define HAVE_vundefinedvnx4qi (TARGET_VECTOR)
#define HAVE_vundefinedvnx8qi (TARGET_VECTOR)
#define HAVE_vundefinedvnx16qi (TARGET_VECTOR)
#define HAVE_vundefinedvnx32qi (TARGET_VECTOR)
#define HAVE_vundefinedvnx64qi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_vundefinedvnx1hi (TARGET_VECTOR)
#define HAVE_vundefinedvnx2hi (TARGET_VECTOR)
#define HAVE_vundefinedvnx4hi (TARGET_VECTOR)
#define HAVE_vundefinedvnx8hi (TARGET_VECTOR)
#define HAVE_vundefinedvnx16hi (TARGET_VECTOR)
#define HAVE_vundefinedvnx32hi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_vundefinedvnx1si (TARGET_VECTOR)
#define HAVE_vundefinedvnx2si (TARGET_VECTOR)
#define HAVE_vundefinedvnx4si (TARGET_VECTOR)
#define HAVE_vundefinedvnx8si (TARGET_VECTOR)
#define HAVE_vundefinedvnx16si ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_vundefinedvnx1di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_vundefinedvnx2di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_vundefinedvnx4di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_vundefinedvnx8di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_vundefinedvnx1sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_vundefinedvnx2sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_vundefinedvnx4sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_vundefinedvnx8sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_vundefinedvnx16sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32 && TARGET_MIN_VLEN > 32))
#define HAVE_vundefinedvnx1df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_vundefinedvnx2df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_vundefinedvnx4df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_vundefinedvnx8df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_vundefinedvnx1bi (TARGET_VECTOR)
#define HAVE_vundefinedvnx2bi (TARGET_VECTOR)
#define HAVE_vundefinedvnx4bi (TARGET_VECTOR)
#define HAVE_vundefinedvnx8bi (TARGET_VECTOR)
#define HAVE_vundefinedvnx16bi (TARGET_VECTOR)
#define HAVE_vundefinedvnx32bi (TARGET_VECTOR)
#define HAVE_vundefinedvnx64bi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_vlmax_avlsi ((TARGET_VECTOR) && (Pmode == SImode))
#define HAVE_vlmax_avldi ((TARGET_VECTOR) && (Pmode == DImode))
#define HAVE_vsetvlsi ((TARGET_VECTOR) && (Pmode == SImode))
#define HAVE_vsetvldi ((TARGET_VECTOR) && (Pmode == DImode))
#define HAVE_vsetvl_vtype_change_only (TARGET_VECTOR)
#define HAVE_vsetvl_discard_resultsi ((TARGET_VECTOR) && (Pmode == SImode))
#define HAVE_vsetvl_discard_resultdi ((TARGET_VECTOR) && (Pmode == DImode))
#define HAVE_vsetvlsi_no_side_effects ((TARGET_VECTOR) && (Pmode == SImode))
#define HAVE_vsetvldi_no_side_effects ((TARGET_VECTOR) && (Pmode == DImode))
#define HAVE_pred_movvnx1qi (TARGET_VECTOR && (MEM_P (operands[0]) || MEM_P (operands[3]) \
   || CONST_VECTOR_P (operands[1])))
#define HAVE_pred_movvnx2qi (TARGET_VECTOR && (MEM_P (operands[0]) || MEM_P (operands[3]) \
   || CONST_VECTOR_P (operands[1])))
#define HAVE_pred_movvnx4qi (TARGET_VECTOR && (MEM_P (operands[0]) || MEM_P (operands[3]) \
   || CONST_VECTOR_P (operands[1])))
#define HAVE_pred_movvnx8qi (TARGET_VECTOR && (MEM_P (operands[0]) || MEM_P (operands[3]) \
   || CONST_VECTOR_P (operands[1])))
#define HAVE_pred_movvnx16qi (TARGET_VECTOR && (MEM_P (operands[0]) || MEM_P (operands[3]) \
   || CONST_VECTOR_P (operands[1])))
#define HAVE_pred_movvnx32qi (TARGET_VECTOR && (MEM_P (operands[0]) || MEM_P (operands[3]) \
   || CONST_VECTOR_P (operands[1])))
#define HAVE_pred_movvnx64qi ((TARGET_VECTOR && (MEM_P (operands[0]) || MEM_P (operands[3]) \
   || CONST_VECTOR_P (operands[1]))) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_movvnx1hi (TARGET_VECTOR && (MEM_P (operands[0]) || MEM_P (operands[3]) \
   || CONST_VECTOR_P (operands[1])))
#define HAVE_pred_movvnx2hi (TARGET_VECTOR && (MEM_P (operands[0]) || MEM_P (operands[3]) \
   || CONST_VECTOR_P (operands[1])))
#define HAVE_pred_movvnx4hi (TARGET_VECTOR && (MEM_P (operands[0]) || MEM_P (operands[3]) \
   || CONST_VECTOR_P (operands[1])))
#define HAVE_pred_movvnx8hi (TARGET_VECTOR && (MEM_P (operands[0]) || MEM_P (operands[3]) \
   || CONST_VECTOR_P (operands[1])))
#define HAVE_pred_movvnx16hi (TARGET_VECTOR && (MEM_P (operands[0]) || MEM_P (operands[3]) \
   || CONST_VECTOR_P (operands[1])))
#define HAVE_pred_movvnx32hi ((TARGET_VECTOR && (MEM_P (operands[0]) || MEM_P (operands[3]) \
   || CONST_VECTOR_P (operands[1]))) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_movvnx1si (TARGET_VECTOR && (MEM_P (operands[0]) || MEM_P (operands[3]) \
   || CONST_VECTOR_P (operands[1])))
#define HAVE_pred_movvnx2si (TARGET_VECTOR && (MEM_P (operands[0]) || MEM_P (operands[3]) \
   || CONST_VECTOR_P (operands[1])))
#define HAVE_pred_movvnx4si (TARGET_VECTOR && (MEM_P (operands[0]) || MEM_P (operands[3]) \
   || CONST_VECTOR_P (operands[1])))
#define HAVE_pred_movvnx8si (TARGET_VECTOR && (MEM_P (operands[0]) || MEM_P (operands[3]) \
   || CONST_VECTOR_P (operands[1])))
#define HAVE_pred_movvnx16si ((TARGET_VECTOR && (MEM_P (operands[0]) || MEM_P (operands[3]) \
   || CONST_VECTOR_P (operands[1]))) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_movvnx1di ((TARGET_VECTOR && (MEM_P (operands[0]) || MEM_P (operands[3]) \
   || CONST_VECTOR_P (operands[1]))) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_movvnx2di ((TARGET_VECTOR && (MEM_P (operands[0]) || MEM_P (operands[3]) \
   || CONST_VECTOR_P (operands[1]))) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_movvnx4di ((TARGET_VECTOR && (MEM_P (operands[0]) || MEM_P (operands[3]) \
   || CONST_VECTOR_P (operands[1]))) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_movvnx8di ((TARGET_VECTOR && (MEM_P (operands[0]) || MEM_P (operands[3]) \
   || CONST_VECTOR_P (operands[1]))) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_movvnx1sf ((TARGET_VECTOR && (MEM_P (operands[0]) || MEM_P (operands[3]) \
   || CONST_VECTOR_P (operands[1]))) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_movvnx2sf ((TARGET_VECTOR && (MEM_P (operands[0]) || MEM_P (operands[3]) \
   || CONST_VECTOR_P (operands[1]))) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_movvnx4sf ((TARGET_VECTOR && (MEM_P (operands[0]) || MEM_P (operands[3]) \
   || CONST_VECTOR_P (operands[1]))) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_movvnx8sf ((TARGET_VECTOR && (MEM_P (operands[0]) || MEM_P (operands[3]) \
   || CONST_VECTOR_P (operands[1]))) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_movvnx16sf ((TARGET_VECTOR && (MEM_P (operands[0]) || MEM_P (operands[3]) \
   || CONST_VECTOR_P (operands[1]))) && (TARGET_VECTOR_ELEN_FP_32 && TARGET_MIN_VLEN > 32))
#define HAVE_pred_movvnx1df ((TARGET_VECTOR && (MEM_P (operands[0]) || MEM_P (operands[3]) \
   || CONST_VECTOR_P (operands[1]))) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_movvnx2df ((TARGET_VECTOR && (MEM_P (operands[0]) || MEM_P (operands[3]) \
   || CONST_VECTOR_P (operands[1]))) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_movvnx4df ((TARGET_VECTOR && (MEM_P (operands[0]) || MEM_P (operands[3]) \
   || CONST_VECTOR_P (operands[1]))) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_movvnx8df ((TARGET_VECTOR && (MEM_P (operands[0]) || MEM_P (operands[3]) \
   || CONST_VECTOR_P (operands[1]))) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_storevnx1qi (TARGET_VECTOR)
#define HAVE_pred_storevnx2qi (TARGET_VECTOR)
#define HAVE_pred_storevnx4qi (TARGET_VECTOR)
#define HAVE_pred_storevnx8qi (TARGET_VECTOR)
#define HAVE_pred_storevnx16qi (TARGET_VECTOR)
#define HAVE_pred_storevnx32qi (TARGET_VECTOR)
#define HAVE_pred_storevnx64qi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_storevnx1hi (TARGET_VECTOR)
#define HAVE_pred_storevnx2hi (TARGET_VECTOR)
#define HAVE_pred_storevnx4hi (TARGET_VECTOR)
#define HAVE_pred_storevnx8hi (TARGET_VECTOR)
#define HAVE_pred_storevnx16hi (TARGET_VECTOR)
#define HAVE_pred_storevnx32hi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_storevnx1si (TARGET_VECTOR)
#define HAVE_pred_storevnx2si (TARGET_VECTOR)
#define HAVE_pred_storevnx4si (TARGET_VECTOR)
#define HAVE_pred_storevnx8si (TARGET_VECTOR)
#define HAVE_pred_storevnx16si ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_storevnx1di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_storevnx2di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_storevnx4di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_storevnx8di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_storevnx1sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_storevnx2sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_storevnx4sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_storevnx8sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_storevnx16sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32 && TARGET_MIN_VLEN > 32))
#define HAVE_pred_storevnx1df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_storevnx2df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_storevnx4df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_storevnx8df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_movvnx1bi (TARGET_VECTOR)
#define HAVE_pred_movvnx2bi (TARGET_VECTOR)
#define HAVE_pred_movvnx4bi (TARGET_VECTOR)
#define HAVE_pred_movvnx8bi (TARGET_VECTOR)
#define HAVE_pred_movvnx16bi (TARGET_VECTOR)
#define HAVE_pred_movvnx32bi (TARGET_VECTOR)
#define HAVE_pred_movvnx64bi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_storevnx1bi (TARGET_VECTOR)
#define HAVE_pred_storevnx2bi (TARGET_VECTOR)
#define HAVE_pred_storevnx4bi (TARGET_VECTOR)
#define HAVE_pred_storevnx8bi (TARGET_VECTOR)
#define HAVE_pred_storevnx16bi (TARGET_VECTOR)
#define HAVE_pred_storevnx32bi (TARGET_VECTOR)
#define HAVE_pred_storevnx64bi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_mergevnx1qi (TARGET_VECTOR)
#define HAVE_pred_mergevnx2qi (TARGET_VECTOR)
#define HAVE_pred_mergevnx4qi (TARGET_VECTOR)
#define HAVE_pred_mergevnx8qi (TARGET_VECTOR)
#define HAVE_pred_mergevnx16qi (TARGET_VECTOR)
#define HAVE_pred_mergevnx32qi (TARGET_VECTOR)
#define HAVE_pred_mergevnx64qi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_mergevnx1hi (TARGET_VECTOR)
#define HAVE_pred_mergevnx2hi (TARGET_VECTOR)
#define HAVE_pred_mergevnx4hi (TARGET_VECTOR)
#define HAVE_pred_mergevnx8hi (TARGET_VECTOR)
#define HAVE_pred_mergevnx16hi (TARGET_VECTOR)
#define HAVE_pred_mergevnx32hi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_mergevnx1si (TARGET_VECTOR)
#define HAVE_pred_mergevnx2si (TARGET_VECTOR)
#define HAVE_pred_mergevnx4si (TARGET_VECTOR)
#define HAVE_pred_mergevnx8si (TARGET_VECTOR)
#define HAVE_pred_mergevnx16si ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_mergevnx1di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_mergevnx2di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_mergevnx4di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_mergevnx8di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_mergevnx1sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_mergevnx2sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_mergevnx4sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_mergevnx8sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_mergevnx16sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32 && TARGET_MIN_VLEN > 32))
#define HAVE_pred_mergevnx1df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_mergevnx2df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_mergevnx4df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_mergevnx8df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_mergevnx1qi_scalar (TARGET_VECTOR)
#define HAVE_pred_mergevnx2qi_scalar (TARGET_VECTOR)
#define HAVE_pred_mergevnx4qi_scalar (TARGET_VECTOR)
#define HAVE_pred_mergevnx8qi_scalar (TARGET_VECTOR)
#define HAVE_pred_mergevnx16qi_scalar (TARGET_VECTOR)
#define HAVE_pred_mergevnx32qi_scalar (TARGET_VECTOR)
#define HAVE_pred_mergevnx64qi_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_mergevnx1hi_scalar (TARGET_VECTOR)
#define HAVE_pred_mergevnx2hi_scalar (TARGET_VECTOR)
#define HAVE_pred_mergevnx4hi_scalar (TARGET_VECTOR)
#define HAVE_pred_mergevnx8hi_scalar (TARGET_VECTOR)
#define HAVE_pred_mergevnx16hi_scalar (TARGET_VECTOR)
#define HAVE_pred_mergevnx32hi_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_mergevnx1si_scalar (TARGET_VECTOR)
#define HAVE_pred_mergevnx2si_scalar (TARGET_VECTOR)
#define HAVE_pred_mergevnx4si_scalar (TARGET_VECTOR)
#define HAVE_pred_mergevnx8si_scalar (TARGET_VECTOR)
#define HAVE_pred_mergevnx16si_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_strided_loadvnx1qi (TARGET_VECTOR)
#define HAVE_pred_strided_loadvnx2qi (TARGET_VECTOR)
#define HAVE_pred_strided_loadvnx4qi (TARGET_VECTOR)
#define HAVE_pred_strided_loadvnx8qi (TARGET_VECTOR)
#define HAVE_pred_strided_loadvnx16qi (TARGET_VECTOR)
#define HAVE_pred_strided_loadvnx32qi (TARGET_VECTOR)
#define HAVE_pred_strided_loadvnx64qi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_strided_loadvnx1hi (TARGET_VECTOR)
#define HAVE_pred_strided_loadvnx2hi (TARGET_VECTOR)
#define HAVE_pred_strided_loadvnx4hi (TARGET_VECTOR)
#define HAVE_pred_strided_loadvnx8hi (TARGET_VECTOR)
#define HAVE_pred_strided_loadvnx16hi (TARGET_VECTOR)
#define HAVE_pred_strided_loadvnx32hi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_strided_loadvnx1si (TARGET_VECTOR)
#define HAVE_pred_strided_loadvnx2si (TARGET_VECTOR)
#define HAVE_pred_strided_loadvnx4si (TARGET_VECTOR)
#define HAVE_pred_strided_loadvnx8si (TARGET_VECTOR)
#define HAVE_pred_strided_loadvnx16si ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_strided_loadvnx1di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_strided_loadvnx2di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_strided_loadvnx4di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_strided_loadvnx8di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_strided_loadvnx1sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_strided_loadvnx2sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_strided_loadvnx4sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_strided_loadvnx8sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_strided_loadvnx16sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32 && TARGET_MIN_VLEN > 32))
#define HAVE_pred_strided_loadvnx1df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_strided_loadvnx2df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_strided_loadvnx4df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_strided_loadvnx8df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_strided_storevnx1qi (TARGET_VECTOR)
#define HAVE_pred_strided_storevnx2qi (TARGET_VECTOR)
#define HAVE_pred_strided_storevnx4qi (TARGET_VECTOR)
#define HAVE_pred_strided_storevnx8qi (TARGET_VECTOR)
#define HAVE_pred_strided_storevnx16qi (TARGET_VECTOR)
#define HAVE_pred_strided_storevnx32qi (TARGET_VECTOR)
#define HAVE_pred_strided_storevnx64qi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_strided_storevnx1hi (TARGET_VECTOR)
#define HAVE_pred_strided_storevnx2hi (TARGET_VECTOR)
#define HAVE_pred_strided_storevnx4hi (TARGET_VECTOR)
#define HAVE_pred_strided_storevnx8hi (TARGET_VECTOR)
#define HAVE_pred_strided_storevnx16hi (TARGET_VECTOR)
#define HAVE_pred_strided_storevnx32hi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_strided_storevnx1si (TARGET_VECTOR)
#define HAVE_pred_strided_storevnx2si (TARGET_VECTOR)
#define HAVE_pred_strided_storevnx4si (TARGET_VECTOR)
#define HAVE_pred_strided_storevnx8si (TARGET_VECTOR)
#define HAVE_pred_strided_storevnx16si ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_strided_storevnx1di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_strided_storevnx2di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_strided_storevnx4di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_strided_storevnx8di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_strided_storevnx1sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_strided_storevnx2sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_strided_storevnx4sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_strided_storevnx8sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_strided_storevnx16sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32 && TARGET_MIN_VLEN > 32))
#define HAVE_pred_strided_storevnx1df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_strided_storevnx2df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_strided_storevnx4df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_strided_storevnx8df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_indexed_oloadvnx1qi_same_eew (TARGET_VECTOR)
#define HAVE_pred_indexed_uloadvnx1qi_same_eew (TARGET_VECTOR)
#define HAVE_pred_indexed_oloadvnx2qi_same_eew (TARGET_VECTOR)
#define HAVE_pred_indexed_uloadvnx2qi_same_eew (TARGET_VECTOR)
#define HAVE_pred_indexed_oloadvnx4qi_same_eew (TARGET_VECTOR)
#define HAVE_pred_indexed_uloadvnx4qi_same_eew (TARGET_VECTOR)
#define HAVE_pred_indexed_oloadvnx8qi_same_eew (TARGET_VECTOR)
#define HAVE_pred_indexed_uloadvnx8qi_same_eew (TARGET_VECTOR)
#define HAVE_pred_indexed_oloadvnx16qi_same_eew (TARGET_VECTOR)
#define HAVE_pred_indexed_uloadvnx16qi_same_eew (TARGET_VECTOR)
#define HAVE_pred_indexed_oloadvnx32qi_same_eew (TARGET_VECTOR)
#define HAVE_pred_indexed_uloadvnx32qi_same_eew (TARGET_VECTOR)
#define HAVE_pred_indexed_oloadvnx64qi_same_eew ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_indexed_uloadvnx64qi_same_eew ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_indexed_oloadvnx1hi_same_eew (TARGET_VECTOR)
#define HAVE_pred_indexed_uloadvnx1hi_same_eew (TARGET_VECTOR)
#define HAVE_pred_indexed_oloadvnx2hi_same_eew (TARGET_VECTOR)
#define HAVE_pred_indexed_uloadvnx2hi_same_eew (TARGET_VECTOR)
#define HAVE_pred_indexed_oloadvnx4hi_same_eew (TARGET_VECTOR)
#define HAVE_pred_indexed_uloadvnx4hi_same_eew (TARGET_VECTOR)
#define HAVE_pred_indexed_oloadvnx8hi_same_eew (TARGET_VECTOR)
#define HAVE_pred_indexed_uloadvnx8hi_same_eew (TARGET_VECTOR)
#define HAVE_pred_indexed_oloadvnx16hi_same_eew (TARGET_VECTOR)
#define HAVE_pred_indexed_uloadvnx16hi_same_eew (TARGET_VECTOR)
#define HAVE_pred_indexed_oloadvnx32hi_same_eew ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_indexed_uloadvnx32hi_same_eew ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_indexed_oloadvnx1si_same_eew (TARGET_VECTOR)
#define HAVE_pred_indexed_uloadvnx1si_same_eew (TARGET_VECTOR)
#define HAVE_pred_indexed_oloadvnx2si_same_eew (TARGET_VECTOR)
#define HAVE_pred_indexed_uloadvnx2si_same_eew (TARGET_VECTOR)
#define HAVE_pred_indexed_oloadvnx4si_same_eew (TARGET_VECTOR)
#define HAVE_pred_indexed_uloadvnx4si_same_eew (TARGET_VECTOR)
#define HAVE_pred_indexed_oloadvnx8si_same_eew (TARGET_VECTOR)
#define HAVE_pred_indexed_uloadvnx8si_same_eew (TARGET_VECTOR)
#define HAVE_pred_indexed_oloadvnx16si_same_eew ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_indexed_uloadvnx16si_same_eew ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_indexed_oloadvnx1di_same_eew ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_indexed_uloadvnx1di_same_eew ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_indexed_oloadvnx2di_same_eew ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_indexed_uloadvnx2di_same_eew ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_indexed_oloadvnx4di_same_eew ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_indexed_uloadvnx4di_same_eew ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_indexed_oloadvnx8di_same_eew ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_indexed_uloadvnx8di_same_eew ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_indexed_oloadvnx1sf_same_eew ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_indexed_uloadvnx1sf_same_eew ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_indexed_oloadvnx2sf_same_eew ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_indexed_uloadvnx2sf_same_eew ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_indexed_oloadvnx4sf_same_eew ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_indexed_uloadvnx4sf_same_eew ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_indexed_oloadvnx8sf_same_eew ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_indexed_uloadvnx8sf_same_eew ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_indexed_oloadvnx16sf_same_eew ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32 && TARGET_MIN_VLEN > 32))
#define HAVE_pred_indexed_uloadvnx16sf_same_eew ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32 && TARGET_MIN_VLEN > 32))
#define HAVE_pred_indexed_oloadvnx1df_same_eew ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_indexed_uloadvnx1df_same_eew ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_indexed_oloadvnx2df_same_eew ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_indexed_uloadvnx2df_same_eew ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_indexed_oloadvnx4df_same_eew ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_indexed_uloadvnx4df_same_eew ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_indexed_oloadvnx8df_same_eew ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_indexed_uloadvnx8df_same_eew ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_indexed_oloadvnx1hi_x2_greater_eew (TARGET_VECTOR)
#define HAVE_pred_indexed_uloadvnx1hi_x2_greater_eew (TARGET_VECTOR)
#define HAVE_pred_indexed_oloadvnx2hi_x2_greater_eew (TARGET_VECTOR)
#define HAVE_pred_indexed_uloadvnx2hi_x2_greater_eew (TARGET_VECTOR)
#define HAVE_pred_indexed_oloadvnx4hi_x2_greater_eew (TARGET_VECTOR)
#define HAVE_pred_indexed_uloadvnx4hi_x2_greater_eew (TARGET_VECTOR)
#define HAVE_pred_indexed_oloadvnx8hi_x2_greater_eew (TARGET_VECTOR)
#define HAVE_pred_indexed_uloadvnx8hi_x2_greater_eew (TARGET_VECTOR)
#define HAVE_pred_indexed_oloadvnx16hi_x2_greater_eew (TARGET_VECTOR)
#define HAVE_pred_indexed_uloadvnx16hi_x2_greater_eew (TARGET_VECTOR)
#define HAVE_pred_indexed_oloadvnx32hi_x2_greater_eew ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_indexed_uloadvnx32hi_x2_greater_eew ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_indexed_oloadvnx1si_x2_greater_eew (TARGET_VECTOR)
#define HAVE_pred_indexed_uloadvnx1si_x2_greater_eew (TARGET_VECTOR)
#define HAVE_pred_indexed_oloadvnx2si_x2_greater_eew (TARGET_VECTOR)
#define HAVE_pred_indexed_uloadvnx2si_x2_greater_eew (TARGET_VECTOR)
#define HAVE_pred_indexed_oloadvnx4si_x2_greater_eew (TARGET_VECTOR)
#define HAVE_pred_indexed_uloadvnx4si_x2_greater_eew (TARGET_VECTOR)
#define HAVE_pred_indexed_oloadvnx8si_x2_greater_eew (TARGET_VECTOR)
#define HAVE_pred_indexed_uloadvnx8si_x2_greater_eew (TARGET_VECTOR)
#define HAVE_pred_indexed_oloadvnx16si_x2_greater_eew ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_indexed_uloadvnx16si_x2_greater_eew ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_indexed_oloadvnx1di_x2_greater_eew ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_indexed_uloadvnx1di_x2_greater_eew ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_indexed_oloadvnx2di_x2_greater_eew ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_indexed_uloadvnx2di_x2_greater_eew ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_indexed_oloadvnx4di_x2_greater_eew ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_indexed_uloadvnx4di_x2_greater_eew ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_indexed_oloadvnx8di_x2_greater_eew ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_indexed_uloadvnx8di_x2_greater_eew ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_indexed_oloadvnx1sf_x2_greater_eew ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_indexed_uloadvnx1sf_x2_greater_eew ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_indexed_oloadvnx2sf_x2_greater_eew ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_indexed_uloadvnx2sf_x2_greater_eew ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_indexed_oloadvnx4sf_x2_greater_eew ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_indexed_uloadvnx4sf_x2_greater_eew ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_indexed_oloadvnx8sf_x2_greater_eew ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_indexed_uloadvnx8sf_x2_greater_eew ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_indexed_oloadvnx16sf_x2_greater_eew ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32 && TARGET_MIN_VLEN > 32))
#define HAVE_pred_indexed_uloadvnx16sf_x2_greater_eew ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32 && TARGET_MIN_VLEN > 32))
#define HAVE_pred_indexed_oloadvnx1df_x2_greater_eew ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_indexed_uloadvnx1df_x2_greater_eew ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_indexed_oloadvnx2df_x2_greater_eew ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_indexed_uloadvnx2df_x2_greater_eew ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_indexed_oloadvnx4df_x2_greater_eew ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_indexed_uloadvnx4df_x2_greater_eew ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_indexed_oloadvnx8df_x2_greater_eew ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_indexed_uloadvnx8df_x2_greater_eew ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_indexed_oloadvnx1si_x4_greater_eew (TARGET_VECTOR)
#define HAVE_pred_indexed_uloadvnx1si_x4_greater_eew (TARGET_VECTOR)
#define HAVE_pred_indexed_oloadvnx2si_x4_greater_eew (TARGET_VECTOR)
#define HAVE_pred_indexed_uloadvnx2si_x4_greater_eew (TARGET_VECTOR)
#define HAVE_pred_indexed_oloadvnx4si_x4_greater_eew (TARGET_VECTOR)
#define HAVE_pred_indexed_uloadvnx4si_x4_greater_eew (TARGET_VECTOR)
#define HAVE_pred_indexed_oloadvnx8si_x4_greater_eew (TARGET_VECTOR)
#define HAVE_pred_indexed_uloadvnx8si_x4_greater_eew (TARGET_VECTOR)
#define HAVE_pred_indexed_oloadvnx16si_x4_greater_eew ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_indexed_uloadvnx16si_x4_greater_eew ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_indexed_oloadvnx1di_x4_greater_eew ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_indexed_uloadvnx1di_x4_greater_eew ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_indexed_oloadvnx2di_x4_greater_eew ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_indexed_uloadvnx2di_x4_greater_eew ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_indexed_oloadvnx4di_x4_greater_eew ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_indexed_uloadvnx4di_x4_greater_eew ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_indexed_oloadvnx8di_x4_greater_eew ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_indexed_uloadvnx8di_x4_greater_eew ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_indexed_oloadvnx1sf_x4_greater_eew ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_indexed_uloadvnx1sf_x4_greater_eew ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_indexed_oloadvnx2sf_x4_greater_eew ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_indexed_uloadvnx2sf_x4_greater_eew ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_indexed_oloadvnx4sf_x4_greater_eew ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_indexed_uloadvnx4sf_x4_greater_eew ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_indexed_oloadvnx8sf_x4_greater_eew ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_indexed_uloadvnx8sf_x4_greater_eew ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_indexed_oloadvnx16sf_x4_greater_eew ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32 && TARGET_MIN_VLEN > 32))
#define HAVE_pred_indexed_uloadvnx16sf_x4_greater_eew ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32 && TARGET_MIN_VLEN > 32))
#define HAVE_pred_indexed_oloadvnx1df_x4_greater_eew ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_indexed_uloadvnx1df_x4_greater_eew ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_indexed_oloadvnx2df_x4_greater_eew ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_indexed_uloadvnx2df_x4_greater_eew ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_indexed_oloadvnx4df_x4_greater_eew ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_indexed_uloadvnx4df_x4_greater_eew ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_indexed_oloadvnx8df_x4_greater_eew ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_indexed_uloadvnx8df_x4_greater_eew ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_indexed_oloadvnx1di_x8_greater_eew ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_indexed_uloadvnx1di_x8_greater_eew ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_indexed_oloadvnx2di_x8_greater_eew ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_indexed_uloadvnx2di_x8_greater_eew ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_indexed_oloadvnx4di_x8_greater_eew ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_indexed_uloadvnx4di_x8_greater_eew ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_indexed_oloadvnx8di_x8_greater_eew ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_indexed_uloadvnx8di_x8_greater_eew ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_indexed_oloadvnx1df_x8_greater_eew ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_indexed_uloadvnx1df_x8_greater_eew ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_indexed_oloadvnx2df_x8_greater_eew ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_indexed_uloadvnx2df_x8_greater_eew ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_indexed_oloadvnx4df_x8_greater_eew ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_indexed_uloadvnx4df_x8_greater_eew ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_indexed_oloadvnx8df_x8_greater_eew ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_indexed_uloadvnx8df_x8_greater_eew ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_indexed_oloadvnx1qi_x2_smaller_eew (TARGET_VECTOR)
#define HAVE_pred_indexed_uloadvnx1qi_x2_smaller_eew (TARGET_VECTOR)
#define HAVE_pred_indexed_oloadvnx2qi_x2_smaller_eew (TARGET_VECTOR)
#define HAVE_pred_indexed_uloadvnx2qi_x2_smaller_eew (TARGET_VECTOR)
#define HAVE_pred_indexed_oloadvnx4qi_x2_smaller_eew (TARGET_VECTOR)
#define HAVE_pred_indexed_uloadvnx4qi_x2_smaller_eew (TARGET_VECTOR)
#define HAVE_pred_indexed_oloadvnx8qi_x2_smaller_eew (TARGET_VECTOR)
#define HAVE_pred_indexed_uloadvnx8qi_x2_smaller_eew (TARGET_VECTOR)
#define HAVE_pred_indexed_oloadvnx16qi_x2_smaller_eew (TARGET_VECTOR)
#define HAVE_pred_indexed_uloadvnx16qi_x2_smaller_eew (TARGET_VECTOR)
#define HAVE_pred_indexed_oloadvnx32qi_x2_smaller_eew (TARGET_VECTOR)
#define HAVE_pred_indexed_uloadvnx32qi_x2_smaller_eew (TARGET_VECTOR)
#define HAVE_pred_indexed_oloadvnx1hi_x2_smaller_eew (TARGET_VECTOR)
#define HAVE_pred_indexed_uloadvnx1hi_x2_smaller_eew (TARGET_VECTOR)
#define HAVE_pred_indexed_oloadvnx2hi_x2_smaller_eew (TARGET_VECTOR)
#define HAVE_pred_indexed_uloadvnx2hi_x2_smaller_eew (TARGET_VECTOR)
#define HAVE_pred_indexed_oloadvnx4hi_x2_smaller_eew (TARGET_VECTOR)
#define HAVE_pred_indexed_uloadvnx4hi_x2_smaller_eew (TARGET_VECTOR)
#define HAVE_pred_indexed_oloadvnx8hi_x2_smaller_eew (TARGET_VECTOR)
#define HAVE_pred_indexed_uloadvnx8hi_x2_smaller_eew (TARGET_VECTOR)
#define HAVE_pred_indexed_oloadvnx16hi_x2_smaller_eew (TARGET_VECTOR)
#define HAVE_pred_indexed_uloadvnx16hi_x2_smaller_eew (TARGET_VECTOR)
#define HAVE_pred_indexed_oloadvnx1si_x2_smaller_eew (TARGET_VECTOR)
#define HAVE_pred_indexed_uloadvnx1si_x2_smaller_eew (TARGET_VECTOR)
#define HAVE_pred_indexed_oloadvnx2si_x2_smaller_eew (TARGET_VECTOR)
#define HAVE_pred_indexed_uloadvnx2si_x2_smaller_eew (TARGET_VECTOR)
#define HAVE_pred_indexed_oloadvnx4si_x2_smaller_eew (TARGET_VECTOR)
#define HAVE_pred_indexed_uloadvnx4si_x2_smaller_eew (TARGET_VECTOR)
#define HAVE_pred_indexed_oloadvnx8si_x2_smaller_eew (TARGET_VECTOR)
#define HAVE_pred_indexed_uloadvnx8si_x2_smaller_eew (TARGET_VECTOR)
#define HAVE_pred_indexed_oloadvnx1sf_x2_smaller_eew ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_indexed_uloadvnx1sf_x2_smaller_eew ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_indexed_oloadvnx2sf_x2_smaller_eew ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_indexed_uloadvnx2sf_x2_smaller_eew ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_indexed_oloadvnx4sf_x2_smaller_eew ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_indexed_uloadvnx4sf_x2_smaller_eew ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_indexed_oloadvnx8sf_x2_smaller_eew ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_indexed_uloadvnx8sf_x2_smaller_eew ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_indexed_oloadvnx1qi_x4_smaller_eew (TARGET_VECTOR)
#define HAVE_pred_indexed_uloadvnx1qi_x4_smaller_eew (TARGET_VECTOR)
#define HAVE_pred_indexed_oloadvnx2qi_x4_smaller_eew (TARGET_VECTOR)
#define HAVE_pred_indexed_uloadvnx2qi_x4_smaller_eew (TARGET_VECTOR)
#define HAVE_pred_indexed_oloadvnx4qi_x4_smaller_eew (TARGET_VECTOR)
#define HAVE_pred_indexed_uloadvnx4qi_x4_smaller_eew (TARGET_VECTOR)
#define HAVE_pred_indexed_oloadvnx8qi_x4_smaller_eew (TARGET_VECTOR)
#define HAVE_pred_indexed_uloadvnx8qi_x4_smaller_eew (TARGET_VECTOR)
#define HAVE_pred_indexed_oloadvnx16qi_x4_smaller_eew (TARGET_VECTOR)
#define HAVE_pred_indexed_uloadvnx16qi_x4_smaller_eew (TARGET_VECTOR)
#define HAVE_pred_indexed_oloadvnx1hi_x4_smaller_eew (TARGET_VECTOR)
#define HAVE_pred_indexed_uloadvnx1hi_x4_smaller_eew (TARGET_VECTOR)
#define HAVE_pred_indexed_oloadvnx2hi_x4_smaller_eew (TARGET_VECTOR)
#define HAVE_pred_indexed_uloadvnx2hi_x4_smaller_eew (TARGET_VECTOR)
#define HAVE_pred_indexed_oloadvnx4hi_x4_smaller_eew (TARGET_VECTOR)
#define HAVE_pred_indexed_uloadvnx4hi_x4_smaller_eew (TARGET_VECTOR)
#define HAVE_pred_indexed_oloadvnx8hi_x4_smaller_eew (TARGET_VECTOR)
#define HAVE_pred_indexed_uloadvnx8hi_x4_smaller_eew (TARGET_VECTOR)
#define HAVE_pred_indexed_oloadvnx1qi_x8_smaller_eew (TARGET_VECTOR)
#define HAVE_pred_indexed_uloadvnx1qi_x8_smaller_eew (TARGET_VECTOR)
#define HAVE_pred_indexed_oloadvnx2qi_x8_smaller_eew (TARGET_VECTOR)
#define HAVE_pred_indexed_uloadvnx2qi_x8_smaller_eew (TARGET_VECTOR)
#define HAVE_pred_indexed_oloadvnx4qi_x8_smaller_eew (TARGET_VECTOR)
#define HAVE_pred_indexed_uloadvnx4qi_x8_smaller_eew (TARGET_VECTOR)
#define HAVE_pred_indexed_oloadvnx8qi_x8_smaller_eew (TARGET_VECTOR)
#define HAVE_pred_indexed_uloadvnx8qi_x8_smaller_eew (TARGET_VECTOR)
#define HAVE_pred_indexed_ostorevnx1qivnx1qi (TARGET_VECTOR)
#define HAVE_pred_indexed_ustorevnx1qivnx1qi (TARGET_VECTOR)
#define HAVE_pred_indexed_ostorevnx1qivnx1hi (TARGET_VECTOR)
#define HAVE_pred_indexed_ustorevnx1qivnx1hi (TARGET_VECTOR)
#define HAVE_pred_indexed_ostorevnx1qivnx1si (TARGET_VECTOR)
#define HAVE_pred_indexed_ustorevnx1qivnx1si (TARGET_VECTOR)
#define HAVE_pred_indexed_ostorevnx1qivnx1di ((TARGET_VECTOR) && (TARGET_64BIT && TARGET_MIN_VLEN > 32))
#define HAVE_pred_indexed_ustorevnx1qivnx1di ((TARGET_VECTOR) && (TARGET_64BIT && TARGET_MIN_VLEN > 32))
#define HAVE_pred_indexed_ostorevnx1hivnx1qi (TARGET_VECTOR)
#define HAVE_pred_indexed_ustorevnx1hivnx1qi (TARGET_VECTOR)
#define HAVE_pred_indexed_ostorevnx1hivnx1hi (TARGET_VECTOR)
#define HAVE_pred_indexed_ustorevnx1hivnx1hi (TARGET_VECTOR)
#define HAVE_pred_indexed_ostorevnx1hivnx1si (TARGET_VECTOR)
#define HAVE_pred_indexed_ustorevnx1hivnx1si (TARGET_VECTOR)
#define HAVE_pred_indexed_ostorevnx1hivnx1di ((TARGET_VECTOR) && (TARGET_64BIT && TARGET_MIN_VLEN > 32))
#define HAVE_pred_indexed_ustorevnx1hivnx1di ((TARGET_VECTOR) && (TARGET_64BIT && TARGET_MIN_VLEN > 32))
#define HAVE_pred_indexed_ostorevnx1sivnx1qi (TARGET_VECTOR)
#define HAVE_pred_indexed_ustorevnx1sivnx1qi (TARGET_VECTOR)
#define HAVE_pred_indexed_ostorevnx1sivnx1hi (TARGET_VECTOR)
#define HAVE_pred_indexed_ustorevnx1sivnx1hi (TARGET_VECTOR)
#define HAVE_pred_indexed_ostorevnx1sivnx1si (TARGET_VECTOR)
#define HAVE_pred_indexed_ustorevnx1sivnx1si (TARGET_VECTOR)
#define HAVE_pred_indexed_ostorevnx1sivnx1di ((TARGET_VECTOR) && (TARGET_64BIT && TARGET_MIN_VLEN > 32))
#define HAVE_pred_indexed_ustorevnx1sivnx1di ((TARGET_VECTOR) && (TARGET_64BIT && TARGET_MIN_VLEN > 32))
#define HAVE_pred_indexed_ostorevnx1divnx1qi ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_indexed_ustorevnx1divnx1qi ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_indexed_ostorevnx1divnx1hi ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_indexed_ustorevnx1divnx1hi ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_indexed_ostorevnx1divnx1si ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_indexed_ustorevnx1divnx1si ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_indexed_ostorevnx1divnx1di ((TARGET_VECTOR) && ((TARGET_64BIT && TARGET_MIN_VLEN > 32) && (TARGET_VECTOR_ELEN_64)))
#define HAVE_pred_indexed_ustorevnx1divnx1di ((TARGET_VECTOR) && ((TARGET_64BIT && TARGET_MIN_VLEN > 32) && (TARGET_VECTOR_ELEN_64)))
#define HAVE_pred_indexed_ostorevnx1sfvnx1qi ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_indexed_ustorevnx1sfvnx1qi ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_indexed_ostorevnx1sfvnx1hi ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_indexed_ustorevnx1sfvnx1hi ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_indexed_ostorevnx1sfvnx1si ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_indexed_ustorevnx1sfvnx1si ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_indexed_ostorevnx1sfvnx1di ((TARGET_VECTOR) && ((TARGET_64BIT && TARGET_MIN_VLEN > 32) && (TARGET_VECTOR_ELEN_FP_32)))
#define HAVE_pred_indexed_ustorevnx1sfvnx1di ((TARGET_VECTOR) && ((TARGET_64BIT && TARGET_MIN_VLEN > 32) && (TARGET_VECTOR_ELEN_FP_32)))
#define HAVE_pred_indexed_ostorevnx1dfvnx1qi ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_indexed_ustorevnx1dfvnx1qi ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_indexed_ostorevnx1dfvnx1hi ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_indexed_ustorevnx1dfvnx1hi ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_indexed_ostorevnx1dfvnx1si ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_indexed_ustorevnx1dfvnx1si ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_indexed_ostorevnx1dfvnx1di ((TARGET_VECTOR) && ((TARGET_64BIT && TARGET_MIN_VLEN > 32) && (TARGET_VECTOR_ELEN_FP_64)))
#define HAVE_pred_indexed_ustorevnx1dfvnx1di ((TARGET_VECTOR) && ((TARGET_64BIT && TARGET_MIN_VLEN > 32) && (TARGET_VECTOR_ELEN_FP_64)))
#define HAVE_pred_indexed_ostorevnx2qivnx2qi (TARGET_VECTOR)
#define HAVE_pred_indexed_ustorevnx2qivnx2qi (TARGET_VECTOR)
#define HAVE_pred_indexed_ostorevnx2hivnx2qi (TARGET_VECTOR)
#define HAVE_pred_indexed_ustorevnx2hivnx2qi (TARGET_VECTOR)
#define HAVE_pred_indexed_ostorevnx2sivnx2qi (TARGET_VECTOR)
#define HAVE_pred_indexed_ustorevnx2sivnx2qi (TARGET_VECTOR)
#define HAVE_pred_indexed_ostorevnx2divnx2qi ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_indexed_ustorevnx2divnx2qi ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_indexed_ostorevnx2sfvnx2qi ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_indexed_ustorevnx2sfvnx2qi ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_indexed_ostorevnx2dfvnx2qi ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_indexed_ustorevnx2dfvnx2qi ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_indexed_ostorevnx2qivnx2hi (TARGET_VECTOR)
#define HAVE_pred_indexed_ustorevnx2qivnx2hi (TARGET_VECTOR)
#define HAVE_pred_indexed_ostorevnx2hivnx2hi (TARGET_VECTOR)
#define HAVE_pred_indexed_ustorevnx2hivnx2hi (TARGET_VECTOR)
#define HAVE_pred_indexed_ostorevnx2sivnx2hi (TARGET_VECTOR)
#define HAVE_pred_indexed_ustorevnx2sivnx2hi (TARGET_VECTOR)
#define HAVE_pred_indexed_ostorevnx2divnx2hi ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_indexed_ustorevnx2divnx2hi ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_indexed_ostorevnx2sfvnx2hi ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_indexed_ustorevnx2sfvnx2hi ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_indexed_ostorevnx2dfvnx2hi ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_indexed_ustorevnx2dfvnx2hi ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_indexed_ostorevnx2qivnx2si (TARGET_VECTOR)
#define HAVE_pred_indexed_ustorevnx2qivnx2si (TARGET_VECTOR)
#define HAVE_pred_indexed_ostorevnx2hivnx2si (TARGET_VECTOR)
#define HAVE_pred_indexed_ustorevnx2hivnx2si (TARGET_VECTOR)
#define HAVE_pred_indexed_ostorevnx2sivnx2si (TARGET_VECTOR)
#define HAVE_pred_indexed_ustorevnx2sivnx2si (TARGET_VECTOR)
#define HAVE_pred_indexed_ostorevnx2divnx2si ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_indexed_ustorevnx2divnx2si ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_indexed_ostorevnx2sfvnx2si ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_indexed_ustorevnx2sfvnx2si ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_indexed_ostorevnx2dfvnx2si ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_indexed_ustorevnx2dfvnx2si ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_indexed_ostorevnx2qivnx2di ((TARGET_VECTOR) && (TARGET_64BIT && TARGET_MIN_VLEN > 32))
#define HAVE_pred_indexed_ustorevnx2qivnx2di ((TARGET_VECTOR) && (TARGET_64BIT && TARGET_MIN_VLEN > 32))
#define HAVE_pred_indexed_ostorevnx2hivnx2di ((TARGET_VECTOR) && (TARGET_64BIT && TARGET_MIN_VLEN > 32))
#define HAVE_pred_indexed_ustorevnx2hivnx2di ((TARGET_VECTOR) && (TARGET_64BIT && TARGET_MIN_VLEN > 32))
#define HAVE_pred_indexed_ostorevnx2sivnx2di ((TARGET_VECTOR) && (TARGET_64BIT && TARGET_MIN_VLEN > 32))
#define HAVE_pred_indexed_ustorevnx2sivnx2di ((TARGET_VECTOR) && (TARGET_64BIT && TARGET_MIN_VLEN > 32))
#define HAVE_pred_indexed_ostorevnx2divnx2di ((TARGET_VECTOR) && ((TARGET_64BIT && TARGET_MIN_VLEN > 32) && (TARGET_VECTOR_ELEN_64)))
#define HAVE_pred_indexed_ustorevnx2divnx2di ((TARGET_VECTOR) && ((TARGET_64BIT && TARGET_MIN_VLEN > 32) && (TARGET_VECTOR_ELEN_64)))
#define HAVE_pred_indexed_ostorevnx2sfvnx2di ((TARGET_VECTOR) && ((TARGET_64BIT && TARGET_MIN_VLEN > 32) && (TARGET_VECTOR_ELEN_FP_32)))
#define HAVE_pred_indexed_ustorevnx2sfvnx2di ((TARGET_VECTOR) && ((TARGET_64BIT && TARGET_MIN_VLEN > 32) && (TARGET_VECTOR_ELEN_FP_32)))
#define HAVE_pred_indexed_ostorevnx2dfvnx2di ((TARGET_VECTOR) && ((TARGET_64BIT && TARGET_MIN_VLEN > 32) && (TARGET_VECTOR_ELEN_FP_64)))
#define HAVE_pred_indexed_ustorevnx2dfvnx2di ((TARGET_VECTOR) && ((TARGET_64BIT && TARGET_MIN_VLEN > 32) && (TARGET_VECTOR_ELEN_FP_64)))
#define HAVE_pred_indexed_ostorevnx4qivnx4qi (TARGET_VECTOR)
#define HAVE_pred_indexed_ustorevnx4qivnx4qi (TARGET_VECTOR)
#define HAVE_pred_indexed_ostorevnx4hivnx4qi (TARGET_VECTOR)
#define HAVE_pred_indexed_ustorevnx4hivnx4qi (TARGET_VECTOR)
#define HAVE_pred_indexed_ostorevnx4sivnx4qi (TARGET_VECTOR)
#define HAVE_pred_indexed_ustorevnx4sivnx4qi (TARGET_VECTOR)
#define HAVE_pred_indexed_ostorevnx4divnx4qi ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_indexed_ustorevnx4divnx4qi ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_indexed_ostorevnx4sfvnx4qi ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_indexed_ustorevnx4sfvnx4qi ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_indexed_ostorevnx4dfvnx4qi ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_indexed_ustorevnx4dfvnx4qi ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_indexed_ostorevnx4qivnx4hi (TARGET_VECTOR)
#define HAVE_pred_indexed_ustorevnx4qivnx4hi (TARGET_VECTOR)
#define HAVE_pred_indexed_ostorevnx4hivnx4hi (TARGET_VECTOR)
#define HAVE_pred_indexed_ustorevnx4hivnx4hi (TARGET_VECTOR)
#define HAVE_pred_indexed_ostorevnx4sivnx4hi (TARGET_VECTOR)
#define HAVE_pred_indexed_ustorevnx4sivnx4hi (TARGET_VECTOR)
#define HAVE_pred_indexed_ostorevnx4divnx4hi ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_indexed_ustorevnx4divnx4hi ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_indexed_ostorevnx4sfvnx4hi ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_indexed_ustorevnx4sfvnx4hi ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_indexed_ostorevnx4dfvnx4hi ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_indexed_ustorevnx4dfvnx4hi ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_indexed_ostorevnx4qivnx4si (TARGET_VECTOR)
#define HAVE_pred_indexed_ustorevnx4qivnx4si (TARGET_VECTOR)
#define HAVE_pred_indexed_ostorevnx4hivnx4si (TARGET_VECTOR)
#define HAVE_pred_indexed_ustorevnx4hivnx4si (TARGET_VECTOR)
#define HAVE_pred_indexed_ostorevnx4sivnx4si (TARGET_VECTOR)
#define HAVE_pred_indexed_ustorevnx4sivnx4si (TARGET_VECTOR)
#define HAVE_pred_indexed_ostorevnx4divnx4si ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_indexed_ustorevnx4divnx4si ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_indexed_ostorevnx4sfvnx4si ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_indexed_ustorevnx4sfvnx4si ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_indexed_ostorevnx4dfvnx4si ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_indexed_ustorevnx4dfvnx4si ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_indexed_ostorevnx4qivnx4di ((TARGET_VECTOR) && (TARGET_64BIT && TARGET_MIN_VLEN > 32))
#define HAVE_pred_indexed_ustorevnx4qivnx4di ((TARGET_VECTOR) && (TARGET_64BIT && TARGET_MIN_VLEN > 32))
#define HAVE_pred_indexed_ostorevnx4hivnx4di ((TARGET_VECTOR) && (TARGET_64BIT && TARGET_MIN_VLEN > 32))
#define HAVE_pred_indexed_ustorevnx4hivnx4di ((TARGET_VECTOR) && (TARGET_64BIT && TARGET_MIN_VLEN > 32))
#define HAVE_pred_indexed_ostorevnx4sivnx4di ((TARGET_VECTOR) && (TARGET_64BIT && TARGET_MIN_VLEN > 32))
#define HAVE_pred_indexed_ustorevnx4sivnx4di ((TARGET_VECTOR) && (TARGET_64BIT && TARGET_MIN_VLEN > 32))
#define HAVE_pred_indexed_ostorevnx4divnx4di ((TARGET_VECTOR) && ((TARGET_64BIT && TARGET_MIN_VLEN > 32) && (TARGET_VECTOR_ELEN_64)))
#define HAVE_pred_indexed_ustorevnx4divnx4di ((TARGET_VECTOR) && ((TARGET_64BIT && TARGET_MIN_VLEN > 32) && (TARGET_VECTOR_ELEN_64)))
#define HAVE_pred_indexed_ostorevnx4sfvnx4di ((TARGET_VECTOR) && ((TARGET_64BIT && TARGET_MIN_VLEN > 32) && (TARGET_VECTOR_ELEN_FP_32)))
#define HAVE_pred_indexed_ustorevnx4sfvnx4di ((TARGET_VECTOR) && ((TARGET_64BIT && TARGET_MIN_VLEN > 32) && (TARGET_VECTOR_ELEN_FP_32)))
#define HAVE_pred_indexed_ostorevnx4dfvnx4di ((TARGET_VECTOR) && ((TARGET_64BIT && TARGET_MIN_VLEN > 32) && (TARGET_VECTOR_ELEN_FP_64)))
#define HAVE_pred_indexed_ustorevnx4dfvnx4di ((TARGET_VECTOR) && ((TARGET_64BIT && TARGET_MIN_VLEN > 32) && (TARGET_VECTOR_ELEN_FP_64)))
#define HAVE_pred_indexed_ostorevnx8qivnx8qi (TARGET_VECTOR)
#define HAVE_pred_indexed_ustorevnx8qivnx8qi (TARGET_VECTOR)
#define HAVE_pred_indexed_ostorevnx8hivnx8qi (TARGET_VECTOR)
#define HAVE_pred_indexed_ustorevnx8hivnx8qi (TARGET_VECTOR)
#define HAVE_pred_indexed_ostorevnx8sivnx8qi (TARGET_VECTOR)
#define HAVE_pred_indexed_ustorevnx8sivnx8qi (TARGET_VECTOR)
#define HAVE_pred_indexed_ostorevnx8divnx8qi ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_indexed_ustorevnx8divnx8qi ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_indexed_ostorevnx8sfvnx8qi ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_indexed_ustorevnx8sfvnx8qi ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_indexed_ostorevnx8dfvnx8qi ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_indexed_ustorevnx8dfvnx8qi ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_indexed_ostorevnx8qivnx8hi (TARGET_VECTOR)
#define HAVE_pred_indexed_ustorevnx8qivnx8hi (TARGET_VECTOR)
#define HAVE_pred_indexed_ostorevnx8hivnx8hi (TARGET_VECTOR)
#define HAVE_pred_indexed_ustorevnx8hivnx8hi (TARGET_VECTOR)
#define HAVE_pred_indexed_ostorevnx8sivnx8hi (TARGET_VECTOR)
#define HAVE_pred_indexed_ustorevnx8sivnx8hi (TARGET_VECTOR)
#define HAVE_pred_indexed_ostorevnx8divnx8hi ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_indexed_ustorevnx8divnx8hi ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_indexed_ostorevnx8sfvnx8hi ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_indexed_ustorevnx8sfvnx8hi ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_indexed_ostorevnx8dfvnx8hi ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_indexed_ustorevnx8dfvnx8hi ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_indexed_ostorevnx8qivnx8si (TARGET_VECTOR)
#define HAVE_pred_indexed_ustorevnx8qivnx8si (TARGET_VECTOR)
#define HAVE_pred_indexed_ostorevnx8hivnx8si (TARGET_VECTOR)
#define HAVE_pred_indexed_ustorevnx8hivnx8si (TARGET_VECTOR)
#define HAVE_pred_indexed_ostorevnx8sivnx8si (TARGET_VECTOR)
#define HAVE_pred_indexed_ustorevnx8sivnx8si (TARGET_VECTOR)
#define HAVE_pred_indexed_ostorevnx8divnx8si ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_indexed_ustorevnx8divnx8si ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_indexed_ostorevnx8sfvnx8si ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_indexed_ustorevnx8sfvnx8si ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_indexed_ostorevnx8dfvnx8si ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_indexed_ustorevnx8dfvnx8si ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_indexed_ostorevnx8qivnx8di ((TARGET_VECTOR) && (TARGET_64BIT && TARGET_MIN_VLEN > 32))
#define HAVE_pred_indexed_ustorevnx8qivnx8di ((TARGET_VECTOR) && (TARGET_64BIT && TARGET_MIN_VLEN > 32))
#define HAVE_pred_indexed_ostorevnx8hivnx8di ((TARGET_VECTOR) && (TARGET_64BIT && TARGET_MIN_VLEN > 32))
#define HAVE_pred_indexed_ustorevnx8hivnx8di ((TARGET_VECTOR) && (TARGET_64BIT && TARGET_MIN_VLEN > 32))
#define HAVE_pred_indexed_ostorevnx8sivnx8di ((TARGET_VECTOR) && (TARGET_64BIT && TARGET_MIN_VLEN > 32))
#define HAVE_pred_indexed_ustorevnx8sivnx8di ((TARGET_VECTOR) && (TARGET_64BIT && TARGET_MIN_VLEN > 32))
#define HAVE_pred_indexed_ostorevnx8divnx8di ((TARGET_VECTOR) && ((TARGET_64BIT && TARGET_MIN_VLEN > 32) && (TARGET_VECTOR_ELEN_64)))
#define HAVE_pred_indexed_ustorevnx8divnx8di ((TARGET_VECTOR) && ((TARGET_64BIT && TARGET_MIN_VLEN > 32) && (TARGET_VECTOR_ELEN_64)))
#define HAVE_pred_indexed_ostorevnx8sfvnx8di ((TARGET_VECTOR) && ((TARGET_64BIT && TARGET_MIN_VLEN > 32) && (TARGET_VECTOR_ELEN_FP_32)))
#define HAVE_pred_indexed_ustorevnx8sfvnx8di ((TARGET_VECTOR) && ((TARGET_64BIT && TARGET_MIN_VLEN > 32) && (TARGET_VECTOR_ELEN_FP_32)))
#define HAVE_pred_indexed_ostorevnx8dfvnx8di ((TARGET_VECTOR) && ((TARGET_64BIT && TARGET_MIN_VLEN > 32) && (TARGET_VECTOR_ELEN_FP_64)))
#define HAVE_pred_indexed_ustorevnx8dfvnx8di ((TARGET_VECTOR) && ((TARGET_64BIT && TARGET_MIN_VLEN > 32) && (TARGET_VECTOR_ELEN_FP_64)))
#define HAVE_pred_indexed_ostorevnx16qivnx16qi (TARGET_VECTOR)
#define HAVE_pred_indexed_ustorevnx16qivnx16qi (TARGET_VECTOR)
#define HAVE_pred_indexed_ostorevnx16hivnx16qi (TARGET_VECTOR)
#define HAVE_pred_indexed_ustorevnx16hivnx16qi (TARGET_VECTOR)
#define HAVE_pred_indexed_ostorevnx16sivnx16qi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_indexed_ustorevnx16sivnx16qi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_indexed_ostorevnx16sfvnx16qi ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32 && TARGET_MIN_VLEN > 32))
#define HAVE_pred_indexed_ustorevnx16sfvnx16qi ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32 && TARGET_MIN_VLEN > 32))
#define HAVE_pred_indexed_ostorevnx16qivnx16hi (TARGET_VECTOR)
#define HAVE_pred_indexed_ustorevnx16qivnx16hi (TARGET_VECTOR)
#define HAVE_pred_indexed_ostorevnx16hivnx16hi (TARGET_VECTOR)
#define HAVE_pred_indexed_ustorevnx16hivnx16hi (TARGET_VECTOR)
#define HAVE_pred_indexed_ostorevnx16sivnx16hi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_indexed_ustorevnx16sivnx16hi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_indexed_ostorevnx16sfvnx16hi ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32 && TARGET_MIN_VLEN > 32))
#define HAVE_pred_indexed_ustorevnx16sfvnx16hi ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32 && TARGET_MIN_VLEN > 32))
#define HAVE_pred_indexed_ostorevnx16qivnx16si ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_indexed_ustorevnx16qivnx16si ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_indexed_ostorevnx16hivnx16si ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_indexed_ustorevnx16hivnx16si ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_indexed_ostorevnx16sivnx16si ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_indexed_ustorevnx16sivnx16si ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_indexed_ostorevnx16sfvnx16si ((TARGET_VECTOR) && ((TARGET_MIN_VLEN > 32) && (TARGET_VECTOR_ELEN_FP_32 && TARGET_MIN_VLEN > 32)))
#define HAVE_pred_indexed_ustorevnx16sfvnx16si ((TARGET_VECTOR) && ((TARGET_MIN_VLEN > 32) && (TARGET_VECTOR_ELEN_FP_32 && TARGET_MIN_VLEN > 32)))
#define HAVE_pred_indexed_ostorevnx32qivnx32qi (TARGET_VECTOR)
#define HAVE_pred_indexed_ustorevnx32qivnx32qi (TARGET_VECTOR)
#define HAVE_pred_indexed_ostorevnx32qivnx32hi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_indexed_ustorevnx32qivnx32hi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_indexed_ostorevnx32hivnx32qi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_indexed_ustorevnx32hivnx32qi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_indexed_ostorevnx32hivnx32hi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_indexed_ustorevnx32hivnx32hi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_indexed_ostorevnx64qivnx64qi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_indexed_ustorevnx64qivnx64qi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_addvnx1qi (TARGET_VECTOR)
#define HAVE_pred_subvnx1qi (TARGET_VECTOR)
#define HAVE_pred_andvnx1qi (TARGET_VECTOR)
#define HAVE_pred_iorvnx1qi (TARGET_VECTOR)
#define HAVE_pred_xorvnx1qi (TARGET_VECTOR)
#define HAVE_pred_ashlvnx1qi (TARGET_VECTOR)
#define HAVE_pred_ashrvnx1qi (TARGET_VECTOR)
#define HAVE_pred_lshrvnx1qi (TARGET_VECTOR)
#define HAVE_pred_smaxvnx1qi (TARGET_VECTOR)
#define HAVE_pred_umaxvnx1qi (TARGET_VECTOR)
#define HAVE_pred_sminvnx1qi (TARGET_VECTOR)
#define HAVE_pred_uminvnx1qi (TARGET_VECTOR)
#define HAVE_pred_mulvnx1qi (TARGET_VECTOR)
#define HAVE_pred_divvnx1qi (TARGET_VECTOR)
#define HAVE_pred_udivvnx1qi (TARGET_VECTOR)
#define HAVE_pred_modvnx1qi (TARGET_VECTOR)
#define HAVE_pred_umodvnx1qi (TARGET_VECTOR)
#define HAVE_pred_addvnx2qi (TARGET_VECTOR)
#define HAVE_pred_subvnx2qi (TARGET_VECTOR)
#define HAVE_pred_andvnx2qi (TARGET_VECTOR)
#define HAVE_pred_iorvnx2qi (TARGET_VECTOR)
#define HAVE_pred_xorvnx2qi (TARGET_VECTOR)
#define HAVE_pred_ashlvnx2qi (TARGET_VECTOR)
#define HAVE_pred_ashrvnx2qi (TARGET_VECTOR)
#define HAVE_pred_lshrvnx2qi (TARGET_VECTOR)
#define HAVE_pred_smaxvnx2qi (TARGET_VECTOR)
#define HAVE_pred_umaxvnx2qi (TARGET_VECTOR)
#define HAVE_pred_sminvnx2qi (TARGET_VECTOR)
#define HAVE_pred_uminvnx2qi (TARGET_VECTOR)
#define HAVE_pred_mulvnx2qi (TARGET_VECTOR)
#define HAVE_pred_divvnx2qi (TARGET_VECTOR)
#define HAVE_pred_udivvnx2qi (TARGET_VECTOR)
#define HAVE_pred_modvnx2qi (TARGET_VECTOR)
#define HAVE_pred_umodvnx2qi (TARGET_VECTOR)
#define HAVE_pred_addvnx4qi (TARGET_VECTOR)
#define HAVE_pred_subvnx4qi (TARGET_VECTOR)
#define HAVE_pred_andvnx4qi (TARGET_VECTOR)
#define HAVE_pred_iorvnx4qi (TARGET_VECTOR)
#define HAVE_pred_xorvnx4qi (TARGET_VECTOR)
#define HAVE_pred_ashlvnx4qi (TARGET_VECTOR)
#define HAVE_pred_ashrvnx4qi (TARGET_VECTOR)
#define HAVE_pred_lshrvnx4qi (TARGET_VECTOR)
#define HAVE_pred_smaxvnx4qi (TARGET_VECTOR)
#define HAVE_pred_umaxvnx4qi (TARGET_VECTOR)
#define HAVE_pred_sminvnx4qi (TARGET_VECTOR)
#define HAVE_pred_uminvnx4qi (TARGET_VECTOR)
#define HAVE_pred_mulvnx4qi (TARGET_VECTOR)
#define HAVE_pred_divvnx4qi (TARGET_VECTOR)
#define HAVE_pred_udivvnx4qi (TARGET_VECTOR)
#define HAVE_pred_modvnx4qi (TARGET_VECTOR)
#define HAVE_pred_umodvnx4qi (TARGET_VECTOR)
#define HAVE_pred_addvnx8qi (TARGET_VECTOR)
#define HAVE_pred_subvnx8qi (TARGET_VECTOR)
#define HAVE_pred_andvnx8qi (TARGET_VECTOR)
#define HAVE_pred_iorvnx8qi (TARGET_VECTOR)
#define HAVE_pred_xorvnx8qi (TARGET_VECTOR)
#define HAVE_pred_ashlvnx8qi (TARGET_VECTOR)
#define HAVE_pred_ashrvnx8qi (TARGET_VECTOR)
#define HAVE_pred_lshrvnx8qi (TARGET_VECTOR)
#define HAVE_pred_smaxvnx8qi (TARGET_VECTOR)
#define HAVE_pred_umaxvnx8qi (TARGET_VECTOR)
#define HAVE_pred_sminvnx8qi (TARGET_VECTOR)
#define HAVE_pred_uminvnx8qi (TARGET_VECTOR)
#define HAVE_pred_mulvnx8qi (TARGET_VECTOR)
#define HAVE_pred_divvnx8qi (TARGET_VECTOR)
#define HAVE_pred_udivvnx8qi (TARGET_VECTOR)
#define HAVE_pred_modvnx8qi (TARGET_VECTOR)
#define HAVE_pred_umodvnx8qi (TARGET_VECTOR)
#define HAVE_pred_addvnx16qi (TARGET_VECTOR)
#define HAVE_pred_subvnx16qi (TARGET_VECTOR)
#define HAVE_pred_andvnx16qi (TARGET_VECTOR)
#define HAVE_pred_iorvnx16qi (TARGET_VECTOR)
#define HAVE_pred_xorvnx16qi (TARGET_VECTOR)
#define HAVE_pred_ashlvnx16qi (TARGET_VECTOR)
#define HAVE_pred_ashrvnx16qi (TARGET_VECTOR)
#define HAVE_pred_lshrvnx16qi (TARGET_VECTOR)
#define HAVE_pred_smaxvnx16qi (TARGET_VECTOR)
#define HAVE_pred_umaxvnx16qi (TARGET_VECTOR)
#define HAVE_pred_sminvnx16qi (TARGET_VECTOR)
#define HAVE_pred_uminvnx16qi (TARGET_VECTOR)
#define HAVE_pred_mulvnx16qi (TARGET_VECTOR)
#define HAVE_pred_divvnx16qi (TARGET_VECTOR)
#define HAVE_pred_udivvnx16qi (TARGET_VECTOR)
#define HAVE_pred_modvnx16qi (TARGET_VECTOR)
#define HAVE_pred_umodvnx16qi (TARGET_VECTOR)
#define HAVE_pred_addvnx32qi (TARGET_VECTOR)
#define HAVE_pred_subvnx32qi (TARGET_VECTOR)
#define HAVE_pred_andvnx32qi (TARGET_VECTOR)
#define HAVE_pred_iorvnx32qi (TARGET_VECTOR)
#define HAVE_pred_xorvnx32qi (TARGET_VECTOR)
#define HAVE_pred_ashlvnx32qi (TARGET_VECTOR)
#define HAVE_pred_ashrvnx32qi (TARGET_VECTOR)
#define HAVE_pred_lshrvnx32qi (TARGET_VECTOR)
#define HAVE_pred_smaxvnx32qi (TARGET_VECTOR)
#define HAVE_pred_umaxvnx32qi (TARGET_VECTOR)
#define HAVE_pred_sminvnx32qi (TARGET_VECTOR)
#define HAVE_pred_uminvnx32qi (TARGET_VECTOR)
#define HAVE_pred_mulvnx32qi (TARGET_VECTOR)
#define HAVE_pred_divvnx32qi (TARGET_VECTOR)
#define HAVE_pred_udivvnx32qi (TARGET_VECTOR)
#define HAVE_pred_modvnx32qi (TARGET_VECTOR)
#define HAVE_pred_umodvnx32qi (TARGET_VECTOR)
#define HAVE_pred_addvnx64qi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_subvnx64qi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_andvnx64qi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_iorvnx64qi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_xorvnx64qi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_ashlvnx64qi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_ashrvnx64qi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_lshrvnx64qi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_smaxvnx64qi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_umaxvnx64qi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_sminvnx64qi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_uminvnx64qi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_mulvnx64qi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_divvnx64qi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_udivvnx64qi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_modvnx64qi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_umodvnx64qi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_addvnx1hi (TARGET_VECTOR)
#define HAVE_pred_subvnx1hi (TARGET_VECTOR)
#define HAVE_pred_andvnx1hi (TARGET_VECTOR)
#define HAVE_pred_iorvnx1hi (TARGET_VECTOR)
#define HAVE_pred_xorvnx1hi (TARGET_VECTOR)
#define HAVE_pred_ashlvnx1hi (TARGET_VECTOR)
#define HAVE_pred_ashrvnx1hi (TARGET_VECTOR)
#define HAVE_pred_lshrvnx1hi (TARGET_VECTOR)
#define HAVE_pred_smaxvnx1hi (TARGET_VECTOR)
#define HAVE_pred_umaxvnx1hi (TARGET_VECTOR)
#define HAVE_pred_sminvnx1hi (TARGET_VECTOR)
#define HAVE_pred_uminvnx1hi (TARGET_VECTOR)
#define HAVE_pred_mulvnx1hi (TARGET_VECTOR)
#define HAVE_pred_divvnx1hi (TARGET_VECTOR)
#define HAVE_pred_udivvnx1hi (TARGET_VECTOR)
#define HAVE_pred_modvnx1hi (TARGET_VECTOR)
#define HAVE_pred_umodvnx1hi (TARGET_VECTOR)
#define HAVE_pred_addvnx2hi (TARGET_VECTOR)
#define HAVE_pred_subvnx2hi (TARGET_VECTOR)
#define HAVE_pred_andvnx2hi (TARGET_VECTOR)
#define HAVE_pred_iorvnx2hi (TARGET_VECTOR)
#define HAVE_pred_xorvnx2hi (TARGET_VECTOR)
#define HAVE_pred_ashlvnx2hi (TARGET_VECTOR)
#define HAVE_pred_ashrvnx2hi (TARGET_VECTOR)
#define HAVE_pred_lshrvnx2hi (TARGET_VECTOR)
#define HAVE_pred_smaxvnx2hi (TARGET_VECTOR)
#define HAVE_pred_umaxvnx2hi (TARGET_VECTOR)
#define HAVE_pred_sminvnx2hi (TARGET_VECTOR)
#define HAVE_pred_uminvnx2hi (TARGET_VECTOR)
#define HAVE_pred_mulvnx2hi (TARGET_VECTOR)
#define HAVE_pred_divvnx2hi (TARGET_VECTOR)
#define HAVE_pred_udivvnx2hi (TARGET_VECTOR)
#define HAVE_pred_modvnx2hi (TARGET_VECTOR)
#define HAVE_pred_umodvnx2hi (TARGET_VECTOR)
#define HAVE_pred_addvnx4hi (TARGET_VECTOR)
#define HAVE_pred_subvnx4hi (TARGET_VECTOR)
#define HAVE_pred_andvnx4hi (TARGET_VECTOR)
#define HAVE_pred_iorvnx4hi (TARGET_VECTOR)
#define HAVE_pred_xorvnx4hi (TARGET_VECTOR)
#define HAVE_pred_ashlvnx4hi (TARGET_VECTOR)
#define HAVE_pred_ashrvnx4hi (TARGET_VECTOR)
#define HAVE_pred_lshrvnx4hi (TARGET_VECTOR)
#define HAVE_pred_smaxvnx4hi (TARGET_VECTOR)
#define HAVE_pred_umaxvnx4hi (TARGET_VECTOR)
#define HAVE_pred_sminvnx4hi (TARGET_VECTOR)
#define HAVE_pred_uminvnx4hi (TARGET_VECTOR)
#define HAVE_pred_mulvnx4hi (TARGET_VECTOR)
#define HAVE_pred_divvnx4hi (TARGET_VECTOR)
#define HAVE_pred_udivvnx4hi (TARGET_VECTOR)
#define HAVE_pred_modvnx4hi (TARGET_VECTOR)
#define HAVE_pred_umodvnx4hi (TARGET_VECTOR)
#define HAVE_pred_addvnx8hi (TARGET_VECTOR)
#define HAVE_pred_subvnx8hi (TARGET_VECTOR)
#define HAVE_pred_andvnx8hi (TARGET_VECTOR)
#define HAVE_pred_iorvnx8hi (TARGET_VECTOR)
#define HAVE_pred_xorvnx8hi (TARGET_VECTOR)
#define HAVE_pred_ashlvnx8hi (TARGET_VECTOR)
#define HAVE_pred_ashrvnx8hi (TARGET_VECTOR)
#define HAVE_pred_lshrvnx8hi (TARGET_VECTOR)
#define HAVE_pred_smaxvnx8hi (TARGET_VECTOR)
#define HAVE_pred_umaxvnx8hi (TARGET_VECTOR)
#define HAVE_pred_sminvnx8hi (TARGET_VECTOR)
#define HAVE_pred_uminvnx8hi (TARGET_VECTOR)
#define HAVE_pred_mulvnx8hi (TARGET_VECTOR)
#define HAVE_pred_divvnx8hi (TARGET_VECTOR)
#define HAVE_pred_udivvnx8hi (TARGET_VECTOR)
#define HAVE_pred_modvnx8hi (TARGET_VECTOR)
#define HAVE_pred_umodvnx8hi (TARGET_VECTOR)
#define HAVE_pred_addvnx16hi (TARGET_VECTOR)
#define HAVE_pred_subvnx16hi (TARGET_VECTOR)
#define HAVE_pred_andvnx16hi (TARGET_VECTOR)
#define HAVE_pred_iorvnx16hi (TARGET_VECTOR)
#define HAVE_pred_xorvnx16hi (TARGET_VECTOR)
#define HAVE_pred_ashlvnx16hi (TARGET_VECTOR)
#define HAVE_pred_ashrvnx16hi (TARGET_VECTOR)
#define HAVE_pred_lshrvnx16hi (TARGET_VECTOR)
#define HAVE_pred_smaxvnx16hi (TARGET_VECTOR)
#define HAVE_pred_umaxvnx16hi (TARGET_VECTOR)
#define HAVE_pred_sminvnx16hi (TARGET_VECTOR)
#define HAVE_pred_uminvnx16hi (TARGET_VECTOR)
#define HAVE_pred_mulvnx16hi (TARGET_VECTOR)
#define HAVE_pred_divvnx16hi (TARGET_VECTOR)
#define HAVE_pred_udivvnx16hi (TARGET_VECTOR)
#define HAVE_pred_modvnx16hi (TARGET_VECTOR)
#define HAVE_pred_umodvnx16hi (TARGET_VECTOR)
#define HAVE_pred_addvnx32hi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_subvnx32hi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_andvnx32hi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_iorvnx32hi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_xorvnx32hi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_ashlvnx32hi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_ashrvnx32hi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_lshrvnx32hi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_smaxvnx32hi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_umaxvnx32hi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_sminvnx32hi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_uminvnx32hi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_mulvnx32hi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_divvnx32hi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_udivvnx32hi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_modvnx32hi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_umodvnx32hi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_addvnx1si (TARGET_VECTOR)
#define HAVE_pred_subvnx1si (TARGET_VECTOR)
#define HAVE_pred_andvnx1si (TARGET_VECTOR)
#define HAVE_pred_iorvnx1si (TARGET_VECTOR)
#define HAVE_pred_xorvnx1si (TARGET_VECTOR)
#define HAVE_pred_ashlvnx1si (TARGET_VECTOR)
#define HAVE_pred_ashrvnx1si (TARGET_VECTOR)
#define HAVE_pred_lshrvnx1si (TARGET_VECTOR)
#define HAVE_pred_smaxvnx1si (TARGET_VECTOR)
#define HAVE_pred_umaxvnx1si (TARGET_VECTOR)
#define HAVE_pred_sminvnx1si (TARGET_VECTOR)
#define HAVE_pred_uminvnx1si (TARGET_VECTOR)
#define HAVE_pred_mulvnx1si (TARGET_VECTOR)
#define HAVE_pred_divvnx1si (TARGET_VECTOR)
#define HAVE_pred_udivvnx1si (TARGET_VECTOR)
#define HAVE_pred_modvnx1si (TARGET_VECTOR)
#define HAVE_pred_umodvnx1si (TARGET_VECTOR)
#define HAVE_pred_addvnx2si (TARGET_VECTOR)
#define HAVE_pred_subvnx2si (TARGET_VECTOR)
#define HAVE_pred_andvnx2si (TARGET_VECTOR)
#define HAVE_pred_iorvnx2si (TARGET_VECTOR)
#define HAVE_pred_xorvnx2si (TARGET_VECTOR)
#define HAVE_pred_ashlvnx2si (TARGET_VECTOR)
#define HAVE_pred_ashrvnx2si (TARGET_VECTOR)
#define HAVE_pred_lshrvnx2si (TARGET_VECTOR)
#define HAVE_pred_smaxvnx2si (TARGET_VECTOR)
#define HAVE_pred_umaxvnx2si (TARGET_VECTOR)
#define HAVE_pred_sminvnx2si (TARGET_VECTOR)
#define HAVE_pred_uminvnx2si (TARGET_VECTOR)
#define HAVE_pred_mulvnx2si (TARGET_VECTOR)
#define HAVE_pred_divvnx2si (TARGET_VECTOR)
#define HAVE_pred_udivvnx2si (TARGET_VECTOR)
#define HAVE_pred_modvnx2si (TARGET_VECTOR)
#define HAVE_pred_umodvnx2si (TARGET_VECTOR)
#define HAVE_pred_addvnx4si (TARGET_VECTOR)
#define HAVE_pred_subvnx4si (TARGET_VECTOR)
#define HAVE_pred_andvnx4si (TARGET_VECTOR)
#define HAVE_pred_iorvnx4si (TARGET_VECTOR)
#define HAVE_pred_xorvnx4si (TARGET_VECTOR)
#define HAVE_pred_ashlvnx4si (TARGET_VECTOR)
#define HAVE_pred_ashrvnx4si (TARGET_VECTOR)
#define HAVE_pred_lshrvnx4si (TARGET_VECTOR)
#define HAVE_pred_smaxvnx4si (TARGET_VECTOR)
#define HAVE_pred_umaxvnx4si (TARGET_VECTOR)
#define HAVE_pred_sminvnx4si (TARGET_VECTOR)
#define HAVE_pred_uminvnx4si (TARGET_VECTOR)
#define HAVE_pred_mulvnx4si (TARGET_VECTOR)
#define HAVE_pred_divvnx4si (TARGET_VECTOR)
#define HAVE_pred_udivvnx4si (TARGET_VECTOR)
#define HAVE_pred_modvnx4si (TARGET_VECTOR)
#define HAVE_pred_umodvnx4si (TARGET_VECTOR)
#define HAVE_pred_addvnx8si (TARGET_VECTOR)
#define HAVE_pred_subvnx8si (TARGET_VECTOR)
#define HAVE_pred_andvnx8si (TARGET_VECTOR)
#define HAVE_pred_iorvnx8si (TARGET_VECTOR)
#define HAVE_pred_xorvnx8si (TARGET_VECTOR)
#define HAVE_pred_ashlvnx8si (TARGET_VECTOR)
#define HAVE_pred_ashrvnx8si (TARGET_VECTOR)
#define HAVE_pred_lshrvnx8si (TARGET_VECTOR)
#define HAVE_pred_smaxvnx8si (TARGET_VECTOR)
#define HAVE_pred_umaxvnx8si (TARGET_VECTOR)
#define HAVE_pred_sminvnx8si (TARGET_VECTOR)
#define HAVE_pred_uminvnx8si (TARGET_VECTOR)
#define HAVE_pred_mulvnx8si (TARGET_VECTOR)
#define HAVE_pred_divvnx8si (TARGET_VECTOR)
#define HAVE_pred_udivvnx8si (TARGET_VECTOR)
#define HAVE_pred_modvnx8si (TARGET_VECTOR)
#define HAVE_pred_umodvnx8si (TARGET_VECTOR)
#define HAVE_pred_addvnx16si ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_subvnx16si ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_andvnx16si ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_iorvnx16si ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_xorvnx16si ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_ashlvnx16si ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_ashrvnx16si ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_lshrvnx16si ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_smaxvnx16si ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_umaxvnx16si ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_sminvnx16si ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_uminvnx16si ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_mulvnx16si ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_divvnx16si ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_udivvnx16si ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_modvnx16si ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_umodvnx16si ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_addvnx1di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_subvnx1di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_andvnx1di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_iorvnx1di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_xorvnx1di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_ashlvnx1di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_ashrvnx1di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_lshrvnx1di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_smaxvnx1di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_umaxvnx1di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_sminvnx1di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_uminvnx1di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_mulvnx1di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_divvnx1di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_udivvnx1di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_modvnx1di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_umodvnx1di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_addvnx2di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_subvnx2di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_andvnx2di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_iorvnx2di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_xorvnx2di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_ashlvnx2di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_ashrvnx2di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_lshrvnx2di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_smaxvnx2di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_umaxvnx2di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_sminvnx2di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_uminvnx2di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_mulvnx2di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_divvnx2di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_udivvnx2di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_modvnx2di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_umodvnx2di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_addvnx4di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_subvnx4di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_andvnx4di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_iorvnx4di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_xorvnx4di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_ashlvnx4di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_ashrvnx4di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_lshrvnx4di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_smaxvnx4di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_umaxvnx4di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_sminvnx4di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_uminvnx4di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_mulvnx4di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_divvnx4di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_udivvnx4di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_modvnx4di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_umodvnx4di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_addvnx8di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_subvnx8di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_andvnx8di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_iorvnx8di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_xorvnx8di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_ashlvnx8di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_ashrvnx8di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_lshrvnx8di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_smaxvnx8di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_umaxvnx8di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_sminvnx8di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_uminvnx8di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_mulvnx8di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_divvnx8di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_udivvnx8di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_modvnx8di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_umodvnx8di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_ashlvnx1qi_scalar (TARGET_VECTOR)
#define HAVE_pred_ashrvnx1qi_scalar (TARGET_VECTOR)
#define HAVE_pred_lshrvnx1qi_scalar (TARGET_VECTOR)
#define HAVE_pred_ashlvnx2qi_scalar (TARGET_VECTOR)
#define HAVE_pred_ashrvnx2qi_scalar (TARGET_VECTOR)
#define HAVE_pred_lshrvnx2qi_scalar (TARGET_VECTOR)
#define HAVE_pred_ashlvnx4qi_scalar (TARGET_VECTOR)
#define HAVE_pred_ashrvnx4qi_scalar (TARGET_VECTOR)
#define HAVE_pred_lshrvnx4qi_scalar (TARGET_VECTOR)
#define HAVE_pred_ashlvnx8qi_scalar (TARGET_VECTOR)
#define HAVE_pred_ashrvnx8qi_scalar (TARGET_VECTOR)
#define HAVE_pred_lshrvnx8qi_scalar (TARGET_VECTOR)
#define HAVE_pred_ashlvnx16qi_scalar (TARGET_VECTOR)
#define HAVE_pred_ashrvnx16qi_scalar (TARGET_VECTOR)
#define HAVE_pred_lshrvnx16qi_scalar (TARGET_VECTOR)
#define HAVE_pred_ashlvnx32qi_scalar (TARGET_VECTOR)
#define HAVE_pred_ashrvnx32qi_scalar (TARGET_VECTOR)
#define HAVE_pred_lshrvnx32qi_scalar (TARGET_VECTOR)
#define HAVE_pred_ashlvnx64qi_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_ashrvnx64qi_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_lshrvnx64qi_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_ashlvnx1hi_scalar (TARGET_VECTOR)
#define HAVE_pred_ashrvnx1hi_scalar (TARGET_VECTOR)
#define HAVE_pred_lshrvnx1hi_scalar (TARGET_VECTOR)
#define HAVE_pred_ashlvnx2hi_scalar (TARGET_VECTOR)
#define HAVE_pred_ashrvnx2hi_scalar (TARGET_VECTOR)
#define HAVE_pred_lshrvnx2hi_scalar (TARGET_VECTOR)
#define HAVE_pred_ashlvnx4hi_scalar (TARGET_VECTOR)
#define HAVE_pred_ashrvnx4hi_scalar (TARGET_VECTOR)
#define HAVE_pred_lshrvnx4hi_scalar (TARGET_VECTOR)
#define HAVE_pred_ashlvnx8hi_scalar (TARGET_VECTOR)
#define HAVE_pred_ashrvnx8hi_scalar (TARGET_VECTOR)
#define HAVE_pred_lshrvnx8hi_scalar (TARGET_VECTOR)
#define HAVE_pred_ashlvnx16hi_scalar (TARGET_VECTOR)
#define HAVE_pred_ashrvnx16hi_scalar (TARGET_VECTOR)
#define HAVE_pred_lshrvnx16hi_scalar (TARGET_VECTOR)
#define HAVE_pred_ashlvnx32hi_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_ashrvnx32hi_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_lshrvnx32hi_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_ashlvnx1si_scalar (TARGET_VECTOR)
#define HAVE_pred_ashrvnx1si_scalar (TARGET_VECTOR)
#define HAVE_pred_lshrvnx1si_scalar (TARGET_VECTOR)
#define HAVE_pred_ashlvnx2si_scalar (TARGET_VECTOR)
#define HAVE_pred_ashrvnx2si_scalar (TARGET_VECTOR)
#define HAVE_pred_lshrvnx2si_scalar (TARGET_VECTOR)
#define HAVE_pred_ashlvnx4si_scalar (TARGET_VECTOR)
#define HAVE_pred_ashrvnx4si_scalar (TARGET_VECTOR)
#define HAVE_pred_lshrvnx4si_scalar (TARGET_VECTOR)
#define HAVE_pred_ashlvnx8si_scalar (TARGET_VECTOR)
#define HAVE_pred_ashrvnx8si_scalar (TARGET_VECTOR)
#define HAVE_pred_lshrvnx8si_scalar (TARGET_VECTOR)
#define HAVE_pred_ashlvnx16si_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_ashrvnx16si_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_lshrvnx16si_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_ashlvnx1di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_ashrvnx1di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_lshrvnx1di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_ashlvnx2di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_ashrvnx2di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_lshrvnx2di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_ashlvnx4di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_ashrvnx4di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_lshrvnx4di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_ashlvnx8di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_ashrvnx8di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_lshrvnx8di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_addvnx1qi_scalar (TARGET_VECTOR)
#define HAVE_pred_andvnx1qi_scalar (TARGET_VECTOR)
#define HAVE_pred_iorvnx1qi_scalar (TARGET_VECTOR)
#define HAVE_pred_xorvnx1qi_scalar (TARGET_VECTOR)
#define HAVE_pred_smaxvnx1qi_scalar (TARGET_VECTOR)
#define HAVE_pred_umaxvnx1qi_scalar (TARGET_VECTOR)
#define HAVE_pred_sminvnx1qi_scalar (TARGET_VECTOR)
#define HAVE_pred_uminvnx1qi_scalar (TARGET_VECTOR)
#define HAVE_pred_mulvnx1qi_scalar (TARGET_VECTOR)
#define HAVE_pred_addvnx2qi_scalar (TARGET_VECTOR)
#define HAVE_pred_andvnx2qi_scalar (TARGET_VECTOR)
#define HAVE_pred_iorvnx2qi_scalar (TARGET_VECTOR)
#define HAVE_pred_xorvnx2qi_scalar (TARGET_VECTOR)
#define HAVE_pred_smaxvnx2qi_scalar (TARGET_VECTOR)
#define HAVE_pred_umaxvnx2qi_scalar (TARGET_VECTOR)
#define HAVE_pred_sminvnx2qi_scalar (TARGET_VECTOR)
#define HAVE_pred_uminvnx2qi_scalar (TARGET_VECTOR)
#define HAVE_pred_mulvnx2qi_scalar (TARGET_VECTOR)
#define HAVE_pred_addvnx4qi_scalar (TARGET_VECTOR)
#define HAVE_pred_andvnx4qi_scalar (TARGET_VECTOR)
#define HAVE_pred_iorvnx4qi_scalar (TARGET_VECTOR)
#define HAVE_pred_xorvnx4qi_scalar (TARGET_VECTOR)
#define HAVE_pred_smaxvnx4qi_scalar (TARGET_VECTOR)
#define HAVE_pred_umaxvnx4qi_scalar (TARGET_VECTOR)
#define HAVE_pred_sminvnx4qi_scalar (TARGET_VECTOR)
#define HAVE_pred_uminvnx4qi_scalar (TARGET_VECTOR)
#define HAVE_pred_mulvnx4qi_scalar (TARGET_VECTOR)
#define HAVE_pred_addvnx8qi_scalar (TARGET_VECTOR)
#define HAVE_pred_andvnx8qi_scalar (TARGET_VECTOR)
#define HAVE_pred_iorvnx8qi_scalar (TARGET_VECTOR)
#define HAVE_pred_xorvnx8qi_scalar (TARGET_VECTOR)
#define HAVE_pred_smaxvnx8qi_scalar (TARGET_VECTOR)
#define HAVE_pred_umaxvnx8qi_scalar (TARGET_VECTOR)
#define HAVE_pred_sminvnx8qi_scalar (TARGET_VECTOR)
#define HAVE_pred_uminvnx8qi_scalar (TARGET_VECTOR)
#define HAVE_pred_mulvnx8qi_scalar (TARGET_VECTOR)
#define HAVE_pred_addvnx16qi_scalar (TARGET_VECTOR)
#define HAVE_pred_andvnx16qi_scalar (TARGET_VECTOR)
#define HAVE_pred_iorvnx16qi_scalar (TARGET_VECTOR)
#define HAVE_pred_xorvnx16qi_scalar (TARGET_VECTOR)
#define HAVE_pred_smaxvnx16qi_scalar (TARGET_VECTOR)
#define HAVE_pred_umaxvnx16qi_scalar (TARGET_VECTOR)
#define HAVE_pred_sminvnx16qi_scalar (TARGET_VECTOR)
#define HAVE_pred_uminvnx16qi_scalar (TARGET_VECTOR)
#define HAVE_pred_mulvnx16qi_scalar (TARGET_VECTOR)
#define HAVE_pred_addvnx32qi_scalar (TARGET_VECTOR)
#define HAVE_pred_andvnx32qi_scalar (TARGET_VECTOR)
#define HAVE_pred_iorvnx32qi_scalar (TARGET_VECTOR)
#define HAVE_pred_xorvnx32qi_scalar (TARGET_VECTOR)
#define HAVE_pred_smaxvnx32qi_scalar (TARGET_VECTOR)
#define HAVE_pred_umaxvnx32qi_scalar (TARGET_VECTOR)
#define HAVE_pred_sminvnx32qi_scalar (TARGET_VECTOR)
#define HAVE_pred_uminvnx32qi_scalar (TARGET_VECTOR)
#define HAVE_pred_mulvnx32qi_scalar (TARGET_VECTOR)
#define HAVE_pred_addvnx64qi_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_andvnx64qi_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_iorvnx64qi_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_xorvnx64qi_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_smaxvnx64qi_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_umaxvnx64qi_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_sminvnx64qi_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_uminvnx64qi_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_mulvnx64qi_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_addvnx1hi_scalar (TARGET_VECTOR)
#define HAVE_pred_andvnx1hi_scalar (TARGET_VECTOR)
#define HAVE_pred_iorvnx1hi_scalar (TARGET_VECTOR)
#define HAVE_pred_xorvnx1hi_scalar (TARGET_VECTOR)
#define HAVE_pred_smaxvnx1hi_scalar (TARGET_VECTOR)
#define HAVE_pred_umaxvnx1hi_scalar (TARGET_VECTOR)
#define HAVE_pred_sminvnx1hi_scalar (TARGET_VECTOR)
#define HAVE_pred_uminvnx1hi_scalar (TARGET_VECTOR)
#define HAVE_pred_mulvnx1hi_scalar (TARGET_VECTOR)
#define HAVE_pred_addvnx2hi_scalar (TARGET_VECTOR)
#define HAVE_pred_andvnx2hi_scalar (TARGET_VECTOR)
#define HAVE_pred_iorvnx2hi_scalar (TARGET_VECTOR)
#define HAVE_pred_xorvnx2hi_scalar (TARGET_VECTOR)
#define HAVE_pred_smaxvnx2hi_scalar (TARGET_VECTOR)
#define HAVE_pred_umaxvnx2hi_scalar (TARGET_VECTOR)
#define HAVE_pred_sminvnx2hi_scalar (TARGET_VECTOR)
#define HAVE_pred_uminvnx2hi_scalar (TARGET_VECTOR)
#define HAVE_pred_mulvnx2hi_scalar (TARGET_VECTOR)
#define HAVE_pred_addvnx4hi_scalar (TARGET_VECTOR)
#define HAVE_pred_andvnx4hi_scalar (TARGET_VECTOR)
#define HAVE_pred_iorvnx4hi_scalar (TARGET_VECTOR)
#define HAVE_pred_xorvnx4hi_scalar (TARGET_VECTOR)
#define HAVE_pred_smaxvnx4hi_scalar (TARGET_VECTOR)
#define HAVE_pred_umaxvnx4hi_scalar (TARGET_VECTOR)
#define HAVE_pred_sminvnx4hi_scalar (TARGET_VECTOR)
#define HAVE_pred_uminvnx4hi_scalar (TARGET_VECTOR)
#define HAVE_pred_mulvnx4hi_scalar (TARGET_VECTOR)
#define HAVE_pred_addvnx8hi_scalar (TARGET_VECTOR)
#define HAVE_pred_andvnx8hi_scalar (TARGET_VECTOR)
#define HAVE_pred_iorvnx8hi_scalar (TARGET_VECTOR)
#define HAVE_pred_xorvnx8hi_scalar (TARGET_VECTOR)
#define HAVE_pred_smaxvnx8hi_scalar (TARGET_VECTOR)
#define HAVE_pred_umaxvnx8hi_scalar (TARGET_VECTOR)
#define HAVE_pred_sminvnx8hi_scalar (TARGET_VECTOR)
#define HAVE_pred_uminvnx8hi_scalar (TARGET_VECTOR)
#define HAVE_pred_mulvnx8hi_scalar (TARGET_VECTOR)
#define HAVE_pred_addvnx16hi_scalar (TARGET_VECTOR)
#define HAVE_pred_andvnx16hi_scalar (TARGET_VECTOR)
#define HAVE_pred_iorvnx16hi_scalar (TARGET_VECTOR)
#define HAVE_pred_xorvnx16hi_scalar (TARGET_VECTOR)
#define HAVE_pred_smaxvnx16hi_scalar (TARGET_VECTOR)
#define HAVE_pred_umaxvnx16hi_scalar (TARGET_VECTOR)
#define HAVE_pred_sminvnx16hi_scalar (TARGET_VECTOR)
#define HAVE_pred_uminvnx16hi_scalar (TARGET_VECTOR)
#define HAVE_pred_mulvnx16hi_scalar (TARGET_VECTOR)
#define HAVE_pred_addvnx32hi_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_andvnx32hi_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_iorvnx32hi_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_xorvnx32hi_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_smaxvnx32hi_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_umaxvnx32hi_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_sminvnx32hi_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_uminvnx32hi_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_mulvnx32hi_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_addvnx1si_scalar (TARGET_VECTOR)
#define HAVE_pred_andvnx1si_scalar (TARGET_VECTOR)
#define HAVE_pred_iorvnx1si_scalar (TARGET_VECTOR)
#define HAVE_pred_xorvnx1si_scalar (TARGET_VECTOR)
#define HAVE_pred_smaxvnx1si_scalar (TARGET_VECTOR)
#define HAVE_pred_umaxvnx1si_scalar (TARGET_VECTOR)
#define HAVE_pred_sminvnx1si_scalar (TARGET_VECTOR)
#define HAVE_pred_uminvnx1si_scalar (TARGET_VECTOR)
#define HAVE_pred_mulvnx1si_scalar (TARGET_VECTOR)
#define HAVE_pred_addvnx2si_scalar (TARGET_VECTOR)
#define HAVE_pred_andvnx2si_scalar (TARGET_VECTOR)
#define HAVE_pred_iorvnx2si_scalar (TARGET_VECTOR)
#define HAVE_pred_xorvnx2si_scalar (TARGET_VECTOR)
#define HAVE_pred_smaxvnx2si_scalar (TARGET_VECTOR)
#define HAVE_pred_umaxvnx2si_scalar (TARGET_VECTOR)
#define HAVE_pred_sminvnx2si_scalar (TARGET_VECTOR)
#define HAVE_pred_uminvnx2si_scalar (TARGET_VECTOR)
#define HAVE_pred_mulvnx2si_scalar (TARGET_VECTOR)
#define HAVE_pred_addvnx4si_scalar (TARGET_VECTOR)
#define HAVE_pred_andvnx4si_scalar (TARGET_VECTOR)
#define HAVE_pred_iorvnx4si_scalar (TARGET_VECTOR)
#define HAVE_pred_xorvnx4si_scalar (TARGET_VECTOR)
#define HAVE_pred_smaxvnx4si_scalar (TARGET_VECTOR)
#define HAVE_pred_umaxvnx4si_scalar (TARGET_VECTOR)
#define HAVE_pred_sminvnx4si_scalar (TARGET_VECTOR)
#define HAVE_pred_uminvnx4si_scalar (TARGET_VECTOR)
#define HAVE_pred_mulvnx4si_scalar (TARGET_VECTOR)
#define HAVE_pred_addvnx8si_scalar (TARGET_VECTOR)
#define HAVE_pred_andvnx8si_scalar (TARGET_VECTOR)
#define HAVE_pred_iorvnx8si_scalar (TARGET_VECTOR)
#define HAVE_pred_xorvnx8si_scalar (TARGET_VECTOR)
#define HAVE_pred_smaxvnx8si_scalar (TARGET_VECTOR)
#define HAVE_pred_umaxvnx8si_scalar (TARGET_VECTOR)
#define HAVE_pred_sminvnx8si_scalar (TARGET_VECTOR)
#define HAVE_pred_uminvnx8si_scalar (TARGET_VECTOR)
#define HAVE_pred_mulvnx8si_scalar (TARGET_VECTOR)
#define HAVE_pred_addvnx16si_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_andvnx16si_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_iorvnx16si_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_xorvnx16si_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_smaxvnx16si_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_umaxvnx16si_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_sminvnx16si_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_uminvnx16si_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_mulvnx16si_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_subvnx1qi_scalar (TARGET_VECTOR)
#define HAVE_pred_divvnx1qi_scalar (TARGET_VECTOR)
#define HAVE_pred_udivvnx1qi_scalar (TARGET_VECTOR)
#define HAVE_pred_modvnx1qi_scalar (TARGET_VECTOR)
#define HAVE_pred_umodvnx1qi_scalar (TARGET_VECTOR)
#define HAVE_pred_subvnx2qi_scalar (TARGET_VECTOR)
#define HAVE_pred_divvnx2qi_scalar (TARGET_VECTOR)
#define HAVE_pred_udivvnx2qi_scalar (TARGET_VECTOR)
#define HAVE_pred_modvnx2qi_scalar (TARGET_VECTOR)
#define HAVE_pred_umodvnx2qi_scalar (TARGET_VECTOR)
#define HAVE_pred_subvnx4qi_scalar (TARGET_VECTOR)
#define HAVE_pred_divvnx4qi_scalar (TARGET_VECTOR)
#define HAVE_pred_udivvnx4qi_scalar (TARGET_VECTOR)
#define HAVE_pred_modvnx4qi_scalar (TARGET_VECTOR)
#define HAVE_pred_umodvnx4qi_scalar (TARGET_VECTOR)
#define HAVE_pred_subvnx8qi_scalar (TARGET_VECTOR)
#define HAVE_pred_divvnx8qi_scalar (TARGET_VECTOR)
#define HAVE_pred_udivvnx8qi_scalar (TARGET_VECTOR)
#define HAVE_pred_modvnx8qi_scalar (TARGET_VECTOR)
#define HAVE_pred_umodvnx8qi_scalar (TARGET_VECTOR)
#define HAVE_pred_subvnx16qi_scalar (TARGET_VECTOR)
#define HAVE_pred_divvnx16qi_scalar (TARGET_VECTOR)
#define HAVE_pred_udivvnx16qi_scalar (TARGET_VECTOR)
#define HAVE_pred_modvnx16qi_scalar (TARGET_VECTOR)
#define HAVE_pred_umodvnx16qi_scalar (TARGET_VECTOR)
#define HAVE_pred_subvnx32qi_scalar (TARGET_VECTOR)
#define HAVE_pred_divvnx32qi_scalar (TARGET_VECTOR)
#define HAVE_pred_udivvnx32qi_scalar (TARGET_VECTOR)
#define HAVE_pred_modvnx32qi_scalar (TARGET_VECTOR)
#define HAVE_pred_umodvnx32qi_scalar (TARGET_VECTOR)
#define HAVE_pred_subvnx64qi_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_divvnx64qi_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_udivvnx64qi_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_modvnx64qi_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_umodvnx64qi_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_subvnx1hi_scalar (TARGET_VECTOR)
#define HAVE_pred_divvnx1hi_scalar (TARGET_VECTOR)
#define HAVE_pred_udivvnx1hi_scalar (TARGET_VECTOR)
#define HAVE_pred_modvnx1hi_scalar (TARGET_VECTOR)
#define HAVE_pred_umodvnx1hi_scalar (TARGET_VECTOR)
#define HAVE_pred_subvnx2hi_scalar (TARGET_VECTOR)
#define HAVE_pred_divvnx2hi_scalar (TARGET_VECTOR)
#define HAVE_pred_udivvnx2hi_scalar (TARGET_VECTOR)
#define HAVE_pred_modvnx2hi_scalar (TARGET_VECTOR)
#define HAVE_pred_umodvnx2hi_scalar (TARGET_VECTOR)
#define HAVE_pred_subvnx4hi_scalar (TARGET_VECTOR)
#define HAVE_pred_divvnx4hi_scalar (TARGET_VECTOR)
#define HAVE_pred_udivvnx4hi_scalar (TARGET_VECTOR)
#define HAVE_pred_modvnx4hi_scalar (TARGET_VECTOR)
#define HAVE_pred_umodvnx4hi_scalar (TARGET_VECTOR)
#define HAVE_pred_subvnx8hi_scalar (TARGET_VECTOR)
#define HAVE_pred_divvnx8hi_scalar (TARGET_VECTOR)
#define HAVE_pred_udivvnx8hi_scalar (TARGET_VECTOR)
#define HAVE_pred_modvnx8hi_scalar (TARGET_VECTOR)
#define HAVE_pred_umodvnx8hi_scalar (TARGET_VECTOR)
#define HAVE_pred_subvnx16hi_scalar (TARGET_VECTOR)
#define HAVE_pred_divvnx16hi_scalar (TARGET_VECTOR)
#define HAVE_pred_udivvnx16hi_scalar (TARGET_VECTOR)
#define HAVE_pred_modvnx16hi_scalar (TARGET_VECTOR)
#define HAVE_pred_umodvnx16hi_scalar (TARGET_VECTOR)
#define HAVE_pred_subvnx32hi_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_divvnx32hi_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_udivvnx32hi_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_modvnx32hi_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_umodvnx32hi_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_subvnx1si_scalar (TARGET_VECTOR)
#define HAVE_pred_divvnx1si_scalar (TARGET_VECTOR)
#define HAVE_pred_udivvnx1si_scalar (TARGET_VECTOR)
#define HAVE_pred_modvnx1si_scalar (TARGET_VECTOR)
#define HAVE_pred_umodvnx1si_scalar (TARGET_VECTOR)
#define HAVE_pred_subvnx2si_scalar (TARGET_VECTOR)
#define HAVE_pred_divvnx2si_scalar (TARGET_VECTOR)
#define HAVE_pred_udivvnx2si_scalar (TARGET_VECTOR)
#define HAVE_pred_modvnx2si_scalar (TARGET_VECTOR)
#define HAVE_pred_umodvnx2si_scalar (TARGET_VECTOR)
#define HAVE_pred_subvnx4si_scalar (TARGET_VECTOR)
#define HAVE_pred_divvnx4si_scalar (TARGET_VECTOR)
#define HAVE_pred_udivvnx4si_scalar (TARGET_VECTOR)
#define HAVE_pred_modvnx4si_scalar (TARGET_VECTOR)
#define HAVE_pred_umodvnx4si_scalar (TARGET_VECTOR)
#define HAVE_pred_subvnx8si_scalar (TARGET_VECTOR)
#define HAVE_pred_divvnx8si_scalar (TARGET_VECTOR)
#define HAVE_pred_udivvnx8si_scalar (TARGET_VECTOR)
#define HAVE_pred_modvnx8si_scalar (TARGET_VECTOR)
#define HAVE_pred_umodvnx8si_scalar (TARGET_VECTOR)
#define HAVE_pred_subvnx16si_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_divvnx16si_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_udivvnx16si_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_modvnx16si_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_umodvnx16si_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_subvnx1qi_reverse_scalar (TARGET_VECTOR)
#define HAVE_pred_subvnx2qi_reverse_scalar (TARGET_VECTOR)
#define HAVE_pred_subvnx4qi_reverse_scalar (TARGET_VECTOR)
#define HAVE_pred_subvnx8qi_reverse_scalar (TARGET_VECTOR)
#define HAVE_pred_subvnx16qi_reverse_scalar (TARGET_VECTOR)
#define HAVE_pred_subvnx32qi_reverse_scalar (TARGET_VECTOR)
#define HAVE_pred_subvnx64qi_reverse_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_subvnx1hi_reverse_scalar (TARGET_VECTOR)
#define HAVE_pred_subvnx2hi_reverse_scalar (TARGET_VECTOR)
#define HAVE_pred_subvnx4hi_reverse_scalar (TARGET_VECTOR)
#define HAVE_pred_subvnx8hi_reverse_scalar (TARGET_VECTOR)
#define HAVE_pred_subvnx16hi_reverse_scalar (TARGET_VECTOR)
#define HAVE_pred_subvnx32hi_reverse_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_subvnx1si_reverse_scalar (TARGET_VECTOR)
#define HAVE_pred_subvnx2si_reverse_scalar (TARGET_VECTOR)
#define HAVE_pred_subvnx4si_reverse_scalar (TARGET_VECTOR)
#define HAVE_pred_subvnx8si_reverse_scalar (TARGET_VECTOR)
#define HAVE_pred_subvnx16si_reverse_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_mulhvnx1qi (TARGET_VECTOR)
#define HAVE_pred_mulhuvnx1qi (TARGET_VECTOR)
#define HAVE_pred_mulhsuvnx1qi (TARGET_VECTOR)
#define HAVE_pred_mulhvnx2qi (TARGET_VECTOR)
#define HAVE_pred_mulhuvnx2qi (TARGET_VECTOR)
#define HAVE_pred_mulhsuvnx2qi (TARGET_VECTOR)
#define HAVE_pred_mulhvnx4qi (TARGET_VECTOR)
#define HAVE_pred_mulhuvnx4qi (TARGET_VECTOR)
#define HAVE_pred_mulhsuvnx4qi (TARGET_VECTOR)
#define HAVE_pred_mulhvnx8qi (TARGET_VECTOR)
#define HAVE_pred_mulhuvnx8qi (TARGET_VECTOR)
#define HAVE_pred_mulhsuvnx8qi (TARGET_VECTOR)
#define HAVE_pred_mulhvnx16qi (TARGET_VECTOR)
#define HAVE_pred_mulhuvnx16qi (TARGET_VECTOR)
#define HAVE_pred_mulhsuvnx16qi (TARGET_VECTOR)
#define HAVE_pred_mulhvnx32qi (TARGET_VECTOR)
#define HAVE_pred_mulhuvnx32qi (TARGET_VECTOR)
#define HAVE_pred_mulhsuvnx32qi (TARGET_VECTOR)
#define HAVE_pred_mulhvnx64qi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_mulhuvnx64qi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_mulhsuvnx64qi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_mulhvnx1hi (TARGET_VECTOR)
#define HAVE_pred_mulhuvnx1hi (TARGET_VECTOR)
#define HAVE_pred_mulhsuvnx1hi (TARGET_VECTOR)
#define HAVE_pred_mulhvnx2hi (TARGET_VECTOR)
#define HAVE_pred_mulhuvnx2hi (TARGET_VECTOR)
#define HAVE_pred_mulhsuvnx2hi (TARGET_VECTOR)
#define HAVE_pred_mulhvnx4hi (TARGET_VECTOR)
#define HAVE_pred_mulhuvnx4hi (TARGET_VECTOR)
#define HAVE_pred_mulhsuvnx4hi (TARGET_VECTOR)
#define HAVE_pred_mulhvnx8hi (TARGET_VECTOR)
#define HAVE_pred_mulhuvnx8hi (TARGET_VECTOR)
#define HAVE_pred_mulhsuvnx8hi (TARGET_VECTOR)
#define HAVE_pred_mulhvnx16hi (TARGET_VECTOR)
#define HAVE_pred_mulhuvnx16hi (TARGET_VECTOR)
#define HAVE_pred_mulhsuvnx16hi (TARGET_VECTOR)
#define HAVE_pred_mulhvnx32hi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_mulhuvnx32hi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_mulhsuvnx32hi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_mulhvnx1si (TARGET_VECTOR)
#define HAVE_pred_mulhuvnx1si (TARGET_VECTOR)
#define HAVE_pred_mulhsuvnx1si (TARGET_VECTOR)
#define HAVE_pred_mulhvnx2si (TARGET_VECTOR)
#define HAVE_pred_mulhuvnx2si (TARGET_VECTOR)
#define HAVE_pred_mulhsuvnx2si (TARGET_VECTOR)
#define HAVE_pred_mulhvnx4si (TARGET_VECTOR)
#define HAVE_pred_mulhuvnx4si (TARGET_VECTOR)
#define HAVE_pred_mulhsuvnx4si (TARGET_VECTOR)
#define HAVE_pred_mulhvnx8si (TARGET_VECTOR)
#define HAVE_pred_mulhuvnx8si (TARGET_VECTOR)
#define HAVE_pred_mulhsuvnx8si (TARGET_VECTOR)
#define HAVE_pred_mulhvnx16si ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_mulhuvnx16si ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_mulhsuvnx16si ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_mulhvnx1di ((TARGET_VECTOR) && (TARGET_FULL_V))
#define HAVE_pred_mulhuvnx1di ((TARGET_VECTOR) && (TARGET_FULL_V))
#define HAVE_pred_mulhsuvnx1di ((TARGET_VECTOR) && (TARGET_FULL_V))
#define HAVE_pred_mulhvnx2di ((TARGET_VECTOR) && (TARGET_FULL_V))
#define HAVE_pred_mulhuvnx2di ((TARGET_VECTOR) && (TARGET_FULL_V))
#define HAVE_pred_mulhsuvnx2di ((TARGET_VECTOR) && (TARGET_FULL_V))
#define HAVE_pred_mulhvnx4di ((TARGET_VECTOR) && (TARGET_FULL_V))
#define HAVE_pred_mulhuvnx4di ((TARGET_VECTOR) && (TARGET_FULL_V))
#define HAVE_pred_mulhsuvnx4di ((TARGET_VECTOR) && (TARGET_FULL_V))
#define HAVE_pred_mulhvnx8di ((TARGET_VECTOR) && (TARGET_FULL_V))
#define HAVE_pred_mulhuvnx8di ((TARGET_VECTOR) && (TARGET_FULL_V))
#define HAVE_pred_mulhsuvnx8di ((TARGET_VECTOR) && (TARGET_FULL_V))
#define HAVE_pred_mulhvnx1qi_scalar (TARGET_VECTOR)
#define HAVE_pred_mulhuvnx1qi_scalar (TARGET_VECTOR)
#define HAVE_pred_mulhsuvnx1qi_scalar (TARGET_VECTOR)
#define HAVE_pred_mulhvnx2qi_scalar (TARGET_VECTOR)
#define HAVE_pred_mulhuvnx2qi_scalar (TARGET_VECTOR)
#define HAVE_pred_mulhsuvnx2qi_scalar (TARGET_VECTOR)
#define HAVE_pred_mulhvnx4qi_scalar (TARGET_VECTOR)
#define HAVE_pred_mulhuvnx4qi_scalar (TARGET_VECTOR)
#define HAVE_pred_mulhsuvnx4qi_scalar (TARGET_VECTOR)
#define HAVE_pred_mulhvnx8qi_scalar (TARGET_VECTOR)
#define HAVE_pred_mulhuvnx8qi_scalar (TARGET_VECTOR)
#define HAVE_pred_mulhsuvnx8qi_scalar (TARGET_VECTOR)
#define HAVE_pred_mulhvnx16qi_scalar (TARGET_VECTOR)
#define HAVE_pred_mulhuvnx16qi_scalar (TARGET_VECTOR)
#define HAVE_pred_mulhsuvnx16qi_scalar (TARGET_VECTOR)
#define HAVE_pred_mulhvnx32qi_scalar (TARGET_VECTOR)
#define HAVE_pred_mulhuvnx32qi_scalar (TARGET_VECTOR)
#define HAVE_pred_mulhsuvnx32qi_scalar (TARGET_VECTOR)
#define HAVE_pred_mulhvnx64qi_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_mulhuvnx64qi_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_mulhsuvnx64qi_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_mulhvnx1hi_scalar (TARGET_VECTOR)
#define HAVE_pred_mulhuvnx1hi_scalar (TARGET_VECTOR)
#define HAVE_pred_mulhsuvnx1hi_scalar (TARGET_VECTOR)
#define HAVE_pred_mulhvnx2hi_scalar (TARGET_VECTOR)
#define HAVE_pred_mulhuvnx2hi_scalar (TARGET_VECTOR)
#define HAVE_pred_mulhsuvnx2hi_scalar (TARGET_VECTOR)
#define HAVE_pred_mulhvnx4hi_scalar (TARGET_VECTOR)
#define HAVE_pred_mulhuvnx4hi_scalar (TARGET_VECTOR)
#define HAVE_pred_mulhsuvnx4hi_scalar (TARGET_VECTOR)
#define HAVE_pred_mulhvnx8hi_scalar (TARGET_VECTOR)
#define HAVE_pred_mulhuvnx8hi_scalar (TARGET_VECTOR)
#define HAVE_pred_mulhsuvnx8hi_scalar (TARGET_VECTOR)
#define HAVE_pred_mulhvnx16hi_scalar (TARGET_VECTOR)
#define HAVE_pred_mulhuvnx16hi_scalar (TARGET_VECTOR)
#define HAVE_pred_mulhsuvnx16hi_scalar (TARGET_VECTOR)
#define HAVE_pred_mulhvnx32hi_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_mulhuvnx32hi_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_mulhsuvnx32hi_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_mulhvnx1si_scalar (TARGET_VECTOR)
#define HAVE_pred_mulhuvnx1si_scalar (TARGET_VECTOR)
#define HAVE_pred_mulhsuvnx1si_scalar (TARGET_VECTOR)
#define HAVE_pred_mulhvnx2si_scalar (TARGET_VECTOR)
#define HAVE_pred_mulhuvnx2si_scalar (TARGET_VECTOR)
#define HAVE_pred_mulhsuvnx2si_scalar (TARGET_VECTOR)
#define HAVE_pred_mulhvnx4si_scalar (TARGET_VECTOR)
#define HAVE_pred_mulhuvnx4si_scalar (TARGET_VECTOR)
#define HAVE_pred_mulhsuvnx4si_scalar (TARGET_VECTOR)
#define HAVE_pred_mulhvnx8si_scalar (TARGET_VECTOR)
#define HAVE_pred_mulhuvnx8si_scalar (TARGET_VECTOR)
#define HAVE_pred_mulhsuvnx8si_scalar (TARGET_VECTOR)
#define HAVE_pred_mulhvnx16si_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_mulhuvnx16si_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_mulhsuvnx16si_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_adcvnx1qi (TARGET_VECTOR)
#define HAVE_pred_adcvnx2qi (TARGET_VECTOR)
#define HAVE_pred_adcvnx4qi (TARGET_VECTOR)
#define HAVE_pred_adcvnx8qi (TARGET_VECTOR)
#define HAVE_pred_adcvnx16qi (TARGET_VECTOR)
#define HAVE_pred_adcvnx32qi (TARGET_VECTOR)
#define HAVE_pred_adcvnx64qi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_adcvnx1hi (TARGET_VECTOR)
#define HAVE_pred_adcvnx2hi (TARGET_VECTOR)
#define HAVE_pred_adcvnx4hi (TARGET_VECTOR)
#define HAVE_pred_adcvnx8hi (TARGET_VECTOR)
#define HAVE_pred_adcvnx16hi (TARGET_VECTOR)
#define HAVE_pred_adcvnx32hi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_adcvnx1si (TARGET_VECTOR)
#define HAVE_pred_adcvnx2si (TARGET_VECTOR)
#define HAVE_pred_adcvnx4si (TARGET_VECTOR)
#define HAVE_pred_adcvnx8si (TARGET_VECTOR)
#define HAVE_pred_adcvnx16si ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_adcvnx1di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_adcvnx2di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_adcvnx4di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_adcvnx8di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_sbcvnx1qi (TARGET_VECTOR)
#define HAVE_pred_sbcvnx2qi (TARGET_VECTOR)
#define HAVE_pred_sbcvnx4qi (TARGET_VECTOR)
#define HAVE_pred_sbcvnx8qi (TARGET_VECTOR)
#define HAVE_pred_sbcvnx16qi (TARGET_VECTOR)
#define HAVE_pred_sbcvnx32qi (TARGET_VECTOR)
#define HAVE_pred_sbcvnx64qi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_sbcvnx1hi (TARGET_VECTOR)
#define HAVE_pred_sbcvnx2hi (TARGET_VECTOR)
#define HAVE_pred_sbcvnx4hi (TARGET_VECTOR)
#define HAVE_pred_sbcvnx8hi (TARGET_VECTOR)
#define HAVE_pred_sbcvnx16hi (TARGET_VECTOR)
#define HAVE_pred_sbcvnx32hi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_sbcvnx1si (TARGET_VECTOR)
#define HAVE_pred_sbcvnx2si (TARGET_VECTOR)
#define HAVE_pred_sbcvnx4si (TARGET_VECTOR)
#define HAVE_pred_sbcvnx8si (TARGET_VECTOR)
#define HAVE_pred_sbcvnx16si ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_sbcvnx1di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_sbcvnx2di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_sbcvnx4di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_sbcvnx8di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_adcvnx1qi_scalar (TARGET_VECTOR)
#define HAVE_pred_adcvnx2qi_scalar (TARGET_VECTOR)
#define HAVE_pred_adcvnx4qi_scalar (TARGET_VECTOR)
#define HAVE_pred_adcvnx8qi_scalar (TARGET_VECTOR)
#define HAVE_pred_adcvnx16qi_scalar (TARGET_VECTOR)
#define HAVE_pred_adcvnx32qi_scalar (TARGET_VECTOR)
#define HAVE_pred_adcvnx64qi_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_adcvnx1hi_scalar (TARGET_VECTOR)
#define HAVE_pred_adcvnx2hi_scalar (TARGET_VECTOR)
#define HAVE_pred_adcvnx4hi_scalar (TARGET_VECTOR)
#define HAVE_pred_adcvnx8hi_scalar (TARGET_VECTOR)
#define HAVE_pred_adcvnx16hi_scalar (TARGET_VECTOR)
#define HAVE_pred_adcvnx32hi_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_adcvnx1si_scalar (TARGET_VECTOR)
#define HAVE_pred_adcvnx2si_scalar (TARGET_VECTOR)
#define HAVE_pred_adcvnx4si_scalar (TARGET_VECTOR)
#define HAVE_pred_adcvnx8si_scalar (TARGET_VECTOR)
#define HAVE_pred_adcvnx16si_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_sbcvnx1qi_scalar (TARGET_VECTOR)
#define HAVE_pred_sbcvnx2qi_scalar (TARGET_VECTOR)
#define HAVE_pred_sbcvnx4qi_scalar (TARGET_VECTOR)
#define HAVE_pred_sbcvnx8qi_scalar (TARGET_VECTOR)
#define HAVE_pred_sbcvnx16qi_scalar (TARGET_VECTOR)
#define HAVE_pred_sbcvnx32qi_scalar (TARGET_VECTOR)
#define HAVE_pred_sbcvnx64qi_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_sbcvnx1hi_scalar (TARGET_VECTOR)
#define HAVE_pred_sbcvnx2hi_scalar (TARGET_VECTOR)
#define HAVE_pred_sbcvnx4hi_scalar (TARGET_VECTOR)
#define HAVE_pred_sbcvnx8hi_scalar (TARGET_VECTOR)
#define HAVE_pred_sbcvnx16hi_scalar (TARGET_VECTOR)
#define HAVE_pred_sbcvnx32hi_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_sbcvnx1si_scalar (TARGET_VECTOR)
#define HAVE_pred_sbcvnx2si_scalar (TARGET_VECTOR)
#define HAVE_pred_sbcvnx4si_scalar (TARGET_VECTOR)
#define HAVE_pred_sbcvnx8si_scalar (TARGET_VECTOR)
#define HAVE_pred_sbcvnx16si_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_madcvnx1qi (TARGET_VECTOR)
#define HAVE_pred_madcvnx2qi (TARGET_VECTOR)
#define HAVE_pred_madcvnx4qi (TARGET_VECTOR)
#define HAVE_pred_madcvnx8qi (TARGET_VECTOR)
#define HAVE_pred_madcvnx16qi (TARGET_VECTOR)
#define HAVE_pred_madcvnx32qi (TARGET_VECTOR)
#define HAVE_pred_madcvnx64qi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_madcvnx1hi (TARGET_VECTOR)
#define HAVE_pred_madcvnx2hi (TARGET_VECTOR)
#define HAVE_pred_madcvnx4hi (TARGET_VECTOR)
#define HAVE_pred_madcvnx8hi (TARGET_VECTOR)
#define HAVE_pred_madcvnx16hi (TARGET_VECTOR)
#define HAVE_pred_madcvnx32hi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_madcvnx1si (TARGET_VECTOR)
#define HAVE_pred_madcvnx2si (TARGET_VECTOR)
#define HAVE_pred_madcvnx4si (TARGET_VECTOR)
#define HAVE_pred_madcvnx8si (TARGET_VECTOR)
#define HAVE_pred_madcvnx16si ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_madcvnx1di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_madcvnx2di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_madcvnx4di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_madcvnx8di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_msbcvnx1qi (TARGET_VECTOR)
#define HAVE_pred_msbcvnx2qi (TARGET_VECTOR)
#define HAVE_pred_msbcvnx4qi (TARGET_VECTOR)
#define HAVE_pred_msbcvnx8qi (TARGET_VECTOR)
#define HAVE_pred_msbcvnx16qi (TARGET_VECTOR)
#define HAVE_pred_msbcvnx32qi (TARGET_VECTOR)
#define HAVE_pred_msbcvnx64qi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_msbcvnx1hi (TARGET_VECTOR)
#define HAVE_pred_msbcvnx2hi (TARGET_VECTOR)
#define HAVE_pred_msbcvnx4hi (TARGET_VECTOR)
#define HAVE_pred_msbcvnx8hi (TARGET_VECTOR)
#define HAVE_pred_msbcvnx16hi (TARGET_VECTOR)
#define HAVE_pred_msbcvnx32hi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_msbcvnx1si (TARGET_VECTOR)
#define HAVE_pred_msbcvnx2si (TARGET_VECTOR)
#define HAVE_pred_msbcvnx4si (TARGET_VECTOR)
#define HAVE_pred_msbcvnx8si (TARGET_VECTOR)
#define HAVE_pred_msbcvnx16si ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_msbcvnx1di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_msbcvnx2di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_msbcvnx4di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_msbcvnx8di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_madcvnx1qi_scalar (TARGET_VECTOR)
#define HAVE_pred_madcvnx2qi_scalar (TARGET_VECTOR)
#define HAVE_pred_madcvnx4qi_scalar (TARGET_VECTOR)
#define HAVE_pred_madcvnx8qi_scalar (TARGET_VECTOR)
#define HAVE_pred_madcvnx16qi_scalar (TARGET_VECTOR)
#define HAVE_pred_madcvnx32qi_scalar (TARGET_VECTOR)
#define HAVE_pred_madcvnx64qi_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_madcvnx1hi_scalar (TARGET_VECTOR)
#define HAVE_pred_madcvnx2hi_scalar (TARGET_VECTOR)
#define HAVE_pred_madcvnx4hi_scalar (TARGET_VECTOR)
#define HAVE_pred_madcvnx8hi_scalar (TARGET_VECTOR)
#define HAVE_pred_madcvnx16hi_scalar (TARGET_VECTOR)
#define HAVE_pred_madcvnx32hi_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_madcvnx1si_scalar (TARGET_VECTOR)
#define HAVE_pred_madcvnx2si_scalar (TARGET_VECTOR)
#define HAVE_pred_madcvnx4si_scalar (TARGET_VECTOR)
#define HAVE_pred_madcvnx8si_scalar (TARGET_VECTOR)
#define HAVE_pred_madcvnx16si_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_msbcvnx1qi_scalar (TARGET_VECTOR)
#define HAVE_pred_msbcvnx2qi_scalar (TARGET_VECTOR)
#define HAVE_pred_msbcvnx4qi_scalar (TARGET_VECTOR)
#define HAVE_pred_msbcvnx8qi_scalar (TARGET_VECTOR)
#define HAVE_pred_msbcvnx16qi_scalar (TARGET_VECTOR)
#define HAVE_pred_msbcvnx32qi_scalar (TARGET_VECTOR)
#define HAVE_pred_msbcvnx64qi_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_msbcvnx1hi_scalar (TARGET_VECTOR)
#define HAVE_pred_msbcvnx2hi_scalar (TARGET_VECTOR)
#define HAVE_pred_msbcvnx4hi_scalar (TARGET_VECTOR)
#define HAVE_pred_msbcvnx8hi_scalar (TARGET_VECTOR)
#define HAVE_pred_msbcvnx16hi_scalar (TARGET_VECTOR)
#define HAVE_pred_msbcvnx32hi_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_msbcvnx1si_scalar (TARGET_VECTOR)
#define HAVE_pred_msbcvnx2si_scalar (TARGET_VECTOR)
#define HAVE_pred_msbcvnx4si_scalar (TARGET_VECTOR)
#define HAVE_pred_msbcvnx8si_scalar (TARGET_VECTOR)
#define HAVE_pred_msbcvnx16si_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_madcvnx1qi_overflow (TARGET_VECTOR)
#define HAVE_pred_madcvnx2qi_overflow (TARGET_VECTOR)
#define HAVE_pred_madcvnx4qi_overflow (TARGET_VECTOR)
#define HAVE_pred_madcvnx8qi_overflow (TARGET_VECTOR)
#define HAVE_pred_madcvnx16qi_overflow (TARGET_VECTOR)
#define HAVE_pred_madcvnx32qi_overflow (TARGET_VECTOR)
#define HAVE_pred_madcvnx64qi_overflow ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_madcvnx1hi_overflow (TARGET_VECTOR)
#define HAVE_pred_madcvnx2hi_overflow (TARGET_VECTOR)
#define HAVE_pred_madcvnx4hi_overflow (TARGET_VECTOR)
#define HAVE_pred_madcvnx8hi_overflow (TARGET_VECTOR)
#define HAVE_pred_madcvnx16hi_overflow (TARGET_VECTOR)
#define HAVE_pred_madcvnx32hi_overflow ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_madcvnx1si_overflow (TARGET_VECTOR)
#define HAVE_pred_madcvnx2si_overflow (TARGET_VECTOR)
#define HAVE_pred_madcvnx4si_overflow (TARGET_VECTOR)
#define HAVE_pred_madcvnx8si_overflow (TARGET_VECTOR)
#define HAVE_pred_madcvnx16si_overflow ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_madcvnx1di_overflow ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_madcvnx2di_overflow ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_madcvnx4di_overflow ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_madcvnx8di_overflow ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_msbcvnx1qi_overflow (TARGET_VECTOR)
#define HAVE_pred_msbcvnx2qi_overflow (TARGET_VECTOR)
#define HAVE_pred_msbcvnx4qi_overflow (TARGET_VECTOR)
#define HAVE_pred_msbcvnx8qi_overflow (TARGET_VECTOR)
#define HAVE_pred_msbcvnx16qi_overflow (TARGET_VECTOR)
#define HAVE_pred_msbcvnx32qi_overflow (TARGET_VECTOR)
#define HAVE_pred_msbcvnx64qi_overflow ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_msbcvnx1hi_overflow (TARGET_VECTOR)
#define HAVE_pred_msbcvnx2hi_overflow (TARGET_VECTOR)
#define HAVE_pred_msbcvnx4hi_overflow (TARGET_VECTOR)
#define HAVE_pred_msbcvnx8hi_overflow (TARGET_VECTOR)
#define HAVE_pred_msbcvnx16hi_overflow (TARGET_VECTOR)
#define HAVE_pred_msbcvnx32hi_overflow ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_msbcvnx1si_overflow (TARGET_VECTOR)
#define HAVE_pred_msbcvnx2si_overflow (TARGET_VECTOR)
#define HAVE_pred_msbcvnx4si_overflow (TARGET_VECTOR)
#define HAVE_pred_msbcvnx8si_overflow (TARGET_VECTOR)
#define HAVE_pred_msbcvnx16si_overflow ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_msbcvnx1di_overflow ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_msbcvnx2di_overflow ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_msbcvnx4di_overflow ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_msbcvnx8di_overflow ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_madcvnx1qi_overflow_scalar (TARGET_VECTOR)
#define HAVE_pred_madcvnx2qi_overflow_scalar (TARGET_VECTOR)
#define HAVE_pred_madcvnx4qi_overflow_scalar (TARGET_VECTOR)
#define HAVE_pred_madcvnx8qi_overflow_scalar (TARGET_VECTOR)
#define HAVE_pred_madcvnx16qi_overflow_scalar (TARGET_VECTOR)
#define HAVE_pred_madcvnx32qi_overflow_scalar (TARGET_VECTOR)
#define HAVE_pred_madcvnx64qi_overflow_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_madcvnx1hi_overflow_scalar (TARGET_VECTOR)
#define HAVE_pred_madcvnx2hi_overflow_scalar (TARGET_VECTOR)
#define HAVE_pred_madcvnx4hi_overflow_scalar (TARGET_VECTOR)
#define HAVE_pred_madcvnx8hi_overflow_scalar (TARGET_VECTOR)
#define HAVE_pred_madcvnx16hi_overflow_scalar (TARGET_VECTOR)
#define HAVE_pred_madcvnx32hi_overflow_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_madcvnx1si_overflow_scalar (TARGET_VECTOR)
#define HAVE_pred_madcvnx2si_overflow_scalar (TARGET_VECTOR)
#define HAVE_pred_madcvnx4si_overflow_scalar (TARGET_VECTOR)
#define HAVE_pred_madcvnx8si_overflow_scalar (TARGET_VECTOR)
#define HAVE_pred_madcvnx16si_overflow_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_msbcvnx1qi_overflow_scalar (TARGET_VECTOR)
#define HAVE_pred_msbcvnx2qi_overflow_scalar (TARGET_VECTOR)
#define HAVE_pred_msbcvnx4qi_overflow_scalar (TARGET_VECTOR)
#define HAVE_pred_msbcvnx8qi_overflow_scalar (TARGET_VECTOR)
#define HAVE_pred_msbcvnx16qi_overflow_scalar (TARGET_VECTOR)
#define HAVE_pred_msbcvnx32qi_overflow_scalar (TARGET_VECTOR)
#define HAVE_pred_msbcvnx64qi_overflow_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_msbcvnx1hi_overflow_scalar (TARGET_VECTOR)
#define HAVE_pred_msbcvnx2hi_overflow_scalar (TARGET_VECTOR)
#define HAVE_pred_msbcvnx4hi_overflow_scalar (TARGET_VECTOR)
#define HAVE_pred_msbcvnx8hi_overflow_scalar (TARGET_VECTOR)
#define HAVE_pred_msbcvnx16hi_overflow_scalar (TARGET_VECTOR)
#define HAVE_pred_msbcvnx32hi_overflow_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_msbcvnx1si_overflow_scalar (TARGET_VECTOR)
#define HAVE_pred_msbcvnx2si_overflow_scalar (TARGET_VECTOR)
#define HAVE_pred_msbcvnx4si_overflow_scalar (TARGET_VECTOR)
#define HAVE_pred_msbcvnx8si_overflow_scalar (TARGET_VECTOR)
#define HAVE_pred_msbcvnx16si_overflow_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_negvnx1qi (TARGET_VECTOR)
#define HAVE_pred_one_cmplvnx1qi (TARGET_VECTOR)
#define HAVE_pred_negvnx2qi (TARGET_VECTOR)
#define HAVE_pred_one_cmplvnx2qi (TARGET_VECTOR)
#define HAVE_pred_negvnx4qi (TARGET_VECTOR)
#define HAVE_pred_one_cmplvnx4qi (TARGET_VECTOR)
#define HAVE_pred_negvnx8qi (TARGET_VECTOR)
#define HAVE_pred_one_cmplvnx8qi (TARGET_VECTOR)
#define HAVE_pred_negvnx16qi (TARGET_VECTOR)
#define HAVE_pred_one_cmplvnx16qi (TARGET_VECTOR)
#define HAVE_pred_negvnx32qi (TARGET_VECTOR)
#define HAVE_pred_one_cmplvnx32qi (TARGET_VECTOR)
#define HAVE_pred_negvnx64qi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_one_cmplvnx64qi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_negvnx1hi (TARGET_VECTOR)
#define HAVE_pred_one_cmplvnx1hi (TARGET_VECTOR)
#define HAVE_pred_negvnx2hi (TARGET_VECTOR)
#define HAVE_pred_one_cmplvnx2hi (TARGET_VECTOR)
#define HAVE_pred_negvnx4hi (TARGET_VECTOR)
#define HAVE_pred_one_cmplvnx4hi (TARGET_VECTOR)
#define HAVE_pred_negvnx8hi (TARGET_VECTOR)
#define HAVE_pred_one_cmplvnx8hi (TARGET_VECTOR)
#define HAVE_pred_negvnx16hi (TARGET_VECTOR)
#define HAVE_pred_one_cmplvnx16hi (TARGET_VECTOR)
#define HAVE_pred_negvnx32hi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_one_cmplvnx32hi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_negvnx1si (TARGET_VECTOR)
#define HAVE_pred_one_cmplvnx1si (TARGET_VECTOR)
#define HAVE_pred_negvnx2si (TARGET_VECTOR)
#define HAVE_pred_one_cmplvnx2si (TARGET_VECTOR)
#define HAVE_pred_negvnx4si (TARGET_VECTOR)
#define HAVE_pred_one_cmplvnx4si (TARGET_VECTOR)
#define HAVE_pred_negvnx8si (TARGET_VECTOR)
#define HAVE_pred_one_cmplvnx8si (TARGET_VECTOR)
#define HAVE_pred_negvnx16si ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_one_cmplvnx16si ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_negvnx1di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_one_cmplvnx1di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_negvnx2di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_one_cmplvnx2di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_negvnx4di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_one_cmplvnx4di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_negvnx8di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_one_cmplvnx8di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_extendvnx1hi_vf2 (TARGET_VECTOR)
#define HAVE_pred_zero_extendvnx1hi_vf2 (TARGET_VECTOR)
#define HAVE_pred_extendvnx2hi_vf2 (TARGET_VECTOR)
#define HAVE_pred_zero_extendvnx2hi_vf2 (TARGET_VECTOR)
#define HAVE_pred_extendvnx4hi_vf2 (TARGET_VECTOR)
#define HAVE_pred_zero_extendvnx4hi_vf2 (TARGET_VECTOR)
#define HAVE_pred_extendvnx8hi_vf2 (TARGET_VECTOR)
#define HAVE_pred_zero_extendvnx8hi_vf2 (TARGET_VECTOR)
#define HAVE_pred_extendvnx16hi_vf2 (TARGET_VECTOR)
#define HAVE_pred_zero_extendvnx16hi_vf2 (TARGET_VECTOR)
#define HAVE_pred_extendvnx32hi_vf2 ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_zero_extendvnx32hi_vf2 ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_extendvnx1si_vf2 (TARGET_VECTOR)
#define HAVE_pred_zero_extendvnx1si_vf2 (TARGET_VECTOR)
#define HAVE_pred_extendvnx2si_vf2 (TARGET_VECTOR)
#define HAVE_pred_zero_extendvnx2si_vf2 (TARGET_VECTOR)
#define HAVE_pred_extendvnx4si_vf2 (TARGET_VECTOR)
#define HAVE_pred_zero_extendvnx4si_vf2 (TARGET_VECTOR)
#define HAVE_pred_extendvnx8si_vf2 (TARGET_VECTOR)
#define HAVE_pred_zero_extendvnx8si_vf2 (TARGET_VECTOR)
#define HAVE_pred_extendvnx16si_vf2 ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_zero_extendvnx16si_vf2 ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_extendvnx1di_vf2 ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_zero_extendvnx1di_vf2 ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_extendvnx2di_vf2 ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_zero_extendvnx2di_vf2 ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_extendvnx4di_vf2 ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_zero_extendvnx4di_vf2 ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_extendvnx8di_vf2 ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_zero_extendvnx8di_vf2 ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_extendvnx1si_vf4 (TARGET_VECTOR)
#define HAVE_pred_zero_extendvnx1si_vf4 (TARGET_VECTOR)
#define HAVE_pred_extendvnx2si_vf4 (TARGET_VECTOR)
#define HAVE_pred_zero_extendvnx2si_vf4 (TARGET_VECTOR)
#define HAVE_pred_extendvnx4si_vf4 (TARGET_VECTOR)
#define HAVE_pred_zero_extendvnx4si_vf4 (TARGET_VECTOR)
#define HAVE_pred_extendvnx8si_vf4 (TARGET_VECTOR)
#define HAVE_pred_zero_extendvnx8si_vf4 (TARGET_VECTOR)
#define HAVE_pred_extendvnx16si_vf4 ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_zero_extendvnx16si_vf4 ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_extendvnx1di_vf4 ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_zero_extendvnx1di_vf4 ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_extendvnx2di_vf4 ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_zero_extendvnx2di_vf4 ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_extendvnx4di_vf4 ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_zero_extendvnx4di_vf4 ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_extendvnx8di_vf4 ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_zero_extendvnx8di_vf4 ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_extendvnx1di_vf8 ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_zero_extendvnx1di_vf8 ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_extendvnx2di_vf8 ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_zero_extendvnx2di_vf8 ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_extendvnx4di_vf8 ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_zero_extendvnx4di_vf8 ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_extendvnx8di_vf8 ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_zero_extendvnx8di_vf8 ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_dual_widen_addsvnx1hi (TARGET_VECTOR)
#define HAVE_pred_dual_widen_subsvnx1hi (TARGET_VECTOR)
#define HAVE_pred_dual_widen_mulsvnx1hi (TARGET_VECTOR)
#define HAVE_pred_dual_widen_adduvnx1hi (TARGET_VECTOR)
#define HAVE_pred_dual_widen_subuvnx1hi (TARGET_VECTOR)
#define HAVE_pred_dual_widen_muluvnx1hi (TARGET_VECTOR)
#define HAVE_pred_dual_widen_addsvnx2hi (TARGET_VECTOR)
#define HAVE_pred_dual_widen_subsvnx2hi (TARGET_VECTOR)
#define HAVE_pred_dual_widen_mulsvnx2hi (TARGET_VECTOR)
#define HAVE_pred_dual_widen_adduvnx2hi (TARGET_VECTOR)
#define HAVE_pred_dual_widen_subuvnx2hi (TARGET_VECTOR)
#define HAVE_pred_dual_widen_muluvnx2hi (TARGET_VECTOR)
#define HAVE_pred_dual_widen_addsvnx4hi (TARGET_VECTOR)
#define HAVE_pred_dual_widen_subsvnx4hi (TARGET_VECTOR)
#define HAVE_pred_dual_widen_mulsvnx4hi (TARGET_VECTOR)
#define HAVE_pred_dual_widen_adduvnx4hi (TARGET_VECTOR)
#define HAVE_pred_dual_widen_subuvnx4hi (TARGET_VECTOR)
#define HAVE_pred_dual_widen_muluvnx4hi (TARGET_VECTOR)
#define HAVE_pred_dual_widen_addsvnx8hi (TARGET_VECTOR)
#define HAVE_pred_dual_widen_subsvnx8hi (TARGET_VECTOR)
#define HAVE_pred_dual_widen_mulsvnx8hi (TARGET_VECTOR)
#define HAVE_pred_dual_widen_adduvnx8hi (TARGET_VECTOR)
#define HAVE_pred_dual_widen_subuvnx8hi (TARGET_VECTOR)
#define HAVE_pred_dual_widen_muluvnx8hi (TARGET_VECTOR)
#define HAVE_pred_dual_widen_addsvnx16hi (TARGET_VECTOR)
#define HAVE_pred_dual_widen_subsvnx16hi (TARGET_VECTOR)
#define HAVE_pred_dual_widen_mulsvnx16hi (TARGET_VECTOR)
#define HAVE_pred_dual_widen_adduvnx16hi (TARGET_VECTOR)
#define HAVE_pred_dual_widen_subuvnx16hi (TARGET_VECTOR)
#define HAVE_pred_dual_widen_muluvnx16hi (TARGET_VECTOR)
#define HAVE_pred_dual_widen_addsvnx32hi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_dual_widen_subsvnx32hi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_dual_widen_mulsvnx32hi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_dual_widen_adduvnx32hi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_dual_widen_subuvnx32hi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_dual_widen_muluvnx32hi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_dual_widen_addsvnx1si (TARGET_VECTOR)
#define HAVE_pred_dual_widen_subsvnx1si (TARGET_VECTOR)
#define HAVE_pred_dual_widen_mulsvnx1si (TARGET_VECTOR)
#define HAVE_pred_dual_widen_adduvnx1si (TARGET_VECTOR)
#define HAVE_pred_dual_widen_subuvnx1si (TARGET_VECTOR)
#define HAVE_pred_dual_widen_muluvnx1si (TARGET_VECTOR)
#define HAVE_pred_dual_widen_addsvnx2si (TARGET_VECTOR)
#define HAVE_pred_dual_widen_subsvnx2si (TARGET_VECTOR)
#define HAVE_pred_dual_widen_mulsvnx2si (TARGET_VECTOR)
#define HAVE_pred_dual_widen_adduvnx2si (TARGET_VECTOR)
#define HAVE_pred_dual_widen_subuvnx2si (TARGET_VECTOR)
#define HAVE_pred_dual_widen_muluvnx2si (TARGET_VECTOR)
#define HAVE_pred_dual_widen_addsvnx4si (TARGET_VECTOR)
#define HAVE_pred_dual_widen_subsvnx4si (TARGET_VECTOR)
#define HAVE_pred_dual_widen_mulsvnx4si (TARGET_VECTOR)
#define HAVE_pred_dual_widen_adduvnx4si (TARGET_VECTOR)
#define HAVE_pred_dual_widen_subuvnx4si (TARGET_VECTOR)
#define HAVE_pred_dual_widen_muluvnx4si (TARGET_VECTOR)
#define HAVE_pred_dual_widen_addsvnx8si (TARGET_VECTOR)
#define HAVE_pred_dual_widen_subsvnx8si (TARGET_VECTOR)
#define HAVE_pred_dual_widen_mulsvnx8si (TARGET_VECTOR)
#define HAVE_pred_dual_widen_adduvnx8si (TARGET_VECTOR)
#define HAVE_pred_dual_widen_subuvnx8si (TARGET_VECTOR)
#define HAVE_pred_dual_widen_muluvnx8si (TARGET_VECTOR)
#define HAVE_pred_dual_widen_addsvnx16si ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_dual_widen_subsvnx16si ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_dual_widen_mulsvnx16si ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_dual_widen_adduvnx16si ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_dual_widen_subuvnx16si ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_dual_widen_muluvnx16si ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_dual_widen_addsvnx1di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_dual_widen_subsvnx1di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_dual_widen_mulsvnx1di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_dual_widen_adduvnx1di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_dual_widen_subuvnx1di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_dual_widen_muluvnx1di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_dual_widen_addsvnx2di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_dual_widen_subsvnx2di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_dual_widen_mulsvnx2di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_dual_widen_adduvnx2di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_dual_widen_subuvnx2di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_dual_widen_muluvnx2di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_dual_widen_addsvnx4di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_dual_widen_subsvnx4di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_dual_widen_mulsvnx4di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_dual_widen_adduvnx4di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_dual_widen_subuvnx4di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_dual_widen_muluvnx4di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_dual_widen_addsvnx8di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_dual_widen_subsvnx8di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_dual_widen_mulsvnx8di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_dual_widen_adduvnx8di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_dual_widen_subuvnx8di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_dual_widen_muluvnx8di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_dual_widen_addsvnx1hi_scalar (TARGET_VECTOR)
#define HAVE_pred_dual_widen_subsvnx1hi_scalar (TARGET_VECTOR)
#define HAVE_pred_dual_widen_mulsvnx1hi_scalar (TARGET_VECTOR)
#define HAVE_pred_dual_widen_adduvnx1hi_scalar (TARGET_VECTOR)
#define HAVE_pred_dual_widen_subuvnx1hi_scalar (TARGET_VECTOR)
#define HAVE_pred_dual_widen_muluvnx1hi_scalar (TARGET_VECTOR)
#define HAVE_pred_dual_widen_addsvnx2hi_scalar (TARGET_VECTOR)
#define HAVE_pred_dual_widen_subsvnx2hi_scalar (TARGET_VECTOR)
#define HAVE_pred_dual_widen_mulsvnx2hi_scalar (TARGET_VECTOR)
#define HAVE_pred_dual_widen_adduvnx2hi_scalar (TARGET_VECTOR)
#define HAVE_pred_dual_widen_subuvnx2hi_scalar (TARGET_VECTOR)
#define HAVE_pred_dual_widen_muluvnx2hi_scalar (TARGET_VECTOR)
#define HAVE_pred_dual_widen_addsvnx4hi_scalar (TARGET_VECTOR)
#define HAVE_pred_dual_widen_subsvnx4hi_scalar (TARGET_VECTOR)
#define HAVE_pred_dual_widen_mulsvnx4hi_scalar (TARGET_VECTOR)
#define HAVE_pred_dual_widen_adduvnx4hi_scalar (TARGET_VECTOR)
#define HAVE_pred_dual_widen_subuvnx4hi_scalar (TARGET_VECTOR)
#define HAVE_pred_dual_widen_muluvnx4hi_scalar (TARGET_VECTOR)
#define HAVE_pred_dual_widen_addsvnx8hi_scalar (TARGET_VECTOR)
#define HAVE_pred_dual_widen_subsvnx8hi_scalar (TARGET_VECTOR)
#define HAVE_pred_dual_widen_mulsvnx8hi_scalar (TARGET_VECTOR)
#define HAVE_pred_dual_widen_adduvnx8hi_scalar (TARGET_VECTOR)
#define HAVE_pred_dual_widen_subuvnx8hi_scalar (TARGET_VECTOR)
#define HAVE_pred_dual_widen_muluvnx8hi_scalar (TARGET_VECTOR)
#define HAVE_pred_dual_widen_addsvnx16hi_scalar (TARGET_VECTOR)
#define HAVE_pred_dual_widen_subsvnx16hi_scalar (TARGET_VECTOR)
#define HAVE_pred_dual_widen_mulsvnx16hi_scalar (TARGET_VECTOR)
#define HAVE_pred_dual_widen_adduvnx16hi_scalar (TARGET_VECTOR)
#define HAVE_pred_dual_widen_subuvnx16hi_scalar (TARGET_VECTOR)
#define HAVE_pred_dual_widen_muluvnx16hi_scalar (TARGET_VECTOR)
#define HAVE_pred_dual_widen_addsvnx32hi_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_dual_widen_subsvnx32hi_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_dual_widen_mulsvnx32hi_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_dual_widen_adduvnx32hi_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_dual_widen_subuvnx32hi_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_dual_widen_muluvnx32hi_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_dual_widen_addsvnx1si_scalar (TARGET_VECTOR)
#define HAVE_pred_dual_widen_subsvnx1si_scalar (TARGET_VECTOR)
#define HAVE_pred_dual_widen_mulsvnx1si_scalar (TARGET_VECTOR)
#define HAVE_pred_dual_widen_adduvnx1si_scalar (TARGET_VECTOR)
#define HAVE_pred_dual_widen_subuvnx1si_scalar (TARGET_VECTOR)
#define HAVE_pred_dual_widen_muluvnx1si_scalar (TARGET_VECTOR)
#define HAVE_pred_dual_widen_addsvnx2si_scalar (TARGET_VECTOR)
#define HAVE_pred_dual_widen_subsvnx2si_scalar (TARGET_VECTOR)
#define HAVE_pred_dual_widen_mulsvnx2si_scalar (TARGET_VECTOR)
#define HAVE_pred_dual_widen_adduvnx2si_scalar (TARGET_VECTOR)
#define HAVE_pred_dual_widen_subuvnx2si_scalar (TARGET_VECTOR)
#define HAVE_pred_dual_widen_muluvnx2si_scalar (TARGET_VECTOR)
#define HAVE_pred_dual_widen_addsvnx4si_scalar (TARGET_VECTOR)
#define HAVE_pred_dual_widen_subsvnx4si_scalar (TARGET_VECTOR)
#define HAVE_pred_dual_widen_mulsvnx4si_scalar (TARGET_VECTOR)
#define HAVE_pred_dual_widen_adduvnx4si_scalar (TARGET_VECTOR)
#define HAVE_pred_dual_widen_subuvnx4si_scalar (TARGET_VECTOR)
#define HAVE_pred_dual_widen_muluvnx4si_scalar (TARGET_VECTOR)
#define HAVE_pred_dual_widen_addsvnx8si_scalar (TARGET_VECTOR)
#define HAVE_pred_dual_widen_subsvnx8si_scalar (TARGET_VECTOR)
#define HAVE_pred_dual_widen_mulsvnx8si_scalar (TARGET_VECTOR)
#define HAVE_pred_dual_widen_adduvnx8si_scalar (TARGET_VECTOR)
#define HAVE_pred_dual_widen_subuvnx8si_scalar (TARGET_VECTOR)
#define HAVE_pred_dual_widen_muluvnx8si_scalar (TARGET_VECTOR)
#define HAVE_pred_dual_widen_addsvnx16si_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_dual_widen_subsvnx16si_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_dual_widen_mulsvnx16si_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_dual_widen_adduvnx16si_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_dual_widen_subuvnx16si_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_dual_widen_muluvnx16si_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_dual_widen_addsvnx1di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_dual_widen_subsvnx1di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_dual_widen_mulsvnx1di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_dual_widen_adduvnx1di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_dual_widen_subuvnx1di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_dual_widen_muluvnx1di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_dual_widen_addsvnx2di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_dual_widen_subsvnx2di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_dual_widen_mulsvnx2di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_dual_widen_adduvnx2di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_dual_widen_subuvnx2di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_dual_widen_muluvnx2di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_dual_widen_addsvnx4di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_dual_widen_subsvnx4di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_dual_widen_mulsvnx4di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_dual_widen_adduvnx4di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_dual_widen_subuvnx4di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_dual_widen_muluvnx4di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_dual_widen_addsvnx8di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_dual_widen_subsvnx8di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_dual_widen_mulsvnx8di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_dual_widen_adduvnx8di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_dual_widen_subuvnx8di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_dual_widen_muluvnx8di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_single_widen_addsvnx1hi (TARGET_VECTOR)
#define HAVE_pred_single_widen_subsvnx1hi (TARGET_VECTOR)
#define HAVE_pred_single_widen_adduvnx1hi (TARGET_VECTOR)
#define HAVE_pred_single_widen_subuvnx1hi (TARGET_VECTOR)
#define HAVE_pred_single_widen_addsvnx2hi (TARGET_VECTOR)
#define HAVE_pred_single_widen_subsvnx2hi (TARGET_VECTOR)
#define HAVE_pred_single_widen_adduvnx2hi (TARGET_VECTOR)
#define HAVE_pred_single_widen_subuvnx2hi (TARGET_VECTOR)
#define HAVE_pred_single_widen_addsvnx4hi (TARGET_VECTOR)
#define HAVE_pred_single_widen_subsvnx4hi (TARGET_VECTOR)
#define HAVE_pred_single_widen_adduvnx4hi (TARGET_VECTOR)
#define HAVE_pred_single_widen_subuvnx4hi (TARGET_VECTOR)
#define HAVE_pred_single_widen_addsvnx8hi (TARGET_VECTOR)
#define HAVE_pred_single_widen_subsvnx8hi (TARGET_VECTOR)
#define HAVE_pred_single_widen_adduvnx8hi (TARGET_VECTOR)
#define HAVE_pred_single_widen_subuvnx8hi (TARGET_VECTOR)
#define HAVE_pred_single_widen_addsvnx16hi (TARGET_VECTOR)
#define HAVE_pred_single_widen_subsvnx16hi (TARGET_VECTOR)
#define HAVE_pred_single_widen_adduvnx16hi (TARGET_VECTOR)
#define HAVE_pred_single_widen_subuvnx16hi (TARGET_VECTOR)
#define HAVE_pred_single_widen_addsvnx32hi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_single_widen_subsvnx32hi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_single_widen_adduvnx32hi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_single_widen_subuvnx32hi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_single_widen_addsvnx1si (TARGET_VECTOR)
#define HAVE_pred_single_widen_subsvnx1si (TARGET_VECTOR)
#define HAVE_pred_single_widen_adduvnx1si (TARGET_VECTOR)
#define HAVE_pred_single_widen_subuvnx1si (TARGET_VECTOR)
#define HAVE_pred_single_widen_addsvnx2si (TARGET_VECTOR)
#define HAVE_pred_single_widen_subsvnx2si (TARGET_VECTOR)
#define HAVE_pred_single_widen_adduvnx2si (TARGET_VECTOR)
#define HAVE_pred_single_widen_subuvnx2si (TARGET_VECTOR)
#define HAVE_pred_single_widen_addsvnx4si (TARGET_VECTOR)
#define HAVE_pred_single_widen_subsvnx4si (TARGET_VECTOR)
#define HAVE_pred_single_widen_adduvnx4si (TARGET_VECTOR)
#define HAVE_pred_single_widen_subuvnx4si (TARGET_VECTOR)
#define HAVE_pred_single_widen_addsvnx8si (TARGET_VECTOR)
#define HAVE_pred_single_widen_subsvnx8si (TARGET_VECTOR)
#define HAVE_pred_single_widen_adduvnx8si (TARGET_VECTOR)
#define HAVE_pred_single_widen_subuvnx8si (TARGET_VECTOR)
#define HAVE_pred_single_widen_addsvnx16si ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_single_widen_subsvnx16si ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_single_widen_adduvnx16si ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_single_widen_subuvnx16si ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_single_widen_addsvnx1di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_single_widen_subsvnx1di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_single_widen_adduvnx1di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_single_widen_subuvnx1di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_single_widen_addsvnx2di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_single_widen_subsvnx2di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_single_widen_adduvnx2di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_single_widen_subuvnx2di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_single_widen_addsvnx4di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_single_widen_subsvnx4di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_single_widen_adduvnx4di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_single_widen_subuvnx4di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_single_widen_addsvnx8di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_single_widen_subsvnx8di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_single_widen_adduvnx8di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_single_widen_subuvnx8di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_single_widen_addsvnx1hi_scalar (TARGET_VECTOR)
#define HAVE_pred_single_widen_subsvnx1hi_scalar (TARGET_VECTOR)
#define HAVE_pred_single_widen_adduvnx1hi_scalar (TARGET_VECTOR)
#define HAVE_pred_single_widen_subuvnx1hi_scalar (TARGET_VECTOR)
#define HAVE_pred_single_widen_addsvnx2hi_scalar (TARGET_VECTOR)
#define HAVE_pred_single_widen_subsvnx2hi_scalar (TARGET_VECTOR)
#define HAVE_pred_single_widen_adduvnx2hi_scalar (TARGET_VECTOR)
#define HAVE_pred_single_widen_subuvnx2hi_scalar (TARGET_VECTOR)
#define HAVE_pred_single_widen_addsvnx4hi_scalar (TARGET_VECTOR)
#define HAVE_pred_single_widen_subsvnx4hi_scalar (TARGET_VECTOR)
#define HAVE_pred_single_widen_adduvnx4hi_scalar (TARGET_VECTOR)
#define HAVE_pred_single_widen_subuvnx4hi_scalar (TARGET_VECTOR)
#define HAVE_pred_single_widen_addsvnx8hi_scalar (TARGET_VECTOR)
#define HAVE_pred_single_widen_subsvnx8hi_scalar (TARGET_VECTOR)
#define HAVE_pred_single_widen_adduvnx8hi_scalar (TARGET_VECTOR)
#define HAVE_pred_single_widen_subuvnx8hi_scalar (TARGET_VECTOR)
#define HAVE_pred_single_widen_addsvnx16hi_scalar (TARGET_VECTOR)
#define HAVE_pred_single_widen_subsvnx16hi_scalar (TARGET_VECTOR)
#define HAVE_pred_single_widen_adduvnx16hi_scalar (TARGET_VECTOR)
#define HAVE_pred_single_widen_subuvnx16hi_scalar (TARGET_VECTOR)
#define HAVE_pred_single_widen_addsvnx32hi_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_single_widen_subsvnx32hi_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_single_widen_adduvnx32hi_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_single_widen_subuvnx32hi_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_single_widen_addsvnx1si_scalar (TARGET_VECTOR)
#define HAVE_pred_single_widen_subsvnx1si_scalar (TARGET_VECTOR)
#define HAVE_pred_single_widen_adduvnx1si_scalar (TARGET_VECTOR)
#define HAVE_pred_single_widen_subuvnx1si_scalar (TARGET_VECTOR)
#define HAVE_pred_single_widen_addsvnx2si_scalar (TARGET_VECTOR)
#define HAVE_pred_single_widen_subsvnx2si_scalar (TARGET_VECTOR)
#define HAVE_pred_single_widen_adduvnx2si_scalar (TARGET_VECTOR)
#define HAVE_pred_single_widen_subuvnx2si_scalar (TARGET_VECTOR)
#define HAVE_pred_single_widen_addsvnx4si_scalar (TARGET_VECTOR)
#define HAVE_pred_single_widen_subsvnx4si_scalar (TARGET_VECTOR)
#define HAVE_pred_single_widen_adduvnx4si_scalar (TARGET_VECTOR)
#define HAVE_pred_single_widen_subuvnx4si_scalar (TARGET_VECTOR)
#define HAVE_pred_single_widen_addsvnx8si_scalar (TARGET_VECTOR)
#define HAVE_pred_single_widen_subsvnx8si_scalar (TARGET_VECTOR)
#define HAVE_pred_single_widen_adduvnx8si_scalar (TARGET_VECTOR)
#define HAVE_pred_single_widen_subuvnx8si_scalar (TARGET_VECTOR)
#define HAVE_pred_single_widen_addsvnx16si_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_single_widen_subsvnx16si_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_single_widen_adduvnx16si_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_single_widen_subuvnx16si_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_single_widen_addsvnx1di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_single_widen_subsvnx1di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_single_widen_adduvnx1di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_single_widen_subuvnx1di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_single_widen_addsvnx2di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_single_widen_subsvnx2di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_single_widen_adduvnx2di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_single_widen_subuvnx2di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_single_widen_addsvnx4di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_single_widen_subsvnx4di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_single_widen_adduvnx4di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_single_widen_subuvnx4di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_single_widen_addsvnx8di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_single_widen_subsvnx8di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_single_widen_adduvnx8di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_single_widen_subuvnx8di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_widen_mulsuvnx1hi (TARGET_VECTOR)
#define HAVE_pred_widen_mulsuvnx2hi (TARGET_VECTOR)
#define HAVE_pred_widen_mulsuvnx4hi (TARGET_VECTOR)
#define HAVE_pred_widen_mulsuvnx8hi (TARGET_VECTOR)
#define HAVE_pred_widen_mulsuvnx16hi (TARGET_VECTOR)
#define HAVE_pred_widen_mulsuvnx32hi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_widen_mulsuvnx1si (TARGET_VECTOR)
#define HAVE_pred_widen_mulsuvnx2si (TARGET_VECTOR)
#define HAVE_pred_widen_mulsuvnx4si (TARGET_VECTOR)
#define HAVE_pred_widen_mulsuvnx8si (TARGET_VECTOR)
#define HAVE_pred_widen_mulsuvnx16si ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_widen_mulsuvnx1di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_widen_mulsuvnx2di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_widen_mulsuvnx4di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_widen_mulsuvnx8di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_widen_mulsuvnx1hi_scalar (TARGET_VECTOR)
#define HAVE_pred_widen_mulsuvnx2hi_scalar (TARGET_VECTOR)
#define HAVE_pred_widen_mulsuvnx4hi_scalar (TARGET_VECTOR)
#define HAVE_pred_widen_mulsuvnx8hi_scalar (TARGET_VECTOR)
#define HAVE_pred_widen_mulsuvnx16hi_scalar (TARGET_VECTOR)
#define HAVE_pred_widen_mulsuvnx32hi_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_widen_mulsuvnx1si_scalar (TARGET_VECTOR)
#define HAVE_pred_widen_mulsuvnx2si_scalar (TARGET_VECTOR)
#define HAVE_pred_widen_mulsuvnx4si_scalar (TARGET_VECTOR)
#define HAVE_pred_widen_mulsuvnx8si_scalar (TARGET_VECTOR)
#define HAVE_pred_widen_mulsuvnx16si_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_widen_mulsuvnx1di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_widen_mulsuvnx2di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_widen_mulsuvnx4di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_widen_mulsuvnx8di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_extendvnx1hi (TARGET_VECTOR)
#define HAVE_pred_zero_extendvnx1hi (TARGET_VECTOR)
#define HAVE_pred_extendvnx2hi (TARGET_VECTOR)
#define HAVE_pred_zero_extendvnx2hi (TARGET_VECTOR)
#define HAVE_pred_extendvnx4hi (TARGET_VECTOR)
#define HAVE_pred_zero_extendvnx4hi (TARGET_VECTOR)
#define HAVE_pred_extendvnx8hi (TARGET_VECTOR)
#define HAVE_pred_zero_extendvnx8hi (TARGET_VECTOR)
#define HAVE_pred_extendvnx16hi (TARGET_VECTOR)
#define HAVE_pred_zero_extendvnx16hi (TARGET_VECTOR)
#define HAVE_pred_extendvnx32hi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_zero_extendvnx32hi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_extendvnx1si (TARGET_VECTOR)
#define HAVE_pred_zero_extendvnx1si (TARGET_VECTOR)
#define HAVE_pred_extendvnx2si (TARGET_VECTOR)
#define HAVE_pred_zero_extendvnx2si (TARGET_VECTOR)
#define HAVE_pred_extendvnx4si (TARGET_VECTOR)
#define HAVE_pred_zero_extendvnx4si (TARGET_VECTOR)
#define HAVE_pred_extendvnx8si (TARGET_VECTOR)
#define HAVE_pred_zero_extendvnx8si (TARGET_VECTOR)
#define HAVE_pred_extendvnx16si ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_zero_extendvnx16si ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_extendvnx1di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_zero_extendvnx1di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_extendvnx2di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_zero_extendvnx2di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_extendvnx4di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_zero_extendvnx4di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_extendvnx8di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_zero_extendvnx8di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_narrow_ashrvnx1hi (TARGET_VECTOR)
#define HAVE_pred_narrow_lshrvnx1hi (TARGET_VECTOR)
#define HAVE_pred_narrow_ashrvnx2hi (TARGET_VECTOR)
#define HAVE_pred_narrow_lshrvnx2hi (TARGET_VECTOR)
#define HAVE_pred_narrow_ashrvnx4hi (TARGET_VECTOR)
#define HAVE_pred_narrow_lshrvnx4hi (TARGET_VECTOR)
#define HAVE_pred_narrow_ashrvnx8hi (TARGET_VECTOR)
#define HAVE_pred_narrow_lshrvnx8hi (TARGET_VECTOR)
#define HAVE_pred_narrow_ashrvnx16hi (TARGET_VECTOR)
#define HAVE_pred_narrow_lshrvnx16hi (TARGET_VECTOR)
#define HAVE_pred_narrow_ashrvnx32hi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_narrow_lshrvnx32hi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_narrow_ashrvnx1si (TARGET_VECTOR)
#define HAVE_pred_narrow_lshrvnx1si (TARGET_VECTOR)
#define HAVE_pred_narrow_ashrvnx2si (TARGET_VECTOR)
#define HAVE_pred_narrow_lshrvnx2si (TARGET_VECTOR)
#define HAVE_pred_narrow_ashrvnx4si (TARGET_VECTOR)
#define HAVE_pred_narrow_lshrvnx4si (TARGET_VECTOR)
#define HAVE_pred_narrow_ashrvnx8si (TARGET_VECTOR)
#define HAVE_pred_narrow_lshrvnx8si (TARGET_VECTOR)
#define HAVE_pred_narrow_ashrvnx16si ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_narrow_lshrvnx16si ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_narrow_ashrvnx1di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_narrow_lshrvnx1di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_narrow_ashrvnx2di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_narrow_lshrvnx2di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_narrow_ashrvnx4di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_narrow_lshrvnx4di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_narrow_ashrvnx8di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_narrow_lshrvnx8di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_narrow_ashrvnx1hi_scalar (TARGET_VECTOR)
#define HAVE_pred_narrow_lshrvnx1hi_scalar (TARGET_VECTOR)
#define HAVE_pred_narrow_ashrvnx2hi_scalar (TARGET_VECTOR)
#define HAVE_pred_narrow_lshrvnx2hi_scalar (TARGET_VECTOR)
#define HAVE_pred_narrow_ashrvnx4hi_scalar (TARGET_VECTOR)
#define HAVE_pred_narrow_lshrvnx4hi_scalar (TARGET_VECTOR)
#define HAVE_pred_narrow_ashrvnx8hi_scalar (TARGET_VECTOR)
#define HAVE_pred_narrow_lshrvnx8hi_scalar (TARGET_VECTOR)
#define HAVE_pred_narrow_ashrvnx16hi_scalar (TARGET_VECTOR)
#define HAVE_pred_narrow_lshrvnx16hi_scalar (TARGET_VECTOR)
#define HAVE_pred_narrow_ashrvnx32hi_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_narrow_lshrvnx32hi_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_narrow_ashrvnx1si_scalar (TARGET_VECTOR)
#define HAVE_pred_narrow_lshrvnx1si_scalar (TARGET_VECTOR)
#define HAVE_pred_narrow_ashrvnx2si_scalar (TARGET_VECTOR)
#define HAVE_pred_narrow_lshrvnx2si_scalar (TARGET_VECTOR)
#define HAVE_pred_narrow_ashrvnx4si_scalar (TARGET_VECTOR)
#define HAVE_pred_narrow_lshrvnx4si_scalar (TARGET_VECTOR)
#define HAVE_pred_narrow_ashrvnx8si_scalar (TARGET_VECTOR)
#define HAVE_pred_narrow_lshrvnx8si_scalar (TARGET_VECTOR)
#define HAVE_pred_narrow_ashrvnx16si_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_narrow_lshrvnx16si_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_narrow_ashrvnx1di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_narrow_lshrvnx1di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_narrow_ashrvnx2di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_narrow_lshrvnx2di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_narrow_ashrvnx4di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_narrow_lshrvnx4di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_narrow_ashrvnx8di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_narrow_lshrvnx8di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_truncvnx1hi (TARGET_VECTOR)
#define HAVE_pred_truncvnx2hi (TARGET_VECTOR)
#define HAVE_pred_truncvnx4hi (TARGET_VECTOR)
#define HAVE_pred_truncvnx8hi (TARGET_VECTOR)
#define HAVE_pred_truncvnx16hi (TARGET_VECTOR)
#define HAVE_pred_truncvnx32hi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_truncvnx1si (TARGET_VECTOR)
#define HAVE_pred_truncvnx2si (TARGET_VECTOR)
#define HAVE_pred_truncvnx4si (TARGET_VECTOR)
#define HAVE_pred_truncvnx8si (TARGET_VECTOR)
#define HAVE_pred_truncvnx16si ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_truncvnx1di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_truncvnx2di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_truncvnx4di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_truncvnx8di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_ssaddvnx1qi (TARGET_VECTOR)
#define HAVE_pred_sssubvnx1qi (TARGET_VECTOR)
#define HAVE_pred_usaddvnx1qi (TARGET_VECTOR)
#define HAVE_pred_ussubvnx1qi (TARGET_VECTOR)
#define HAVE_pred_ssaddvnx2qi (TARGET_VECTOR)
#define HAVE_pred_sssubvnx2qi (TARGET_VECTOR)
#define HAVE_pred_usaddvnx2qi (TARGET_VECTOR)
#define HAVE_pred_ussubvnx2qi (TARGET_VECTOR)
#define HAVE_pred_ssaddvnx4qi (TARGET_VECTOR)
#define HAVE_pred_sssubvnx4qi (TARGET_VECTOR)
#define HAVE_pred_usaddvnx4qi (TARGET_VECTOR)
#define HAVE_pred_ussubvnx4qi (TARGET_VECTOR)
#define HAVE_pred_ssaddvnx8qi (TARGET_VECTOR)
#define HAVE_pred_sssubvnx8qi (TARGET_VECTOR)
#define HAVE_pred_usaddvnx8qi (TARGET_VECTOR)
#define HAVE_pred_ussubvnx8qi (TARGET_VECTOR)
#define HAVE_pred_ssaddvnx16qi (TARGET_VECTOR)
#define HAVE_pred_sssubvnx16qi (TARGET_VECTOR)
#define HAVE_pred_usaddvnx16qi (TARGET_VECTOR)
#define HAVE_pred_ussubvnx16qi (TARGET_VECTOR)
#define HAVE_pred_ssaddvnx32qi (TARGET_VECTOR)
#define HAVE_pred_sssubvnx32qi (TARGET_VECTOR)
#define HAVE_pred_usaddvnx32qi (TARGET_VECTOR)
#define HAVE_pred_ussubvnx32qi (TARGET_VECTOR)
#define HAVE_pred_ssaddvnx64qi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_sssubvnx64qi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_usaddvnx64qi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_ussubvnx64qi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_ssaddvnx1hi (TARGET_VECTOR)
#define HAVE_pred_sssubvnx1hi (TARGET_VECTOR)
#define HAVE_pred_usaddvnx1hi (TARGET_VECTOR)
#define HAVE_pred_ussubvnx1hi (TARGET_VECTOR)
#define HAVE_pred_ssaddvnx2hi (TARGET_VECTOR)
#define HAVE_pred_sssubvnx2hi (TARGET_VECTOR)
#define HAVE_pred_usaddvnx2hi (TARGET_VECTOR)
#define HAVE_pred_ussubvnx2hi (TARGET_VECTOR)
#define HAVE_pred_ssaddvnx4hi (TARGET_VECTOR)
#define HAVE_pred_sssubvnx4hi (TARGET_VECTOR)
#define HAVE_pred_usaddvnx4hi (TARGET_VECTOR)
#define HAVE_pred_ussubvnx4hi (TARGET_VECTOR)
#define HAVE_pred_ssaddvnx8hi (TARGET_VECTOR)
#define HAVE_pred_sssubvnx8hi (TARGET_VECTOR)
#define HAVE_pred_usaddvnx8hi (TARGET_VECTOR)
#define HAVE_pred_ussubvnx8hi (TARGET_VECTOR)
#define HAVE_pred_ssaddvnx16hi (TARGET_VECTOR)
#define HAVE_pred_sssubvnx16hi (TARGET_VECTOR)
#define HAVE_pred_usaddvnx16hi (TARGET_VECTOR)
#define HAVE_pred_ussubvnx16hi (TARGET_VECTOR)
#define HAVE_pred_ssaddvnx32hi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_sssubvnx32hi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_usaddvnx32hi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_ussubvnx32hi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_ssaddvnx1si (TARGET_VECTOR)
#define HAVE_pred_sssubvnx1si (TARGET_VECTOR)
#define HAVE_pred_usaddvnx1si (TARGET_VECTOR)
#define HAVE_pred_ussubvnx1si (TARGET_VECTOR)
#define HAVE_pred_ssaddvnx2si (TARGET_VECTOR)
#define HAVE_pred_sssubvnx2si (TARGET_VECTOR)
#define HAVE_pred_usaddvnx2si (TARGET_VECTOR)
#define HAVE_pred_ussubvnx2si (TARGET_VECTOR)
#define HAVE_pred_ssaddvnx4si (TARGET_VECTOR)
#define HAVE_pred_sssubvnx4si (TARGET_VECTOR)
#define HAVE_pred_usaddvnx4si (TARGET_VECTOR)
#define HAVE_pred_ussubvnx4si (TARGET_VECTOR)
#define HAVE_pred_ssaddvnx8si (TARGET_VECTOR)
#define HAVE_pred_sssubvnx8si (TARGET_VECTOR)
#define HAVE_pred_usaddvnx8si (TARGET_VECTOR)
#define HAVE_pred_ussubvnx8si (TARGET_VECTOR)
#define HAVE_pred_ssaddvnx16si ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_sssubvnx16si ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_usaddvnx16si ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_ussubvnx16si ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_ssaddvnx1di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_sssubvnx1di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_usaddvnx1di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_ussubvnx1di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_ssaddvnx2di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_sssubvnx2di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_usaddvnx2di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_ussubvnx2di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_ssaddvnx4di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_sssubvnx4di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_usaddvnx4di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_ussubvnx4di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_ssaddvnx8di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_sssubvnx8di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_usaddvnx8di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_ussubvnx8di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_ssaddvnx1qi_scalar (TARGET_VECTOR)
#define HAVE_pred_usaddvnx1qi_scalar (TARGET_VECTOR)
#define HAVE_pred_ssaddvnx2qi_scalar (TARGET_VECTOR)
#define HAVE_pred_usaddvnx2qi_scalar (TARGET_VECTOR)
#define HAVE_pred_ssaddvnx4qi_scalar (TARGET_VECTOR)
#define HAVE_pred_usaddvnx4qi_scalar (TARGET_VECTOR)
#define HAVE_pred_ssaddvnx8qi_scalar (TARGET_VECTOR)
#define HAVE_pred_usaddvnx8qi_scalar (TARGET_VECTOR)
#define HAVE_pred_ssaddvnx16qi_scalar (TARGET_VECTOR)
#define HAVE_pred_usaddvnx16qi_scalar (TARGET_VECTOR)
#define HAVE_pred_ssaddvnx32qi_scalar (TARGET_VECTOR)
#define HAVE_pred_usaddvnx32qi_scalar (TARGET_VECTOR)
#define HAVE_pred_ssaddvnx64qi_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_usaddvnx64qi_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_ssaddvnx1hi_scalar (TARGET_VECTOR)
#define HAVE_pred_usaddvnx1hi_scalar (TARGET_VECTOR)
#define HAVE_pred_ssaddvnx2hi_scalar (TARGET_VECTOR)
#define HAVE_pred_usaddvnx2hi_scalar (TARGET_VECTOR)
#define HAVE_pred_ssaddvnx4hi_scalar (TARGET_VECTOR)
#define HAVE_pred_usaddvnx4hi_scalar (TARGET_VECTOR)
#define HAVE_pred_ssaddvnx8hi_scalar (TARGET_VECTOR)
#define HAVE_pred_usaddvnx8hi_scalar (TARGET_VECTOR)
#define HAVE_pred_ssaddvnx16hi_scalar (TARGET_VECTOR)
#define HAVE_pred_usaddvnx16hi_scalar (TARGET_VECTOR)
#define HAVE_pred_ssaddvnx32hi_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_usaddvnx32hi_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_ssaddvnx1si_scalar (TARGET_VECTOR)
#define HAVE_pred_usaddvnx1si_scalar (TARGET_VECTOR)
#define HAVE_pred_ssaddvnx2si_scalar (TARGET_VECTOR)
#define HAVE_pred_usaddvnx2si_scalar (TARGET_VECTOR)
#define HAVE_pred_ssaddvnx4si_scalar (TARGET_VECTOR)
#define HAVE_pred_usaddvnx4si_scalar (TARGET_VECTOR)
#define HAVE_pred_ssaddvnx8si_scalar (TARGET_VECTOR)
#define HAVE_pred_usaddvnx8si_scalar (TARGET_VECTOR)
#define HAVE_pred_ssaddvnx16si_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_usaddvnx16si_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_sssubvnx1qi_scalar (TARGET_VECTOR)
#define HAVE_pred_ussubvnx1qi_scalar (TARGET_VECTOR)
#define HAVE_pred_sssubvnx2qi_scalar (TARGET_VECTOR)
#define HAVE_pred_ussubvnx2qi_scalar (TARGET_VECTOR)
#define HAVE_pred_sssubvnx4qi_scalar (TARGET_VECTOR)
#define HAVE_pred_ussubvnx4qi_scalar (TARGET_VECTOR)
#define HAVE_pred_sssubvnx8qi_scalar (TARGET_VECTOR)
#define HAVE_pred_ussubvnx8qi_scalar (TARGET_VECTOR)
#define HAVE_pred_sssubvnx16qi_scalar (TARGET_VECTOR)
#define HAVE_pred_ussubvnx16qi_scalar (TARGET_VECTOR)
#define HAVE_pred_sssubvnx32qi_scalar (TARGET_VECTOR)
#define HAVE_pred_ussubvnx32qi_scalar (TARGET_VECTOR)
#define HAVE_pred_sssubvnx64qi_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_ussubvnx64qi_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_sssubvnx1hi_scalar (TARGET_VECTOR)
#define HAVE_pred_ussubvnx1hi_scalar (TARGET_VECTOR)
#define HAVE_pred_sssubvnx2hi_scalar (TARGET_VECTOR)
#define HAVE_pred_ussubvnx2hi_scalar (TARGET_VECTOR)
#define HAVE_pred_sssubvnx4hi_scalar (TARGET_VECTOR)
#define HAVE_pred_ussubvnx4hi_scalar (TARGET_VECTOR)
#define HAVE_pred_sssubvnx8hi_scalar (TARGET_VECTOR)
#define HAVE_pred_ussubvnx8hi_scalar (TARGET_VECTOR)
#define HAVE_pred_sssubvnx16hi_scalar (TARGET_VECTOR)
#define HAVE_pred_ussubvnx16hi_scalar (TARGET_VECTOR)
#define HAVE_pred_sssubvnx32hi_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_ussubvnx32hi_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_sssubvnx1si_scalar (TARGET_VECTOR)
#define HAVE_pred_ussubvnx1si_scalar (TARGET_VECTOR)
#define HAVE_pred_sssubvnx2si_scalar (TARGET_VECTOR)
#define HAVE_pred_ussubvnx2si_scalar (TARGET_VECTOR)
#define HAVE_pred_sssubvnx4si_scalar (TARGET_VECTOR)
#define HAVE_pred_ussubvnx4si_scalar (TARGET_VECTOR)
#define HAVE_pred_sssubvnx8si_scalar (TARGET_VECTOR)
#define HAVE_pred_ussubvnx8si_scalar (TARGET_VECTOR)
#define HAVE_pred_sssubvnx16si_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_ussubvnx16si_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_aadduvnx1qi (TARGET_VECTOR)
#define HAVE_pred_aaddvnx1qi (TARGET_VECTOR)
#define HAVE_pred_asubuvnx1qi (TARGET_VECTOR)
#define HAVE_pred_asubvnx1qi (TARGET_VECTOR)
#define HAVE_pred_smulvnx1qi (TARGET_VECTOR)
#define HAVE_pred_ssrlvnx1qi (TARGET_VECTOR)
#define HAVE_pred_ssravnx1qi (TARGET_VECTOR)
#define HAVE_pred_aadduvnx2qi (TARGET_VECTOR)
#define HAVE_pred_aaddvnx2qi (TARGET_VECTOR)
#define HAVE_pred_asubuvnx2qi (TARGET_VECTOR)
#define HAVE_pred_asubvnx2qi (TARGET_VECTOR)
#define HAVE_pred_smulvnx2qi (TARGET_VECTOR)
#define HAVE_pred_ssrlvnx2qi (TARGET_VECTOR)
#define HAVE_pred_ssravnx2qi (TARGET_VECTOR)
#define HAVE_pred_aadduvnx4qi (TARGET_VECTOR)
#define HAVE_pred_aaddvnx4qi (TARGET_VECTOR)
#define HAVE_pred_asubuvnx4qi (TARGET_VECTOR)
#define HAVE_pred_asubvnx4qi (TARGET_VECTOR)
#define HAVE_pred_smulvnx4qi (TARGET_VECTOR)
#define HAVE_pred_ssrlvnx4qi (TARGET_VECTOR)
#define HAVE_pred_ssravnx4qi (TARGET_VECTOR)
#define HAVE_pred_aadduvnx8qi (TARGET_VECTOR)
#define HAVE_pred_aaddvnx8qi (TARGET_VECTOR)
#define HAVE_pred_asubuvnx8qi (TARGET_VECTOR)
#define HAVE_pred_asubvnx8qi (TARGET_VECTOR)
#define HAVE_pred_smulvnx8qi (TARGET_VECTOR)
#define HAVE_pred_ssrlvnx8qi (TARGET_VECTOR)
#define HAVE_pred_ssravnx8qi (TARGET_VECTOR)
#define HAVE_pred_aadduvnx16qi (TARGET_VECTOR)
#define HAVE_pred_aaddvnx16qi (TARGET_VECTOR)
#define HAVE_pred_asubuvnx16qi (TARGET_VECTOR)
#define HAVE_pred_asubvnx16qi (TARGET_VECTOR)
#define HAVE_pred_smulvnx16qi (TARGET_VECTOR)
#define HAVE_pred_ssrlvnx16qi (TARGET_VECTOR)
#define HAVE_pred_ssravnx16qi (TARGET_VECTOR)
#define HAVE_pred_aadduvnx32qi (TARGET_VECTOR)
#define HAVE_pred_aaddvnx32qi (TARGET_VECTOR)
#define HAVE_pred_asubuvnx32qi (TARGET_VECTOR)
#define HAVE_pred_asubvnx32qi (TARGET_VECTOR)
#define HAVE_pred_smulvnx32qi (TARGET_VECTOR)
#define HAVE_pred_ssrlvnx32qi (TARGET_VECTOR)
#define HAVE_pred_ssravnx32qi (TARGET_VECTOR)
#define HAVE_pred_aadduvnx64qi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_aaddvnx64qi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_asubuvnx64qi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_asubvnx64qi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_smulvnx64qi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_ssrlvnx64qi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_ssravnx64qi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_aadduvnx1hi (TARGET_VECTOR)
#define HAVE_pred_aaddvnx1hi (TARGET_VECTOR)
#define HAVE_pred_asubuvnx1hi (TARGET_VECTOR)
#define HAVE_pred_asubvnx1hi (TARGET_VECTOR)
#define HAVE_pred_smulvnx1hi (TARGET_VECTOR)
#define HAVE_pred_ssrlvnx1hi (TARGET_VECTOR)
#define HAVE_pred_ssravnx1hi (TARGET_VECTOR)
#define HAVE_pred_aadduvnx2hi (TARGET_VECTOR)
#define HAVE_pred_aaddvnx2hi (TARGET_VECTOR)
#define HAVE_pred_asubuvnx2hi (TARGET_VECTOR)
#define HAVE_pred_asubvnx2hi (TARGET_VECTOR)
#define HAVE_pred_smulvnx2hi (TARGET_VECTOR)
#define HAVE_pred_ssrlvnx2hi (TARGET_VECTOR)
#define HAVE_pred_ssravnx2hi (TARGET_VECTOR)
#define HAVE_pred_aadduvnx4hi (TARGET_VECTOR)
#define HAVE_pred_aaddvnx4hi (TARGET_VECTOR)
#define HAVE_pred_asubuvnx4hi (TARGET_VECTOR)
#define HAVE_pred_asubvnx4hi (TARGET_VECTOR)
#define HAVE_pred_smulvnx4hi (TARGET_VECTOR)
#define HAVE_pred_ssrlvnx4hi (TARGET_VECTOR)
#define HAVE_pred_ssravnx4hi (TARGET_VECTOR)
#define HAVE_pred_aadduvnx8hi (TARGET_VECTOR)
#define HAVE_pred_aaddvnx8hi (TARGET_VECTOR)
#define HAVE_pred_asubuvnx8hi (TARGET_VECTOR)
#define HAVE_pred_asubvnx8hi (TARGET_VECTOR)
#define HAVE_pred_smulvnx8hi (TARGET_VECTOR)
#define HAVE_pred_ssrlvnx8hi (TARGET_VECTOR)
#define HAVE_pred_ssravnx8hi (TARGET_VECTOR)
#define HAVE_pred_aadduvnx16hi (TARGET_VECTOR)
#define HAVE_pred_aaddvnx16hi (TARGET_VECTOR)
#define HAVE_pred_asubuvnx16hi (TARGET_VECTOR)
#define HAVE_pred_asubvnx16hi (TARGET_VECTOR)
#define HAVE_pred_smulvnx16hi (TARGET_VECTOR)
#define HAVE_pred_ssrlvnx16hi (TARGET_VECTOR)
#define HAVE_pred_ssravnx16hi (TARGET_VECTOR)
#define HAVE_pred_aadduvnx32hi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_aaddvnx32hi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_asubuvnx32hi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_asubvnx32hi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_smulvnx32hi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_ssrlvnx32hi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_ssravnx32hi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_aadduvnx1si (TARGET_VECTOR)
#define HAVE_pred_aaddvnx1si (TARGET_VECTOR)
#define HAVE_pred_asubuvnx1si (TARGET_VECTOR)
#define HAVE_pred_asubvnx1si (TARGET_VECTOR)
#define HAVE_pred_smulvnx1si (TARGET_VECTOR)
#define HAVE_pred_ssrlvnx1si (TARGET_VECTOR)
#define HAVE_pred_ssravnx1si (TARGET_VECTOR)
#define HAVE_pred_aadduvnx2si (TARGET_VECTOR)
#define HAVE_pred_aaddvnx2si (TARGET_VECTOR)
#define HAVE_pred_asubuvnx2si (TARGET_VECTOR)
#define HAVE_pred_asubvnx2si (TARGET_VECTOR)
#define HAVE_pred_smulvnx2si (TARGET_VECTOR)
#define HAVE_pred_ssrlvnx2si (TARGET_VECTOR)
#define HAVE_pred_ssravnx2si (TARGET_VECTOR)
#define HAVE_pred_aadduvnx4si (TARGET_VECTOR)
#define HAVE_pred_aaddvnx4si (TARGET_VECTOR)
#define HAVE_pred_asubuvnx4si (TARGET_VECTOR)
#define HAVE_pred_asubvnx4si (TARGET_VECTOR)
#define HAVE_pred_smulvnx4si (TARGET_VECTOR)
#define HAVE_pred_ssrlvnx4si (TARGET_VECTOR)
#define HAVE_pred_ssravnx4si (TARGET_VECTOR)
#define HAVE_pred_aadduvnx8si (TARGET_VECTOR)
#define HAVE_pred_aaddvnx8si (TARGET_VECTOR)
#define HAVE_pred_asubuvnx8si (TARGET_VECTOR)
#define HAVE_pred_asubvnx8si (TARGET_VECTOR)
#define HAVE_pred_smulvnx8si (TARGET_VECTOR)
#define HAVE_pred_ssrlvnx8si (TARGET_VECTOR)
#define HAVE_pred_ssravnx8si (TARGET_VECTOR)
#define HAVE_pred_aadduvnx16si ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_aaddvnx16si ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_asubuvnx16si ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_asubvnx16si ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_smulvnx16si ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_ssrlvnx16si ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_ssravnx16si ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_aadduvnx1di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_aaddvnx1di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_asubuvnx1di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_asubvnx1di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_smulvnx1di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_ssrlvnx1di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_ssravnx1di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_aadduvnx2di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_aaddvnx2di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_asubuvnx2di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_asubvnx2di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_smulvnx2di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_ssrlvnx2di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_ssravnx2di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_aadduvnx4di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_aaddvnx4di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_asubuvnx4di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_asubvnx4di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_smulvnx4di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_ssrlvnx4di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_ssravnx4di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_aadduvnx8di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_aaddvnx8di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_asubuvnx8di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_asubvnx8di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_smulvnx8di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_ssrlvnx8di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_ssravnx8di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_aadduvnx1qi_scalar (TARGET_VECTOR)
#define HAVE_pred_aaddvnx1qi_scalar (TARGET_VECTOR)
#define HAVE_pred_asubuvnx1qi_scalar (TARGET_VECTOR)
#define HAVE_pred_asubvnx1qi_scalar (TARGET_VECTOR)
#define HAVE_pred_smulvnx1qi_scalar (TARGET_VECTOR)
#define HAVE_pred_aadduvnx2qi_scalar (TARGET_VECTOR)
#define HAVE_pred_aaddvnx2qi_scalar (TARGET_VECTOR)
#define HAVE_pred_asubuvnx2qi_scalar (TARGET_VECTOR)
#define HAVE_pred_asubvnx2qi_scalar (TARGET_VECTOR)
#define HAVE_pred_smulvnx2qi_scalar (TARGET_VECTOR)
#define HAVE_pred_aadduvnx4qi_scalar (TARGET_VECTOR)
#define HAVE_pred_aaddvnx4qi_scalar (TARGET_VECTOR)
#define HAVE_pred_asubuvnx4qi_scalar (TARGET_VECTOR)
#define HAVE_pred_asubvnx4qi_scalar (TARGET_VECTOR)
#define HAVE_pred_smulvnx4qi_scalar (TARGET_VECTOR)
#define HAVE_pred_aadduvnx8qi_scalar (TARGET_VECTOR)
#define HAVE_pred_aaddvnx8qi_scalar (TARGET_VECTOR)
#define HAVE_pred_asubuvnx8qi_scalar (TARGET_VECTOR)
#define HAVE_pred_asubvnx8qi_scalar (TARGET_VECTOR)
#define HAVE_pred_smulvnx8qi_scalar (TARGET_VECTOR)
#define HAVE_pred_aadduvnx16qi_scalar (TARGET_VECTOR)
#define HAVE_pred_aaddvnx16qi_scalar (TARGET_VECTOR)
#define HAVE_pred_asubuvnx16qi_scalar (TARGET_VECTOR)
#define HAVE_pred_asubvnx16qi_scalar (TARGET_VECTOR)
#define HAVE_pred_smulvnx16qi_scalar (TARGET_VECTOR)
#define HAVE_pred_aadduvnx32qi_scalar (TARGET_VECTOR)
#define HAVE_pred_aaddvnx32qi_scalar (TARGET_VECTOR)
#define HAVE_pred_asubuvnx32qi_scalar (TARGET_VECTOR)
#define HAVE_pred_asubvnx32qi_scalar (TARGET_VECTOR)
#define HAVE_pred_smulvnx32qi_scalar (TARGET_VECTOR)
#define HAVE_pred_aadduvnx64qi_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_aaddvnx64qi_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_asubuvnx64qi_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_asubvnx64qi_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_smulvnx64qi_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_aadduvnx1hi_scalar (TARGET_VECTOR)
#define HAVE_pred_aaddvnx1hi_scalar (TARGET_VECTOR)
#define HAVE_pred_asubuvnx1hi_scalar (TARGET_VECTOR)
#define HAVE_pred_asubvnx1hi_scalar (TARGET_VECTOR)
#define HAVE_pred_smulvnx1hi_scalar (TARGET_VECTOR)
#define HAVE_pred_aadduvnx2hi_scalar (TARGET_VECTOR)
#define HAVE_pred_aaddvnx2hi_scalar (TARGET_VECTOR)
#define HAVE_pred_asubuvnx2hi_scalar (TARGET_VECTOR)
#define HAVE_pred_asubvnx2hi_scalar (TARGET_VECTOR)
#define HAVE_pred_smulvnx2hi_scalar (TARGET_VECTOR)
#define HAVE_pred_aadduvnx4hi_scalar (TARGET_VECTOR)
#define HAVE_pred_aaddvnx4hi_scalar (TARGET_VECTOR)
#define HAVE_pred_asubuvnx4hi_scalar (TARGET_VECTOR)
#define HAVE_pred_asubvnx4hi_scalar (TARGET_VECTOR)
#define HAVE_pred_smulvnx4hi_scalar (TARGET_VECTOR)
#define HAVE_pred_aadduvnx8hi_scalar (TARGET_VECTOR)
#define HAVE_pred_aaddvnx8hi_scalar (TARGET_VECTOR)
#define HAVE_pred_asubuvnx8hi_scalar (TARGET_VECTOR)
#define HAVE_pred_asubvnx8hi_scalar (TARGET_VECTOR)
#define HAVE_pred_smulvnx8hi_scalar (TARGET_VECTOR)
#define HAVE_pred_aadduvnx16hi_scalar (TARGET_VECTOR)
#define HAVE_pred_aaddvnx16hi_scalar (TARGET_VECTOR)
#define HAVE_pred_asubuvnx16hi_scalar (TARGET_VECTOR)
#define HAVE_pred_asubvnx16hi_scalar (TARGET_VECTOR)
#define HAVE_pred_smulvnx16hi_scalar (TARGET_VECTOR)
#define HAVE_pred_aadduvnx32hi_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_aaddvnx32hi_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_asubuvnx32hi_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_asubvnx32hi_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_smulvnx32hi_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_aadduvnx1si_scalar (TARGET_VECTOR)
#define HAVE_pred_aaddvnx1si_scalar (TARGET_VECTOR)
#define HAVE_pred_asubuvnx1si_scalar (TARGET_VECTOR)
#define HAVE_pred_asubvnx1si_scalar (TARGET_VECTOR)
#define HAVE_pred_smulvnx1si_scalar (TARGET_VECTOR)
#define HAVE_pred_aadduvnx2si_scalar (TARGET_VECTOR)
#define HAVE_pred_aaddvnx2si_scalar (TARGET_VECTOR)
#define HAVE_pred_asubuvnx2si_scalar (TARGET_VECTOR)
#define HAVE_pred_asubvnx2si_scalar (TARGET_VECTOR)
#define HAVE_pred_smulvnx2si_scalar (TARGET_VECTOR)
#define HAVE_pred_aadduvnx4si_scalar (TARGET_VECTOR)
#define HAVE_pred_aaddvnx4si_scalar (TARGET_VECTOR)
#define HAVE_pred_asubuvnx4si_scalar (TARGET_VECTOR)
#define HAVE_pred_asubvnx4si_scalar (TARGET_VECTOR)
#define HAVE_pred_smulvnx4si_scalar (TARGET_VECTOR)
#define HAVE_pred_aadduvnx8si_scalar (TARGET_VECTOR)
#define HAVE_pred_aaddvnx8si_scalar (TARGET_VECTOR)
#define HAVE_pred_asubuvnx8si_scalar (TARGET_VECTOR)
#define HAVE_pred_asubvnx8si_scalar (TARGET_VECTOR)
#define HAVE_pred_smulvnx8si_scalar (TARGET_VECTOR)
#define HAVE_pred_aadduvnx16si_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_aaddvnx16si_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_asubuvnx16si_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_asubvnx16si_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_smulvnx16si_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_ssrlvnx1qi_scalar (TARGET_VECTOR)
#define HAVE_pred_ssravnx1qi_scalar (TARGET_VECTOR)
#define HAVE_pred_ssrlvnx2qi_scalar (TARGET_VECTOR)
#define HAVE_pred_ssravnx2qi_scalar (TARGET_VECTOR)
#define HAVE_pred_ssrlvnx4qi_scalar (TARGET_VECTOR)
#define HAVE_pred_ssravnx4qi_scalar (TARGET_VECTOR)
#define HAVE_pred_ssrlvnx8qi_scalar (TARGET_VECTOR)
#define HAVE_pred_ssravnx8qi_scalar (TARGET_VECTOR)
#define HAVE_pred_ssrlvnx16qi_scalar (TARGET_VECTOR)
#define HAVE_pred_ssravnx16qi_scalar (TARGET_VECTOR)
#define HAVE_pred_ssrlvnx32qi_scalar (TARGET_VECTOR)
#define HAVE_pred_ssravnx32qi_scalar (TARGET_VECTOR)
#define HAVE_pred_ssrlvnx64qi_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_ssravnx64qi_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_ssrlvnx1hi_scalar (TARGET_VECTOR)
#define HAVE_pred_ssravnx1hi_scalar (TARGET_VECTOR)
#define HAVE_pred_ssrlvnx2hi_scalar (TARGET_VECTOR)
#define HAVE_pred_ssravnx2hi_scalar (TARGET_VECTOR)
#define HAVE_pred_ssrlvnx4hi_scalar (TARGET_VECTOR)
#define HAVE_pred_ssravnx4hi_scalar (TARGET_VECTOR)
#define HAVE_pred_ssrlvnx8hi_scalar (TARGET_VECTOR)
#define HAVE_pred_ssravnx8hi_scalar (TARGET_VECTOR)
#define HAVE_pred_ssrlvnx16hi_scalar (TARGET_VECTOR)
#define HAVE_pred_ssravnx16hi_scalar (TARGET_VECTOR)
#define HAVE_pred_ssrlvnx32hi_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_ssravnx32hi_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_ssrlvnx1si_scalar (TARGET_VECTOR)
#define HAVE_pred_ssravnx1si_scalar (TARGET_VECTOR)
#define HAVE_pred_ssrlvnx2si_scalar (TARGET_VECTOR)
#define HAVE_pred_ssravnx2si_scalar (TARGET_VECTOR)
#define HAVE_pred_ssrlvnx4si_scalar (TARGET_VECTOR)
#define HAVE_pred_ssravnx4si_scalar (TARGET_VECTOR)
#define HAVE_pred_ssrlvnx8si_scalar (TARGET_VECTOR)
#define HAVE_pred_ssravnx8si_scalar (TARGET_VECTOR)
#define HAVE_pred_ssrlvnx16si_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_ssravnx16si_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_ssrlvnx1di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_ssravnx1di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_ssrlvnx2di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_ssravnx2di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_ssrlvnx4di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_ssravnx4di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_ssrlvnx8di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_ssravnx8di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_narrow_clipvnx1hi (TARGET_VECTOR)
#define HAVE_pred_narrow_clipuvnx1hi (TARGET_VECTOR)
#define HAVE_pred_narrow_clipvnx2hi (TARGET_VECTOR)
#define HAVE_pred_narrow_clipuvnx2hi (TARGET_VECTOR)
#define HAVE_pred_narrow_clipvnx4hi (TARGET_VECTOR)
#define HAVE_pred_narrow_clipuvnx4hi (TARGET_VECTOR)
#define HAVE_pred_narrow_clipvnx8hi (TARGET_VECTOR)
#define HAVE_pred_narrow_clipuvnx8hi (TARGET_VECTOR)
#define HAVE_pred_narrow_clipvnx16hi (TARGET_VECTOR)
#define HAVE_pred_narrow_clipuvnx16hi (TARGET_VECTOR)
#define HAVE_pred_narrow_clipvnx32hi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_narrow_clipuvnx32hi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_narrow_clipvnx1si (TARGET_VECTOR)
#define HAVE_pred_narrow_clipuvnx1si (TARGET_VECTOR)
#define HAVE_pred_narrow_clipvnx2si (TARGET_VECTOR)
#define HAVE_pred_narrow_clipuvnx2si (TARGET_VECTOR)
#define HAVE_pred_narrow_clipvnx4si (TARGET_VECTOR)
#define HAVE_pred_narrow_clipuvnx4si (TARGET_VECTOR)
#define HAVE_pred_narrow_clipvnx8si (TARGET_VECTOR)
#define HAVE_pred_narrow_clipuvnx8si (TARGET_VECTOR)
#define HAVE_pred_narrow_clipvnx16si ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_narrow_clipuvnx16si ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_narrow_clipvnx1di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_narrow_clipuvnx1di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_narrow_clipvnx2di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_narrow_clipuvnx2di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_narrow_clipvnx4di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_narrow_clipuvnx4di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_narrow_clipvnx8di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_narrow_clipuvnx8di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_narrow_clipvnx1hi_scalar (TARGET_VECTOR)
#define HAVE_pred_narrow_clipuvnx1hi_scalar (TARGET_VECTOR)
#define HAVE_pred_narrow_clipvnx2hi_scalar (TARGET_VECTOR)
#define HAVE_pred_narrow_clipuvnx2hi_scalar (TARGET_VECTOR)
#define HAVE_pred_narrow_clipvnx4hi_scalar (TARGET_VECTOR)
#define HAVE_pred_narrow_clipuvnx4hi_scalar (TARGET_VECTOR)
#define HAVE_pred_narrow_clipvnx8hi_scalar (TARGET_VECTOR)
#define HAVE_pred_narrow_clipuvnx8hi_scalar (TARGET_VECTOR)
#define HAVE_pred_narrow_clipvnx16hi_scalar (TARGET_VECTOR)
#define HAVE_pred_narrow_clipuvnx16hi_scalar (TARGET_VECTOR)
#define HAVE_pred_narrow_clipvnx32hi_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_narrow_clipuvnx32hi_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_narrow_clipvnx1si_scalar (TARGET_VECTOR)
#define HAVE_pred_narrow_clipuvnx1si_scalar (TARGET_VECTOR)
#define HAVE_pred_narrow_clipvnx2si_scalar (TARGET_VECTOR)
#define HAVE_pred_narrow_clipuvnx2si_scalar (TARGET_VECTOR)
#define HAVE_pred_narrow_clipvnx4si_scalar (TARGET_VECTOR)
#define HAVE_pred_narrow_clipuvnx4si_scalar (TARGET_VECTOR)
#define HAVE_pred_narrow_clipvnx8si_scalar (TARGET_VECTOR)
#define HAVE_pred_narrow_clipuvnx8si_scalar (TARGET_VECTOR)
#define HAVE_pred_narrow_clipvnx16si_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_narrow_clipuvnx16si_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_narrow_clipvnx1di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_narrow_clipuvnx1di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_narrow_clipvnx2di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_narrow_clipuvnx2di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_narrow_clipvnx4di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_narrow_clipuvnx4di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_narrow_clipvnx8di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_narrow_clipuvnx8di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_widen_mul_plussvnx1hi (TARGET_VECTOR)
#define HAVE_pred_widen_mul_plusuvnx1hi (TARGET_VECTOR)
#define HAVE_pred_widen_mul_plussvnx2hi (TARGET_VECTOR)
#define HAVE_pred_widen_mul_plusuvnx2hi (TARGET_VECTOR)
#define HAVE_pred_widen_mul_plussvnx4hi (TARGET_VECTOR)
#define HAVE_pred_widen_mul_plusuvnx4hi (TARGET_VECTOR)
#define HAVE_pred_widen_mul_plussvnx8hi (TARGET_VECTOR)
#define HAVE_pred_widen_mul_plusuvnx8hi (TARGET_VECTOR)
#define HAVE_pred_widen_mul_plussvnx16hi (TARGET_VECTOR)
#define HAVE_pred_widen_mul_plusuvnx16hi (TARGET_VECTOR)
#define HAVE_pred_widen_mul_plussvnx32hi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_widen_mul_plusuvnx32hi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_widen_mul_plussvnx1si (TARGET_VECTOR)
#define HAVE_pred_widen_mul_plusuvnx1si (TARGET_VECTOR)
#define HAVE_pred_widen_mul_plussvnx2si (TARGET_VECTOR)
#define HAVE_pred_widen_mul_plusuvnx2si (TARGET_VECTOR)
#define HAVE_pred_widen_mul_plussvnx4si (TARGET_VECTOR)
#define HAVE_pred_widen_mul_plusuvnx4si (TARGET_VECTOR)
#define HAVE_pred_widen_mul_plussvnx8si (TARGET_VECTOR)
#define HAVE_pred_widen_mul_plusuvnx8si (TARGET_VECTOR)
#define HAVE_pred_widen_mul_plussvnx16si ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_widen_mul_plusuvnx16si ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_widen_mul_plussvnx1di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_widen_mul_plusuvnx1di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_widen_mul_plussvnx2di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_widen_mul_plusuvnx2di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_widen_mul_plussvnx4di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_widen_mul_plusuvnx4di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_widen_mul_plussvnx8di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_widen_mul_plusuvnx8di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_widen_mul_plussvnx1hi_scalar (TARGET_VECTOR)
#define HAVE_pred_widen_mul_plusuvnx1hi_scalar (TARGET_VECTOR)
#define HAVE_pred_widen_mul_plussvnx2hi_scalar (TARGET_VECTOR)
#define HAVE_pred_widen_mul_plusuvnx2hi_scalar (TARGET_VECTOR)
#define HAVE_pred_widen_mul_plussvnx4hi_scalar (TARGET_VECTOR)
#define HAVE_pred_widen_mul_plusuvnx4hi_scalar (TARGET_VECTOR)
#define HAVE_pred_widen_mul_plussvnx8hi_scalar (TARGET_VECTOR)
#define HAVE_pred_widen_mul_plusuvnx8hi_scalar (TARGET_VECTOR)
#define HAVE_pred_widen_mul_plussvnx16hi_scalar (TARGET_VECTOR)
#define HAVE_pred_widen_mul_plusuvnx16hi_scalar (TARGET_VECTOR)
#define HAVE_pred_widen_mul_plussvnx32hi_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_widen_mul_plusuvnx32hi_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_widen_mul_plussvnx1si_scalar (TARGET_VECTOR)
#define HAVE_pred_widen_mul_plusuvnx1si_scalar (TARGET_VECTOR)
#define HAVE_pred_widen_mul_plussvnx2si_scalar (TARGET_VECTOR)
#define HAVE_pred_widen_mul_plusuvnx2si_scalar (TARGET_VECTOR)
#define HAVE_pred_widen_mul_plussvnx4si_scalar (TARGET_VECTOR)
#define HAVE_pred_widen_mul_plusuvnx4si_scalar (TARGET_VECTOR)
#define HAVE_pred_widen_mul_plussvnx8si_scalar (TARGET_VECTOR)
#define HAVE_pred_widen_mul_plusuvnx8si_scalar (TARGET_VECTOR)
#define HAVE_pred_widen_mul_plussvnx16si_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_widen_mul_plusuvnx16si_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_widen_mul_plussvnx1di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_widen_mul_plusuvnx1di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_widen_mul_plussvnx2di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_widen_mul_plusuvnx2di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_widen_mul_plussvnx4di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_widen_mul_plusuvnx4di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_widen_mul_plussvnx8di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_widen_mul_plusuvnx8di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_widen_mul_plussuvnx1hi (TARGET_VECTOR)
#define HAVE_pred_widen_mul_plussuvnx2hi (TARGET_VECTOR)
#define HAVE_pred_widen_mul_plussuvnx4hi (TARGET_VECTOR)
#define HAVE_pred_widen_mul_plussuvnx8hi (TARGET_VECTOR)
#define HAVE_pred_widen_mul_plussuvnx16hi (TARGET_VECTOR)
#define HAVE_pred_widen_mul_plussuvnx32hi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_widen_mul_plussuvnx1si (TARGET_VECTOR)
#define HAVE_pred_widen_mul_plussuvnx2si (TARGET_VECTOR)
#define HAVE_pred_widen_mul_plussuvnx4si (TARGET_VECTOR)
#define HAVE_pred_widen_mul_plussuvnx8si (TARGET_VECTOR)
#define HAVE_pred_widen_mul_plussuvnx16si ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_widen_mul_plussuvnx1di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_widen_mul_plussuvnx2di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_widen_mul_plussuvnx4di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_widen_mul_plussuvnx8di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_widen_mul_plussuvnx1hi_scalar (TARGET_VECTOR)
#define HAVE_pred_widen_mul_plussuvnx2hi_scalar (TARGET_VECTOR)
#define HAVE_pred_widen_mul_plussuvnx4hi_scalar (TARGET_VECTOR)
#define HAVE_pred_widen_mul_plussuvnx8hi_scalar (TARGET_VECTOR)
#define HAVE_pred_widen_mul_plussuvnx16hi_scalar (TARGET_VECTOR)
#define HAVE_pred_widen_mul_plussuvnx32hi_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_widen_mul_plussuvnx1si_scalar (TARGET_VECTOR)
#define HAVE_pred_widen_mul_plussuvnx2si_scalar (TARGET_VECTOR)
#define HAVE_pred_widen_mul_plussuvnx4si_scalar (TARGET_VECTOR)
#define HAVE_pred_widen_mul_plussuvnx8si_scalar (TARGET_VECTOR)
#define HAVE_pred_widen_mul_plussuvnx16si_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_widen_mul_plussuvnx1di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_widen_mul_plussuvnx2di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_widen_mul_plussuvnx4di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_widen_mul_plussuvnx8di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_widen_mul_plususvnx1hi_scalar (TARGET_VECTOR)
#define HAVE_pred_widen_mul_plususvnx2hi_scalar (TARGET_VECTOR)
#define HAVE_pred_widen_mul_plususvnx4hi_scalar (TARGET_VECTOR)
#define HAVE_pred_widen_mul_plususvnx8hi_scalar (TARGET_VECTOR)
#define HAVE_pred_widen_mul_plususvnx16hi_scalar (TARGET_VECTOR)
#define HAVE_pred_widen_mul_plususvnx32hi_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_widen_mul_plususvnx1si_scalar (TARGET_VECTOR)
#define HAVE_pred_widen_mul_plususvnx2si_scalar (TARGET_VECTOR)
#define HAVE_pred_widen_mul_plususvnx4si_scalar (TARGET_VECTOR)
#define HAVE_pred_widen_mul_plususvnx8si_scalar (TARGET_VECTOR)
#define HAVE_pred_widen_mul_plususvnx16si_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_widen_mul_plususvnx1di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_widen_mul_plususvnx2di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_widen_mul_plususvnx4di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_widen_mul_plususvnx8di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_andvnx1bi (TARGET_VECTOR)
#define HAVE_pred_iorvnx1bi (TARGET_VECTOR)
#define HAVE_pred_xorvnx1bi (TARGET_VECTOR)
#define HAVE_pred_andvnx2bi (TARGET_VECTOR)
#define HAVE_pred_iorvnx2bi (TARGET_VECTOR)
#define HAVE_pred_xorvnx2bi (TARGET_VECTOR)
#define HAVE_pred_andvnx4bi (TARGET_VECTOR)
#define HAVE_pred_iorvnx4bi (TARGET_VECTOR)
#define HAVE_pred_xorvnx4bi (TARGET_VECTOR)
#define HAVE_pred_andvnx8bi (TARGET_VECTOR)
#define HAVE_pred_iorvnx8bi (TARGET_VECTOR)
#define HAVE_pred_xorvnx8bi (TARGET_VECTOR)
#define HAVE_pred_andvnx16bi (TARGET_VECTOR)
#define HAVE_pred_iorvnx16bi (TARGET_VECTOR)
#define HAVE_pred_xorvnx16bi (TARGET_VECTOR)
#define HAVE_pred_andvnx32bi (TARGET_VECTOR)
#define HAVE_pred_iorvnx32bi (TARGET_VECTOR)
#define HAVE_pred_xorvnx32bi (TARGET_VECTOR)
#define HAVE_pred_andvnx64bi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_iorvnx64bi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_xorvnx64bi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_nandvnx1bi (TARGET_VECTOR)
#define HAVE_pred_niorvnx1bi (TARGET_VECTOR)
#define HAVE_pred_nxorvnx1bi (TARGET_VECTOR)
#define HAVE_pred_nandvnx2bi (TARGET_VECTOR)
#define HAVE_pred_niorvnx2bi (TARGET_VECTOR)
#define HAVE_pred_nxorvnx2bi (TARGET_VECTOR)
#define HAVE_pred_nandvnx4bi (TARGET_VECTOR)
#define HAVE_pred_niorvnx4bi (TARGET_VECTOR)
#define HAVE_pred_nxorvnx4bi (TARGET_VECTOR)
#define HAVE_pred_nandvnx8bi (TARGET_VECTOR)
#define HAVE_pred_niorvnx8bi (TARGET_VECTOR)
#define HAVE_pred_nxorvnx8bi (TARGET_VECTOR)
#define HAVE_pred_nandvnx16bi (TARGET_VECTOR)
#define HAVE_pred_niorvnx16bi (TARGET_VECTOR)
#define HAVE_pred_nxorvnx16bi (TARGET_VECTOR)
#define HAVE_pred_nandvnx32bi (TARGET_VECTOR)
#define HAVE_pred_niorvnx32bi (TARGET_VECTOR)
#define HAVE_pred_nxorvnx32bi (TARGET_VECTOR)
#define HAVE_pred_nandvnx64bi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_niorvnx64bi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_nxorvnx64bi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_andnotvnx1bi (TARGET_VECTOR)
#define HAVE_pred_iornotvnx1bi (TARGET_VECTOR)
#define HAVE_pred_andnotvnx2bi (TARGET_VECTOR)
#define HAVE_pred_iornotvnx2bi (TARGET_VECTOR)
#define HAVE_pred_andnotvnx4bi (TARGET_VECTOR)
#define HAVE_pred_iornotvnx4bi (TARGET_VECTOR)
#define HAVE_pred_andnotvnx8bi (TARGET_VECTOR)
#define HAVE_pred_iornotvnx8bi (TARGET_VECTOR)
#define HAVE_pred_andnotvnx16bi (TARGET_VECTOR)
#define HAVE_pred_iornotvnx16bi (TARGET_VECTOR)
#define HAVE_pred_andnotvnx32bi (TARGET_VECTOR)
#define HAVE_pred_iornotvnx32bi (TARGET_VECTOR)
#define HAVE_pred_andnotvnx64bi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_iornotvnx64bi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_notvnx1bi (TARGET_VECTOR)
#define HAVE_pred_notvnx2bi (TARGET_VECTOR)
#define HAVE_pred_notvnx4bi (TARGET_VECTOR)
#define HAVE_pred_notvnx8bi (TARGET_VECTOR)
#define HAVE_pred_notvnx16bi (TARGET_VECTOR)
#define HAVE_pred_notvnx32bi (TARGET_VECTOR)
#define HAVE_pred_notvnx64bi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_popcountvnx1bisi ((TARGET_VECTOR) && (Pmode == SImode))
#define HAVE_pred_popcountvnx2bisi ((TARGET_VECTOR) && (Pmode == SImode))
#define HAVE_pred_popcountvnx4bisi ((TARGET_VECTOR) && (Pmode == SImode))
#define HAVE_pred_popcountvnx8bisi ((TARGET_VECTOR) && (Pmode == SImode))
#define HAVE_pred_popcountvnx16bisi ((TARGET_VECTOR) && (Pmode == SImode))
#define HAVE_pred_popcountvnx32bisi ((TARGET_VECTOR) && (Pmode == SImode))
#define HAVE_pred_popcountvnx64bisi ((TARGET_VECTOR) && (((((Pmode == SImode) && (TARGET_MIN_VLEN > 32)) && (TARGET_MIN_VLEN > 32)) && (TARGET_MIN_VLEN > 32)) && (TARGET_MIN_VLEN > 32)))
#define HAVE_pred_popcountvnx1bidi ((TARGET_VECTOR) && (Pmode == DImode))
#define HAVE_pred_popcountvnx2bidi ((TARGET_VECTOR) && (Pmode == DImode))
#define HAVE_pred_popcountvnx4bidi ((TARGET_VECTOR) && (Pmode == DImode))
#define HAVE_pred_popcountvnx8bidi ((TARGET_VECTOR) && (Pmode == DImode))
#define HAVE_pred_popcountvnx16bidi ((TARGET_VECTOR) && (Pmode == DImode))
#define HAVE_pred_popcountvnx32bidi ((TARGET_VECTOR) && (Pmode == DImode))
#define HAVE_pred_popcountvnx64bidi ((TARGET_VECTOR) && (((((Pmode == DImode) && (TARGET_MIN_VLEN > 32)) && (TARGET_MIN_VLEN > 32)) && (TARGET_MIN_VLEN > 32)) && (TARGET_MIN_VLEN > 32)))
#define HAVE_pred_ffsvnx1bisi ((TARGET_VECTOR) && (Pmode == SImode))
#define HAVE_pred_ffsvnx2bisi ((TARGET_VECTOR) && (Pmode == SImode))
#define HAVE_pred_ffsvnx4bisi ((TARGET_VECTOR) && (Pmode == SImode))
#define HAVE_pred_ffsvnx8bisi ((TARGET_VECTOR) && (Pmode == SImode))
#define HAVE_pred_ffsvnx16bisi ((TARGET_VECTOR) && (Pmode == SImode))
#define HAVE_pred_ffsvnx32bisi ((TARGET_VECTOR) && (Pmode == SImode))
#define HAVE_pred_ffsvnx64bisi ((TARGET_VECTOR) && (((((Pmode == SImode) && (TARGET_MIN_VLEN > 32)) && (TARGET_MIN_VLEN > 32)) && (TARGET_MIN_VLEN > 32)) && (TARGET_MIN_VLEN > 32)))
#define HAVE_pred_ffsvnx1bidi ((TARGET_VECTOR) && (Pmode == DImode))
#define HAVE_pred_ffsvnx2bidi ((TARGET_VECTOR) && (Pmode == DImode))
#define HAVE_pred_ffsvnx4bidi ((TARGET_VECTOR) && (Pmode == DImode))
#define HAVE_pred_ffsvnx8bidi ((TARGET_VECTOR) && (Pmode == DImode))
#define HAVE_pred_ffsvnx16bidi ((TARGET_VECTOR) && (Pmode == DImode))
#define HAVE_pred_ffsvnx32bidi ((TARGET_VECTOR) && (Pmode == DImode))
#define HAVE_pred_ffsvnx64bidi ((TARGET_VECTOR) && (((((Pmode == DImode) && (TARGET_MIN_VLEN > 32)) && (TARGET_MIN_VLEN > 32)) && (TARGET_MIN_VLEN > 32)) && (TARGET_MIN_VLEN > 32)))
#define HAVE_pred_sbfvnx1bi (TARGET_VECTOR)
#define HAVE_pred_sifvnx1bi (TARGET_VECTOR)
#define HAVE_pred_sofvnx1bi (TARGET_VECTOR)
#define HAVE_pred_sbfvnx2bi (TARGET_VECTOR)
#define HAVE_pred_sifvnx2bi (TARGET_VECTOR)
#define HAVE_pred_sofvnx2bi (TARGET_VECTOR)
#define HAVE_pred_sbfvnx4bi (TARGET_VECTOR)
#define HAVE_pred_sifvnx4bi (TARGET_VECTOR)
#define HAVE_pred_sofvnx4bi (TARGET_VECTOR)
#define HAVE_pred_sbfvnx8bi (TARGET_VECTOR)
#define HAVE_pred_sifvnx8bi (TARGET_VECTOR)
#define HAVE_pred_sofvnx8bi (TARGET_VECTOR)
#define HAVE_pred_sbfvnx16bi (TARGET_VECTOR)
#define HAVE_pred_sifvnx16bi (TARGET_VECTOR)
#define HAVE_pred_sofvnx16bi (TARGET_VECTOR)
#define HAVE_pred_sbfvnx32bi (TARGET_VECTOR)
#define HAVE_pred_sifvnx32bi (TARGET_VECTOR)
#define HAVE_pred_sofvnx32bi (TARGET_VECTOR)
#define HAVE_pred_sbfvnx64bi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_sifvnx64bi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_sofvnx64bi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_iotavnx1qi (TARGET_VECTOR)
#define HAVE_pred_iotavnx2qi (TARGET_VECTOR)
#define HAVE_pred_iotavnx4qi (TARGET_VECTOR)
#define HAVE_pred_iotavnx8qi (TARGET_VECTOR)
#define HAVE_pred_iotavnx16qi (TARGET_VECTOR)
#define HAVE_pred_iotavnx32qi (TARGET_VECTOR)
#define HAVE_pred_iotavnx64qi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_iotavnx1hi (TARGET_VECTOR)
#define HAVE_pred_iotavnx2hi (TARGET_VECTOR)
#define HAVE_pred_iotavnx4hi (TARGET_VECTOR)
#define HAVE_pred_iotavnx8hi (TARGET_VECTOR)
#define HAVE_pred_iotavnx16hi (TARGET_VECTOR)
#define HAVE_pred_iotavnx32hi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_iotavnx1si (TARGET_VECTOR)
#define HAVE_pred_iotavnx2si (TARGET_VECTOR)
#define HAVE_pred_iotavnx4si (TARGET_VECTOR)
#define HAVE_pred_iotavnx8si (TARGET_VECTOR)
#define HAVE_pred_iotavnx16si ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_iotavnx1di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_iotavnx2di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_iotavnx4di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_iotavnx8di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_seriesvnx1qi (TARGET_VECTOR)
#define HAVE_pred_seriesvnx2qi (TARGET_VECTOR)
#define HAVE_pred_seriesvnx4qi (TARGET_VECTOR)
#define HAVE_pred_seriesvnx8qi (TARGET_VECTOR)
#define HAVE_pred_seriesvnx16qi (TARGET_VECTOR)
#define HAVE_pred_seriesvnx32qi (TARGET_VECTOR)
#define HAVE_pred_seriesvnx64qi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_seriesvnx1hi (TARGET_VECTOR)
#define HAVE_pred_seriesvnx2hi (TARGET_VECTOR)
#define HAVE_pred_seriesvnx4hi (TARGET_VECTOR)
#define HAVE_pred_seriesvnx8hi (TARGET_VECTOR)
#define HAVE_pred_seriesvnx16hi (TARGET_VECTOR)
#define HAVE_pred_seriesvnx32hi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_seriesvnx1si (TARGET_VECTOR)
#define HAVE_pred_seriesvnx2si (TARGET_VECTOR)
#define HAVE_pred_seriesvnx4si (TARGET_VECTOR)
#define HAVE_pred_seriesvnx8si (TARGET_VECTOR)
#define HAVE_pred_seriesvnx16si ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_seriesvnx1di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_seriesvnx2di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_seriesvnx4di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_seriesvnx8di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_addvnx1sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_mulvnx1sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_smaxvnx1sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_sminvnx1sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_subvnx1sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_divvnx1sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_addvnx2sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_mulvnx2sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_smaxvnx2sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_sminvnx2sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_subvnx2sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_divvnx2sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_addvnx4sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_mulvnx4sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_smaxvnx4sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_sminvnx4sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_subvnx4sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_divvnx4sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_addvnx8sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_mulvnx8sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_smaxvnx8sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_sminvnx8sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_subvnx8sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_divvnx8sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_addvnx16sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32 && TARGET_MIN_VLEN > 32))
#define HAVE_pred_mulvnx16sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32 && TARGET_MIN_VLEN > 32))
#define HAVE_pred_smaxvnx16sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32 && TARGET_MIN_VLEN > 32))
#define HAVE_pred_sminvnx16sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32 && TARGET_MIN_VLEN > 32))
#define HAVE_pred_subvnx16sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32 && TARGET_MIN_VLEN > 32))
#define HAVE_pred_divvnx16sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32 && TARGET_MIN_VLEN > 32))
#define HAVE_pred_addvnx1df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_mulvnx1df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_smaxvnx1df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_sminvnx1df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_subvnx1df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_divvnx1df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_addvnx2df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_mulvnx2df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_smaxvnx2df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_sminvnx2df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_subvnx2df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_divvnx2df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_addvnx4df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_mulvnx4df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_smaxvnx4df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_sminvnx4df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_subvnx4df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_divvnx4df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_addvnx8df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_mulvnx8df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_smaxvnx8df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_sminvnx8df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_subvnx8df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_divvnx8df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_addvnx1sf_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_mulvnx1sf_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_smaxvnx1sf_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_sminvnx1sf_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_addvnx2sf_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_mulvnx2sf_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_smaxvnx2sf_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_sminvnx2sf_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_addvnx4sf_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_mulvnx4sf_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_smaxvnx4sf_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_sminvnx4sf_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_addvnx8sf_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_mulvnx8sf_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_smaxvnx8sf_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_sminvnx8sf_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_addvnx16sf_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32 && TARGET_MIN_VLEN > 32))
#define HAVE_pred_mulvnx16sf_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32 && TARGET_MIN_VLEN > 32))
#define HAVE_pred_smaxvnx16sf_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32 && TARGET_MIN_VLEN > 32))
#define HAVE_pred_sminvnx16sf_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32 && TARGET_MIN_VLEN > 32))
#define HAVE_pred_addvnx1df_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_mulvnx1df_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_smaxvnx1df_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_sminvnx1df_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_addvnx2df_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_mulvnx2df_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_smaxvnx2df_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_sminvnx2df_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_addvnx4df_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_mulvnx4df_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_smaxvnx4df_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_sminvnx4df_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_addvnx8df_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_mulvnx8df_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_smaxvnx8df_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_sminvnx8df_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_subvnx1sf_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_divvnx1sf_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_subvnx2sf_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_divvnx2sf_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_subvnx4sf_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_divvnx4sf_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_subvnx8sf_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_divvnx8sf_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_subvnx16sf_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32 && TARGET_MIN_VLEN > 32))
#define HAVE_pred_divvnx16sf_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32 && TARGET_MIN_VLEN > 32))
#define HAVE_pred_subvnx1df_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_divvnx1df_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_subvnx2df_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_divvnx2df_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_subvnx4df_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_divvnx4df_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_subvnx8df_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_divvnx8df_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_subvnx1sf_reverse_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_divvnx1sf_reverse_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_subvnx2sf_reverse_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_divvnx2sf_reverse_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_subvnx4sf_reverse_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_divvnx4sf_reverse_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_subvnx8sf_reverse_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_divvnx8sf_reverse_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_subvnx16sf_reverse_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32 && TARGET_MIN_VLEN > 32))
#define HAVE_pred_divvnx16sf_reverse_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32 && TARGET_MIN_VLEN > 32))
#define HAVE_pred_subvnx1df_reverse_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_divvnx1df_reverse_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_subvnx2df_reverse_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_divvnx2df_reverse_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_subvnx4df_reverse_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_divvnx4df_reverse_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_subvnx8df_reverse_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_divvnx8df_reverse_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_copysignvnx1sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_ncopysignvnx1sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_xorsignvnx1sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_copysignvnx2sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_ncopysignvnx2sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_xorsignvnx2sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_copysignvnx4sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_ncopysignvnx4sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_xorsignvnx4sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_copysignvnx8sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_ncopysignvnx8sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_xorsignvnx8sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_copysignvnx16sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32 && TARGET_MIN_VLEN > 32))
#define HAVE_pred_ncopysignvnx16sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32 && TARGET_MIN_VLEN > 32))
#define HAVE_pred_xorsignvnx16sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32 && TARGET_MIN_VLEN > 32))
#define HAVE_pred_copysignvnx1df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_ncopysignvnx1df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_xorsignvnx1df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_copysignvnx2df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_ncopysignvnx2df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_xorsignvnx2df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_copysignvnx4df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_ncopysignvnx4df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_xorsignvnx4df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_copysignvnx8df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_ncopysignvnx8df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_xorsignvnx8df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_copysignvnx1sf_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_ncopysignvnx1sf_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_xorsignvnx1sf_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_copysignvnx2sf_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_ncopysignvnx2sf_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_xorsignvnx2sf_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_copysignvnx4sf_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_ncopysignvnx4sf_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_xorsignvnx4sf_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_copysignvnx8sf_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_ncopysignvnx8sf_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_xorsignvnx8sf_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_copysignvnx16sf_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32 && TARGET_MIN_VLEN > 32))
#define HAVE_pred_ncopysignvnx16sf_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32 && TARGET_MIN_VLEN > 32))
#define HAVE_pred_xorsignvnx16sf_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32 && TARGET_MIN_VLEN > 32))
#define HAVE_pred_copysignvnx1df_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_ncopysignvnx1df_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_xorsignvnx1df_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_copysignvnx2df_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_ncopysignvnx2df_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_xorsignvnx2df_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_copysignvnx4df_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_ncopysignvnx4df_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_xorsignvnx4df_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_copysignvnx8df_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_ncopysignvnx8df_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_xorsignvnx8df_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_negvnx1sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_absvnx1sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_sqrtvnx1sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_negvnx2sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_absvnx2sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_sqrtvnx2sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_negvnx4sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_absvnx4sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_sqrtvnx4sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_negvnx8sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_absvnx8sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_sqrtvnx8sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_negvnx16sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32 && TARGET_MIN_VLEN > 32))
#define HAVE_pred_absvnx16sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32 && TARGET_MIN_VLEN > 32))
#define HAVE_pred_sqrtvnx16sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32 && TARGET_MIN_VLEN > 32))
#define HAVE_pred_negvnx1df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_absvnx1df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_sqrtvnx1df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_negvnx2df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_absvnx2df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_sqrtvnx2df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_negvnx4df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_absvnx4df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_sqrtvnx4df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_negvnx8df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_absvnx8df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_sqrtvnx8df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_rsqrt7vnx1sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_rec7vnx1sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_rsqrt7vnx2sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_rec7vnx2sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_rsqrt7vnx4sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_rec7vnx4sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_rsqrt7vnx8sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_rec7vnx8sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_rsqrt7vnx16sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32 && TARGET_MIN_VLEN > 32))
#define HAVE_pred_rec7vnx16sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32 && TARGET_MIN_VLEN > 32))
#define HAVE_pred_rsqrt7vnx1df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_rec7vnx1df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_rsqrt7vnx2df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_rec7vnx2df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_rsqrt7vnx4df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_rec7vnx4df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_rsqrt7vnx8df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_rec7vnx8df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_classvnx1sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_classvnx2sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_classvnx4sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_classvnx8sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_classvnx16sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32 && TARGET_MIN_VLEN > 32))
#define HAVE_pred_classvnx1df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_classvnx2df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_classvnx4df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_classvnx8df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_dual_widen_addvnx1df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_dual_widen_subvnx1df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_dual_widen_mulvnx1df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_dual_widen_addvnx2df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_dual_widen_subvnx2df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_dual_widen_mulvnx2df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_dual_widen_addvnx4df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_dual_widen_subvnx4df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_dual_widen_mulvnx4df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_dual_widen_addvnx8df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_dual_widen_subvnx8df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_dual_widen_mulvnx8df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_dual_widen_addvnx1df_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_dual_widen_subvnx1df_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_dual_widen_mulvnx1df_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_dual_widen_addvnx2df_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_dual_widen_subvnx2df_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_dual_widen_mulvnx2df_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_dual_widen_addvnx4df_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_dual_widen_subvnx4df_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_dual_widen_mulvnx4df_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_dual_widen_addvnx8df_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_dual_widen_subvnx8df_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_dual_widen_mulvnx8df_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_single_widen_addvnx1df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_single_widen_subvnx1df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_single_widen_addvnx2df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_single_widen_subvnx2df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_single_widen_addvnx4df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_single_widen_subvnx4df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_single_widen_addvnx8df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_single_widen_subvnx8df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_single_widen_addvnx1df_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_single_widen_subvnx1df_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_single_widen_addvnx2df_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_single_widen_subvnx2df_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_single_widen_addvnx4df_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_single_widen_subvnx4df_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_single_widen_addvnx8df_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_single_widen_subvnx8df_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_widen_mul_addvnx1df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_widen_mul_subvnx1df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_widen_mul_addvnx2df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_widen_mul_subvnx2df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_widen_mul_addvnx4df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_widen_mul_subvnx4df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_widen_mul_addvnx8df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_widen_mul_subvnx8df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_widen_mul_addvnx1df_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_widen_mul_subvnx1df_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_widen_mul_addvnx2df_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_widen_mul_subvnx2df_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_widen_mul_addvnx4df_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_widen_mul_subvnx4df_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_widen_mul_addvnx8df_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_widen_mul_subvnx8df_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_widen_mul_neg_addvnx1df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_widen_mul_neg_subvnx1df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_widen_mul_neg_addvnx2df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_widen_mul_neg_subvnx2df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_widen_mul_neg_addvnx4df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_widen_mul_neg_subvnx4df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_widen_mul_neg_addvnx8df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_widen_mul_neg_subvnx8df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_widen_mul_neg_addvnx1df_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_widen_mul_neg_subvnx1df_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_widen_mul_neg_addvnx2df_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_widen_mul_neg_subvnx2df_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_widen_mul_neg_addvnx4df_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_widen_mul_neg_subvnx4df_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_widen_mul_neg_addvnx8df_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_widen_mul_neg_subvnx8df_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_mergevnx1sf_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_mergevnx2sf_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_mergevnx4sf_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_mergevnx8sf_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_mergevnx16sf_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32 && TARGET_MIN_VLEN > 32))
#define HAVE_pred_mergevnx1df_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_mergevnx2df_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_mergevnx4df_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_mergevnx8df_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_fcvt_x_fvnx1sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_fcvt_xu_fvnx1sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_fcvt_x_fvnx2sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_fcvt_xu_fvnx2sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_fcvt_x_fvnx4sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_fcvt_xu_fvnx4sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_fcvt_x_fvnx8sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_fcvt_xu_fvnx8sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_fcvt_x_fvnx16sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32 && TARGET_MIN_VLEN > 32))
#define HAVE_pred_fcvt_xu_fvnx16sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32 && TARGET_MIN_VLEN > 32))
#define HAVE_pred_fcvt_x_fvnx1df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_fcvt_xu_fvnx1df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_fcvt_x_fvnx2df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_fcvt_xu_fvnx2df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_fcvt_x_fvnx4df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_fcvt_xu_fvnx4df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_fcvt_x_fvnx8df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_fcvt_xu_fvnx8df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_fix_truncvnx1sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_fixuns_truncvnx1sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_fix_truncvnx2sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_fixuns_truncvnx2sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_fix_truncvnx4sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_fixuns_truncvnx4sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_fix_truncvnx8sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_fixuns_truncvnx8sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_fix_truncvnx16sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32 && TARGET_MIN_VLEN > 32))
#define HAVE_pred_fixuns_truncvnx16sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32 && TARGET_MIN_VLEN > 32))
#define HAVE_pred_fix_truncvnx1df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_fixuns_truncvnx1df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_fix_truncvnx2df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_fixuns_truncvnx2df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_fix_truncvnx4df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_fixuns_truncvnx4df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_fix_truncvnx8df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_fixuns_truncvnx8df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_floatvnx1sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_floatunsvnx1sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_floatvnx2sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_floatunsvnx2sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_floatvnx4sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_floatunsvnx4sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_floatvnx8sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_floatunsvnx8sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_floatvnx16sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32 && TARGET_MIN_VLEN > 32))
#define HAVE_pred_floatunsvnx16sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32 && TARGET_MIN_VLEN > 32))
#define HAVE_pred_floatvnx1df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_floatunsvnx1df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_floatvnx2df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_floatunsvnx2df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_floatvnx4df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_floatunsvnx4df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_floatvnx8df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_floatunsvnx8df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_widen_fcvt_x_fvnx1di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64 && TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_widen_fcvt_xu_fvnx1di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64 && TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_widen_fcvt_x_fvnx2di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64 && TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_widen_fcvt_xu_fvnx2di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64 && TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_widen_fcvt_x_fvnx4di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64 && TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_widen_fcvt_xu_fvnx4di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64 && TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_widen_fcvt_x_fvnx8di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64 && TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_widen_fcvt_xu_fvnx8di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64 && TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_widen_fix_truncvnx1di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64 && TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_widen_fixuns_truncvnx1di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64 && TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_widen_fix_truncvnx2di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64 && TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_widen_fixuns_truncvnx2di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64 && TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_widen_fix_truncvnx4di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64 && TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_widen_fixuns_truncvnx4di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64 && TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_widen_fix_truncvnx8di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64 && TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_widen_fixuns_truncvnx8di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64 && TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_widen_floatvnx1sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_widen_floatunsvnx1sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_widen_floatvnx2sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_widen_floatunsvnx2sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_widen_floatvnx4sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_widen_floatunsvnx4sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_widen_floatvnx8sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_widen_floatunsvnx8sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_widen_floatvnx16sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32 && TARGET_MIN_VLEN > 32))
#define HAVE_pred_widen_floatunsvnx16sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32 && TARGET_MIN_VLEN > 32))
#define HAVE_pred_widen_floatvnx1df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_widen_floatunsvnx1df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_widen_floatvnx2df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_widen_floatunsvnx2df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_widen_floatvnx4df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_widen_floatunsvnx4df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_widen_floatvnx8df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_widen_floatunsvnx8df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_extendvnx1df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_extendvnx2df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_extendvnx4df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_extendvnx8df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_narrow_fcvt_x_fvnx1sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_narrow_fcvt_xu_fvnx1sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_narrow_fcvt_x_fvnx2sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_narrow_fcvt_xu_fvnx2sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_narrow_fcvt_x_fvnx4sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_narrow_fcvt_xu_fvnx4sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_narrow_fcvt_x_fvnx8sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_narrow_fcvt_xu_fvnx8sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_narrow_fcvt_x_fvnx16sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32 && TARGET_MIN_VLEN > 32))
#define HAVE_pred_narrow_fcvt_xu_fvnx16sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32 && TARGET_MIN_VLEN > 32))
#define HAVE_pred_narrow_fcvt_x_fvnx1df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_narrow_fcvt_xu_fvnx1df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_narrow_fcvt_x_fvnx2df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_narrow_fcvt_xu_fvnx2df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_narrow_fcvt_x_fvnx4df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_narrow_fcvt_xu_fvnx4df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_narrow_fcvt_x_fvnx8df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_narrow_fcvt_xu_fvnx8df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_narrow_fix_truncvnx1sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_narrow_fixuns_truncvnx1sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_narrow_fix_truncvnx2sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_narrow_fixuns_truncvnx2sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_narrow_fix_truncvnx4sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_narrow_fixuns_truncvnx4sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_narrow_fix_truncvnx8sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_narrow_fixuns_truncvnx8sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_narrow_fix_truncvnx16sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32 && TARGET_MIN_VLEN > 32))
#define HAVE_pred_narrow_fixuns_truncvnx16sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32 && TARGET_MIN_VLEN > 32))
#define HAVE_pred_narrow_fix_truncvnx1df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_narrow_fixuns_truncvnx1df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_narrow_fix_truncvnx2df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_narrow_fixuns_truncvnx2df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_narrow_fix_truncvnx4df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_narrow_fixuns_truncvnx4df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_narrow_fix_truncvnx8df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_narrow_fixuns_truncvnx8df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_narrow_floatvnx1di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64 && TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_narrow_floatunsvnx1di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64 && TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_narrow_floatvnx2di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64 && TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_narrow_floatunsvnx2di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64 && TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_narrow_floatvnx4di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64 && TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_narrow_floatunsvnx4di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64 && TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_narrow_floatvnx8di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64 && TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_narrow_floatunsvnx8di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64 && TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_truncvnx1df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_truncvnx2df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_truncvnx4df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_truncvnx8df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_rod_truncvnx1df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_rod_truncvnx2df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_rod_truncvnx4df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_rod_truncvnx8df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_reduc_sumvnx1qivnx8qi (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_reduc_maxuvnx1qivnx8qi (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_reduc_maxvnx1qivnx8qi (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_reduc_minuvnx1qivnx8qi (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_reduc_minvnx1qivnx8qi (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_reduc_andvnx1qivnx8qi (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_reduc_orvnx1qivnx8qi (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_reduc_xorvnx1qivnx8qi (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_reduc_sumvnx2qivnx8qi (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_reduc_maxuvnx2qivnx8qi (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_reduc_maxvnx2qivnx8qi (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_reduc_minuvnx2qivnx8qi (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_reduc_minvnx2qivnx8qi (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_reduc_andvnx2qivnx8qi (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_reduc_orvnx2qivnx8qi (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_reduc_xorvnx2qivnx8qi (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_reduc_sumvnx4qivnx8qi (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_reduc_maxuvnx4qivnx8qi (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_reduc_maxvnx4qivnx8qi (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_reduc_minuvnx4qivnx8qi (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_reduc_minvnx4qivnx8qi (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_reduc_andvnx4qivnx8qi (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_reduc_orvnx4qivnx8qi (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_reduc_xorvnx4qivnx8qi (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_reduc_sumvnx8qivnx8qi (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_reduc_maxuvnx8qivnx8qi (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_reduc_maxvnx8qivnx8qi (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_reduc_minuvnx8qivnx8qi (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_reduc_minvnx8qivnx8qi (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_reduc_andvnx8qivnx8qi (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_reduc_orvnx8qivnx8qi (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_reduc_xorvnx8qivnx8qi (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_reduc_sumvnx16qivnx8qi (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_reduc_maxuvnx16qivnx8qi (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_reduc_maxvnx16qivnx8qi (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_reduc_minuvnx16qivnx8qi (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_reduc_minvnx16qivnx8qi (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_reduc_andvnx16qivnx8qi (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_reduc_orvnx16qivnx8qi (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_reduc_xorvnx16qivnx8qi (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_reduc_sumvnx32qivnx8qi (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_reduc_maxuvnx32qivnx8qi (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_reduc_maxvnx32qivnx8qi (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_reduc_minuvnx32qivnx8qi (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_reduc_minvnx32qivnx8qi (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_reduc_andvnx32qivnx8qi (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_reduc_orvnx32qivnx8qi (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_reduc_xorvnx32qivnx8qi (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_reduc_sumvnx64qivnx8qi ((TARGET_VECTOR && TARGET_MIN_VLEN > 32) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_reduc_maxuvnx64qivnx8qi ((TARGET_VECTOR && TARGET_MIN_VLEN > 32) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_reduc_maxvnx64qivnx8qi ((TARGET_VECTOR && TARGET_MIN_VLEN > 32) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_reduc_minuvnx64qivnx8qi ((TARGET_VECTOR && TARGET_MIN_VLEN > 32) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_reduc_minvnx64qivnx8qi ((TARGET_VECTOR && TARGET_MIN_VLEN > 32) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_reduc_andvnx64qivnx8qi ((TARGET_VECTOR && TARGET_MIN_VLEN > 32) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_reduc_orvnx64qivnx8qi ((TARGET_VECTOR && TARGET_MIN_VLEN > 32) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_reduc_xorvnx64qivnx8qi ((TARGET_VECTOR && TARGET_MIN_VLEN > 32) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_reduc_sumvnx1hivnx4hi (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_reduc_maxuvnx1hivnx4hi (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_reduc_maxvnx1hivnx4hi (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_reduc_minuvnx1hivnx4hi (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_reduc_minvnx1hivnx4hi (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_reduc_andvnx1hivnx4hi (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_reduc_orvnx1hivnx4hi (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_reduc_xorvnx1hivnx4hi (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_reduc_sumvnx2hivnx4hi (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_reduc_maxuvnx2hivnx4hi (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_reduc_maxvnx2hivnx4hi (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_reduc_minuvnx2hivnx4hi (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_reduc_minvnx2hivnx4hi (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_reduc_andvnx2hivnx4hi (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_reduc_orvnx2hivnx4hi (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_reduc_xorvnx2hivnx4hi (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_reduc_sumvnx4hivnx4hi (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_reduc_maxuvnx4hivnx4hi (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_reduc_maxvnx4hivnx4hi (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_reduc_minuvnx4hivnx4hi (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_reduc_minvnx4hivnx4hi (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_reduc_andvnx4hivnx4hi (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_reduc_orvnx4hivnx4hi (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_reduc_xorvnx4hivnx4hi (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_reduc_sumvnx8hivnx4hi (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_reduc_maxuvnx8hivnx4hi (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_reduc_maxvnx8hivnx4hi (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_reduc_minuvnx8hivnx4hi (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_reduc_minvnx8hivnx4hi (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_reduc_andvnx8hivnx4hi (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_reduc_orvnx8hivnx4hi (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_reduc_xorvnx8hivnx4hi (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_reduc_sumvnx16hivnx4hi (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_reduc_maxuvnx16hivnx4hi (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_reduc_maxvnx16hivnx4hi (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_reduc_minuvnx16hivnx4hi (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_reduc_minvnx16hivnx4hi (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_reduc_andvnx16hivnx4hi (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_reduc_orvnx16hivnx4hi (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_reduc_xorvnx16hivnx4hi (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_reduc_sumvnx32hivnx4hi ((TARGET_VECTOR && TARGET_MIN_VLEN > 32) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_reduc_maxuvnx32hivnx4hi ((TARGET_VECTOR && TARGET_MIN_VLEN > 32) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_reduc_maxvnx32hivnx4hi ((TARGET_VECTOR && TARGET_MIN_VLEN > 32) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_reduc_minuvnx32hivnx4hi ((TARGET_VECTOR && TARGET_MIN_VLEN > 32) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_reduc_minvnx32hivnx4hi ((TARGET_VECTOR && TARGET_MIN_VLEN > 32) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_reduc_andvnx32hivnx4hi ((TARGET_VECTOR && TARGET_MIN_VLEN > 32) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_reduc_orvnx32hivnx4hi ((TARGET_VECTOR && TARGET_MIN_VLEN > 32) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_reduc_xorvnx32hivnx4hi ((TARGET_VECTOR && TARGET_MIN_VLEN > 32) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_reduc_sumvnx1sivnx2si (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_reduc_maxuvnx1sivnx2si (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_reduc_maxvnx1sivnx2si (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_reduc_minuvnx1sivnx2si (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_reduc_minvnx1sivnx2si (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_reduc_andvnx1sivnx2si (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_reduc_orvnx1sivnx2si (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_reduc_xorvnx1sivnx2si (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_reduc_sumvnx2sivnx2si (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_reduc_maxuvnx2sivnx2si (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_reduc_maxvnx2sivnx2si (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_reduc_minuvnx2sivnx2si (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_reduc_minvnx2sivnx2si (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_reduc_andvnx2sivnx2si (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_reduc_orvnx2sivnx2si (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_reduc_xorvnx2sivnx2si (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_reduc_sumvnx4sivnx2si (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_reduc_maxuvnx4sivnx2si (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_reduc_maxvnx4sivnx2si (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_reduc_minuvnx4sivnx2si (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_reduc_minvnx4sivnx2si (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_reduc_andvnx4sivnx2si (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_reduc_orvnx4sivnx2si (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_reduc_xorvnx4sivnx2si (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_reduc_sumvnx8sivnx2si (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_reduc_maxuvnx8sivnx2si (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_reduc_maxvnx8sivnx2si (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_reduc_minuvnx8sivnx2si (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_reduc_minvnx8sivnx2si (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_reduc_andvnx8sivnx2si (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_reduc_orvnx8sivnx2si (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_reduc_xorvnx8sivnx2si (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_reduc_sumvnx16sivnx2si ((TARGET_VECTOR && TARGET_MIN_VLEN > 32) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_reduc_maxuvnx16sivnx2si ((TARGET_VECTOR && TARGET_MIN_VLEN > 32) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_reduc_maxvnx16sivnx2si ((TARGET_VECTOR && TARGET_MIN_VLEN > 32) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_reduc_minuvnx16sivnx2si ((TARGET_VECTOR && TARGET_MIN_VLEN > 32) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_reduc_minvnx16sivnx2si ((TARGET_VECTOR && TARGET_MIN_VLEN > 32) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_reduc_andvnx16sivnx2si ((TARGET_VECTOR && TARGET_MIN_VLEN > 32) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_reduc_orvnx16sivnx2si ((TARGET_VECTOR && TARGET_MIN_VLEN > 32) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_reduc_xorvnx16sivnx2si ((TARGET_VECTOR && TARGET_MIN_VLEN > 32) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_reduc_sumvnx1divnx1DI ((TARGET_VECTOR && TARGET_MIN_VLEN > 32) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_reduc_maxuvnx1divnx1DI ((TARGET_VECTOR && TARGET_MIN_VLEN > 32) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_reduc_maxvnx1divnx1DI ((TARGET_VECTOR && TARGET_MIN_VLEN > 32) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_reduc_minuvnx1divnx1DI ((TARGET_VECTOR && TARGET_MIN_VLEN > 32) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_reduc_minvnx1divnx1DI ((TARGET_VECTOR && TARGET_MIN_VLEN > 32) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_reduc_andvnx1divnx1DI ((TARGET_VECTOR && TARGET_MIN_VLEN > 32) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_reduc_orvnx1divnx1DI ((TARGET_VECTOR && TARGET_MIN_VLEN > 32) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_reduc_xorvnx1divnx1DI ((TARGET_VECTOR && TARGET_MIN_VLEN > 32) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_reduc_sumvnx2divnx1DI ((TARGET_VECTOR && TARGET_MIN_VLEN > 32) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_reduc_maxuvnx2divnx1DI ((TARGET_VECTOR && TARGET_MIN_VLEN > 32) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_reduc_maxvnx2divnx1DI ((TARGET_VECTOR && TARGET_MIN_VLEN > 32) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_reduc_minuvnx2divnx1DI ((TARGET_VECTOR && TARGET_MIN_VLEN > 32) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_reduc_minvnx2divnx1DI ((TARGET_VECTOR && TARGET_MIN_VLEN > 32) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_reduc_andvnx2divnx1DI ((TARGET_VECTOR && TARGET_MIN_VLEN > 32) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_reduc_orvnx2divnx1DI ((TARGET_VECTOR && TARGET_MIN_VLEN > 32) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_reduc_xorvnx2divnx1DI ((TARGET_VECTOR && TARGET_MIN_VLEN > 32) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_reduc_sumvnx4divnx1DI ((TARGET_VECTOR && TARGET_MIN_VLEN > 32) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_reduc_maxuvnx4divnx1DI ((TARGET_VECTOR && TARGET_MIN_VLEN > 32) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_reduc_maxvnx4divnx1DI ((TARGET_VECTOR && TARGET_MIN_VLEN > 32) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_reduc_minuvnx4divnx1DI ((TARGET_VECTOR && TARGET_MIN_VLEN > 32) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_reduc_minvnx4divnx1DI ((TARGET_VECTOR && TARGET_MIN_VLEN > 32) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_reduc_andvnx4divnx1DI ((TARGET_VECTOR && TARGET_MIN_VLEN > 32) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_reduc_orvnx4divnx1DI ((TARGET_VECTOR && TARGET_MIN_VLEN > 32) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_reduc_xorvnx4divnx1DI ((TARGET_VECTOR && TARGET_MIN_VLEN > 32) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_reduc_sumvnx8divnx1DI ((TARGET_VECTOR && TARGET_MIN_VLEN > 32) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_reduc_maxuvnx8divnx1DI ((TARGET_VECTOR && TARGET_MIN_VLEN > 32) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_reduc_maxvnx8divnx1DI ((TARGET_VECTOR && TARGET_MIN_VLEN > 32) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_reduc_minuvnx8divnx1DI ((TARGET_VECTOR && TARGET_MIN_VLEN > 32) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_reduc_minvnx8divnx1DI ((TARGET_VECTOR && TARGET_MIN_VLEN > 32) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_reduc_andvnx8divnx1DI ((TARGET_VECTOR && TARGET_MIN_VLEN > 32) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_reduc_orvnx8divnx1DI ((TARGET_VECTOR && TARGET_MIN_VLEN > 32) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_reduc_xorvnx8divnx1DI ((TARGET_VECTOR && TARGET_MIN_VLEN > 32) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_reduc_sumvnx1qivnx4qi (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_reduc_maxuvnx1qivnx4qi (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_reduc_maxvnx1qivnx4qi (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_reduc_minuvnx1qivnx4qi (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_reduc_minvnx1qivnx4qi (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_reduc_andvnx1qivnx4qi (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_reduc_orvnx1qivnx4qi (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_reduc_xorvnx1qivnx4qi (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_reduc_sumvnx2qivnx4qi (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_reduc_maxuvnx2qivnx4qi (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_reduc_maxvnx2qivnx4qi (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_reduc_minuvnx2qivnx4qi (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_reduc_minvnx2qivnx4qi (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_reduc_andvnx2qivnx4qi (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_reduc_orvnx2qivnx4qi (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_reduc_xorvnx2qivnx4qi (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_reduc_sumvnx4qivnx4qi (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_reduc_maxuvnx4qivnx4qi (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_reduc_maxvnx4qivnx4qi (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_reduc_minuvnx4qivnx4qi (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_reduc_minvnx4qivnx4qi (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_reduc_andvnx4qivnx4qi (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_reduc_orvnx4qivnx4qi (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_reduc_xorvnx4qivnx4qi (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_reduc_sumvnx8qivnx4qi (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_reduc_maxuvnx8qivnx4qi (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_reduc_maxvnx8qivnx4qi (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_reduc_minuvnx8qivnx4qi (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_reduc_minvnx8qivnx4qi (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_reduc_andvnx8qivnx4qi (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_reduc_orvnx8qivnx4qi (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_reduc_xorvnx8qivnx4qi (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_reduc_sumvnx16qivnx4qi (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_reduc_maxuvnx16qivnx4qi (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_reduc_maxvnx16qivnx4qi (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_reduc_minuvnx16qivnx4qi (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_reduc_minvnx16qivnx4qi (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_reduc_andvnx16qivnx4qi (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_reduc_orvnx16qivnx4qi (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_reduc_xorvnx16qivnx4qi (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_reduc_sumvnx32qivnx4qi (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_reduc_maxuvnx32qivnx4qi (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_reduc_maxvnx32qivnx4qi (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_reduc_minuvnx32qivnx4qi (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_reduc_minvnx32qivnx4qi (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_reduc_andvnx32qivnx4qi (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_reduc_orvnx32qivnx4qi (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_reduc_xorvnx32qivnx4qi (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_reduc_sumvnx1hivnx2hi (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_reduc_maxuvnx1hivnx2hi (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_reduc_maxvnx1hivnx2hi (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_reduc_minuvnx1hivnx2hi (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_reduc_minvnx1hivnx2hi (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_reduc_andvnx1hivnx2hi (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_reduc_orvnx1hivnx2hi (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_reduc_xorvnx1hivnx2hi (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_reduc_sumvnx2hivnx2hi (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_reduc_maxuvnx2hivnx2hi (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_reduc_maxvnx2hivnx2hi (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_reduc_minuvnx2hivnx2hi (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_reduc_minvnx2hivnx2hi (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_reduc_andvnx2hivnx2hi (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_reduc_orvnx2hivnx2hi (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_reduc_xorvnx2hivnx2hi (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_reduc_sumvnx4hivnx2hi (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_reduc_maxuvnx4hivnx2hi (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_reduc_maxvnx4hivnx2hi (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_reduc_minuvnx4hivnx2hi (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_reduc_minvnx4hivnx2hi (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_reduc_andvnx4hivnx2hi (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_reduc_orvnx4hivnx2hi (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_reduc_xorvnx4hivnx2hi (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_reduc_sumvnx8hivnx2hi (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_reduc_maxuvnx8hivnx2hi (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_reduc_maxvnx8hivnx2hi (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_reduc_minuvnx8hivnx2hi (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_reduc_minvnx8hivnx2hi (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_reduc_andvnx8hivnx2hi (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_reduc_orvnx8hivnx2hi (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_reduc_xorvnx8hivnx2hi (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_reduc_sumvnx16hivnx2hi (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_reduc_maxuvnx16hivnx2hi (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_reduc_maxvnx16hivnx2hi (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_reduc_minuvnx16hivnx2hi (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_reduc_minvnx16hivnx2hi (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_reduc_andvnx16hivnx2hi (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_reduc_orvnx16hivnx2hi (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_reduc_xorvnx16hivnx2hi (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_reduc_sumvnx1sivnx1si (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_reduc_maxuvnx1sivnx1si (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_reduc_maxvnx1sivnx1si (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_reduc_minuvnx1sivnx1si (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_reduc_minvnx1sivnx1si (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_reduc_andvnx1sivnx1si (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_reduc_orvnx1sivnx1si (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_reduc_xorvnx1sivnx1si (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_reduc_sumvnx2sivnx1si (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_reduc_maxuvnx2sivnx1si (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_reduc_maxvnx2sivnx1si (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_reduc_minuvnx2sivnx1si (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_reduc_minvnx2sivnx1si (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_reduc_andvnx2sivnx1si (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_reduc_orvnx2sivnx1si (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_reduc_xorvnx2sivnx1si (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_reduc_sumvnx4sivnx1si (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_reduc_maxuvnx4sivnx1si (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_reduc_maxvnx4sivnx1si (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_reduc_minuvnx4sivnx1si (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_reduc_minvnx4sivnx1si (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_reduc_andvnx4sivnx1si (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_reduc_orvnx4sivnx1si (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_reduc_xorvnx4sivnx1si (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_reduc_sumvnx8sivnx1si (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_reduc_maxuvnx8sivnx1si (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_reduc_maxvnx8sivnx1si (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_reduc_minuvnx8sivnx1si (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_reduc_minvnx8sivnx1si (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_reduc_andvnx8sivnx1si (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_reduc_orvnx8sivnx1si (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_reduc_xorvnx8sivnx1si (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_widen_reduc_plusvnx1qivnx4hi (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_widen_reduc_plusuvnx1qivnx4hi (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_widen_reduc_plusvnx2qivnx4hi (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_widen_reduc_plusuvnx2qivnx4hi (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_widen_reduc_plusvnx4qivnx4hi (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_widen_reduc_plusuvnx4qivnx4hi (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_widen_reduc_plusvnx8qivnx4hi (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_widen_reduc_plusuvnx8qivnx4hi (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_widen_reduc_plusvnx16qivnx4hi (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_widen_reduc_plusuvnx16qivnx4hi (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_widen_reduc_plusvnx32qivnx4hi (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_widen_reduc_plusuvnx32qivnx4hi (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_widen_reduc_plusvnx64qivnx4hi ((TARGET_VECTOR && TARGET_MIN_VLEN > 32) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_widen_reduc_plusuvnx64qivnx4hi ((TARGET_VECTOR && TARGET_MIN_VLEN > 32) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_widen_reduc_plusvnx1hivnx2si (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_widen_reduc_plusuvnx1hivnx2si (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_widen_reduc_plusvnx2hivnx2si (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_widen_reduc_plusuvnx2hivnx2si (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_widen_reduc_plusvnx4hivnx2si (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_widen_reduc_plusuvnx4hivnx2si (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_widen_reduc_plusvnx8hivnx2si (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_widen_reduc_plusuvnx8hivnx2si (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_widen_reduc_plusvnx16hivnx2si (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_widen_reduc_plusuvnx16hivnx2si (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_widen_reduc_plusvnx32hivnx2si ((TARGET_VECTOR && TARGET_MIN_VLEN > 32) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_widen_reduc_plusuvnx32hivnx2si ((TARGET_VECTOR && TARGET_MIN_VLEN > 32) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_widen_reduc_plusvnx1sivnx2di (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_widen_reduc_plusuvnx1sivnx2di (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_widen_reduc_plusvnx2sivnx2di (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_widen_reduc_plusuvnx2sivnx2di (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_widen_reduc_plusvnx4sivnx2di (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_widen_reduc_plusuvnx4sivnx2di (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_widen_reduc_plusvnx8sivnx2di (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_widen_reduc_plusuvnx8sivnx2di (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_widen_reduc_plusvnx16sivnx2di ((TARGET_VECTOR && TARGET_MIN_VLEN > 32) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_widen_reduc_plusuvnx16sivnx2di ((TARGET_VECTOR && TARGET_MIN_VLEN > 32) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_widen_reduc_plusvnx1qivnx2hi (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_widen_reduc_plusuvnx1qivnx2hi (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_widen_reduc_plusvnx2qivnx2hi (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_widen_reduc_plusuvnx2qivnx2hi (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_widen_reduc_plusvnx4qivnx2hi (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_widen_reduc_plusuvnx4qivnx2hi (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_widen_reduc_plusvnx8qivnx2hi (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_widen_reduc_plusuvnx8qivnx2hi (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_widen_reduc_plusvnx16qivnx2hi (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_widen_reduc_plusuvnx16qivnx2hi (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_widen_reduc_plusvnx32qivnx2hi (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_widen_reduc_plusuvnx32qivnx2hi (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_widen_reduc_plusvnx1hivnx1si (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_widen_reduc_plusuvnx1hivnx1si (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_widen_reduc_plusvnx2hivnx1si (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_widen_reduc_plusuvnx2hivnx1si (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_widen_reduc_plusvnx4hivnx1si (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_widen_reduc_plusuvnx4hivnx1si (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_widen_reduc_plusvnx8hivnx1si (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_widen_reduc_plusuvnx8hivnx1si (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_widen_reduc_plusvnx16hivnx1si (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_widen_reduc_plusuvnx16hivnx1si (TARGET_VECTOR && TARGET_MIN_VLEN == 32)
#define HAVE_pred_reduc_maxvnx1sfvnx2sf ((TARGET_VECTOR && TARGET_MIN_VLEN > 32) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_reduc_minvnx1sfvnx2sf ((TARGET_VECTOR && TARGET_MIN_VLEN > 32) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_reduc_maxvnx2sfvnx2sf ((TARGET_VECTOR && TARGET_MIN_VLEN > 32) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_reduc_minvnx2sfvnx2sf ((TARGET_VECTOR && TARGET_MIN_VLEN > 32) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_reduc_maxvnx4sfvnx2sf ((TARGET_VECTOR && TARGET_MIN_VLEN > 32) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_reduc_minvnx4sfvnx2sf ((TARGET_VECTOR && TARGET_MIN_VLEN > 32) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_reduc_maxvnx8sfvnx2sf ((TARGET_VECTOR && TARGET_MIN_VLEN > 32) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_reduc_minvnx8sfvnx2sf ((TARGET_VECTOR && TARGET_MIN_VLEN > 32) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_reduc_maxvnx16sfvnx2sf ((TARGET_VECTOR && TARGET_MIN_VLEN > 32) && (TARGET_VECTOR_ELEN_FP_32 && TARGET_MIN_VLEN > 32))
#define HAVE_pred_reduc_minvnx16sfvnx2sf ((TARGET_VECTOR && TARGET_MIN_VLEN > 32) && (TARGET_VECTOR_ELEN_FP_32 && TARGET_MIN_VLEN > 32))
#define HAVE_pred_reduc_maxvnx1dfvnx1df ((TARGET_VECTOR && TARGET_MIN_VLEN > 32) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_reduc_minvnx1dfvnx1df ((TARGET_VECTOR && TARGET_MIN_VLEN > 32) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_reduc_maxvnx2dfvnx1df ((TARGET_VECTOR && TARGET_MIN_VLEN > 32) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_reduc_minvnx2dfvnx1df ((TARGET_VECTOR && TARGET_MIN_VLEN > 32) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_reduc_maxvnx4dfvnx1df ((TARGET_VECTOR && TARGET_MIN_VLEN > 32) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_reduc_minvnx4dfvnx1df ((TARGET_VECTOR && TARGET_MIN_VLEN > 32) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_reduc_maxvnx8dfvnx1df ((TARGET_VECTOR && TARGET_MIN_VLEN > 32) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_reduc_minvnx8dfvnx1df ((TARGET_VECTOR && TARGET_MIN_VLEN > 32) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_reduc_maxvnx1sfvnx1sf ((TARGET_VECTOR && TARGET_MIN_VLEN == 32) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_reduc_minvnx1sfvnx1sf ((TARGET_VECTOR && TARGET_MIN_VLEN == 32) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_reduc_maxvnx2sfvnx1sf ((TARGET_VECTOR && TARGET_MIN_VLEN == 32) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_reduc_minvnx2sfvnx1sf ((TARGET_VECTOR && TARGET_MIN_VLEN == 32) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_reduc_maxvnx4sfvnx1sf ((TARGET_VECTOR && TARGET_MIN_VLEN == 32) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_reduc_minvnx4sfvnx1sf ((TARGET_VECTOR && TARGET_MIN_VLEN == 32) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_reduc_maxvnx8sfvnx1sf ((TARGET_VECTOR && TARGET_MIN_VLEN == 32) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_reduc_minvnx8sfvnx1sf ((TARGET_VECTOR && TARGET_MIN_VLEN == 32) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_reduc_plusovnx1sfvnx2sf ((TARGET_VECTOR && TARGET_MIN_VLEN > 32) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_reduc_plusuvnx1sfvnx2sf ((TARGET_VECTOR && TARGET_MIN_VLEN > 32) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_reduc_plusovnx2sfvnx2sf ((TARGET_VECTOR && TARGET_MIN_VLEN > 32) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_reduc_plusuvnx2sfvnx2sf ((TARGET_VECTOR && TARGET_MIN_VLEN > 32) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_reduc_plusovnx4sfvnx2sf ((TARGET_VECTOR && TARGET_MIN_VLEN > 32) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_reduc_plusuvnx4sfvnx2sf ((TARGET_VECTOR && TARGET_MIN_VLEN > 32) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_reduc_plusovnx8sfvnx2sf ((TARGET_VECTOR && TARGET_MIN_VLEN > 32) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_reduc_plusuvnx8sfvnx2sf ((TARGET_VECTOR && TARGET_MIN_VLEN > 32) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_reduc_plusovnx16sfvnx2sf ((TARGET_VECTOR && TARGET_MIN_VLEN > 32) && (TARGET_VECTOR_ELEN_FP_32 && TARGET_MIN_VLEN > 32))
#define HAVE_pred_reduc_plusuvnx16sfvnx2sf ((TARGET_VECTOR && TARGET_MIN_VLEN > 32) && (TARGET_VECTOR_ELEN_FP_32 && TARGET_MIN_VLEN > 32))
#define HAVE_pred_reduc_plusovnx1dfvnx1df ((TARGET_VECTOR && TARGET_MIN_VLEN > 32) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_reduc_plusuvnx1dfvnx1df ((TARGET_VECTOR && TARGET_MIN_VLEN > 32) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_reduc_plusovnx2dfvnx1df ((TARGET_VECTOR && TARGET_MIN_VLEN > 32) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_reduc_plusuvnx2dfvnx1df ((TARGET_VECTOR && TARGET_MIN_VLEN > 32) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_reduc_plusovnx4dfvnx1df ((TARGET_VECTOR && TARGET_MIN_VLEN > 32) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_reduc_plusuvnx4dfvnx1df ((TARGET_VECTOR && TARGET_MIN_VLEN > 32) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_reduc_plusovnx8dfvnx1df ((TARGET_VECTOR && TARGET_MIN_VLEN > 32) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_reduc_plusuvnx8dfvnx1df ((TARGET_VECTOR && TARGET_MIN_VLEN > 32) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_reduc_plusovnx1sfvnx1sf ((TARGET_VECTOR && TARGET_MIN_VLEN == 32) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_reduc_plusuvnx1sfvnx1sf ((TARGET_VECTOR && TARGET_MIN_VLEN == 32) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_reduc_plusovnx2sfvnx1sf ((TARGET_VECTOR && TARGET_MIN_VLEN == 32) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_reduc_plusuvnx2sfvnx1sf ((TARGET_VECTOR && TARGET_MIN_VLEN == 32) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_reduc_plusovnx4sfvnx1sf ((TARGET_VECTOR && TARGET_MIN_VLEN == 32) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_reduc_plusuvnx4sfvnx1sf ((TARGET_VECTOR && TARGET_MIN_VLEN == 32) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_reduc_plusovnx8sfvnx1sf ((TARGET_VECTOR && TARGET_MIN_VLEN == 32) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_reduc_plusuvnx8sfvnx1sf ((TARGET_VECTOR && TARGET_MIN_VLEN == 32) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_widen_reduc_plusovnx1sfvnx1df (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_widen_reduc_plusuvnx1sfvnx1df (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_widen_reduc_plusovnx2sfvnx1df (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_widen_reduc_plusuvnx2sfvnx1df (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_widen_reduc_plusovnx4sfvnx1df (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_widen_reduc_plusuvnx4sfvnx1df (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_widen_reduc_plusovnx8sfvnx1df (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_widen_reduc_plusuvnx8sfvnx1df (TARGET_VECTOR && TARGET_MIN_VLEN > 32)
#define HAVE_pred_widen_reduc_plusovnx16sfvnx1df ((TARGET_VECTOR && TARGET_MIN_VLEN > 32) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_widen_reduc_plusuvnx16sfvnx1df ((TARGET_VECTOR && TARGET_MIN_VLEN > 32) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_extract_first_truncvnx1di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_extract_first_truncvnx2di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_extract_first_truncvnx4di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_extract_first_truncvnx8di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_slideupvnx1qi (TARGET_VECTOR)
#define HAVE_pred_slidedownvnx1qi (TARGET_VECTOR)
#define HAVE_pred_slideupvnx2qi (TARGET_VECTOR)
#define HAVE_pred_slidedownvnx2qi (TARGET_VECTOR)
#define HAVE_pred_slideupvnx4qi (TARGET_VECTOR)
#define HAVE_pred_slidedownvnx4qi (TARGET_VECTOR)
#define HAVE_pred_slideupvnx8qi (TARGET_VECTOR)
#define HAVE_pred_slidedownvnx8qi (TARGET_VECTOR)
#define HAVE_pred_slideupvnx16qi (TARGET_VECTOR)
#define HAVE_pred_slidedownvnx16qi (TARGET_VECTOR)
#define HAVE_pred_slideupvnx32qi (TARGET_VECTOR)
#define HAVE_pred_slidedownvnx32qi (TARGET_VECTOR)
#define HAVE_pred_slideupvnx64qi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_slidedownvnx64qi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_slideupvnx1hi (TARGET_VECTOR)
#define HAVE_pred_slidedownvnx1hi (TARGET_VECTOR)
#define HAVE_pred_slideupvnx2hi (TARGET_VECTOR)
#define HAVE_pred_slidedownvnx2hi (TARGET_VECTOR)
#define HAVE_pred_slideupvnx4hi (TARGET_VECTOR)
#define HAVE_pred_slidedownvnx4hi (TARGET_VECTOR)
#define HAVE_pred_slideupvnx8hi (TARGET_VECTOR)
#define HAVE_pred_slidedownvnx8hi (TARGET_VECTOR)
#define HAVE_pred_slideupvnx16hi (TARGET_VECTOR)
#define HAVE_pred_slidedownvnx16hi (TARGET_VECTOR)
#define HAVE_pred_slideupvnx32hi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_slidedownvnx32hi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_slideupvnx1si (TARGET_VECTOR)
#define HAVE_pred_slidedownvnx1si (TARGET_VECTOR)
#define HAVE_pred_slideupvnx2si (TARGET_VECTOR)
#define HAVE_pred_slidedownvnx2si (TARGET_VECTOR)
#define HAVE_pred_slideupvnx4si (TARGET_VECTOR)
#define HAVE_pred_slidedownvnx4si (TARGET_VECTOR)
#define HAVE_pred_slideupvnx8si (TARGET_VECTOR)
#define HAVE_pred_slidedownvnx8si (TARGET_VECTOR)
#define HAVE_pred_slideupvnx16si ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_slidedownvnx16si ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_slideupvnx1di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_slidedownvnx1di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_slideupvnx2di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_slidedownvnx2di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_slideupvnx4di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_slidedownvnx4di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_slideupvnx8di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_slidedownvnx8di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_slideupvnx1sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_slidedownvnx1sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_slideupvnx2sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_slidedownvnx2sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_slideupvnx4sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_slidedownvnx4sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_slideupvnx8sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_slidedownvnx8sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_slideupvnx16sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32 && TARGET_MIN_VLEN > 32))
#define HAVE_pred_slidedownvnx16sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32 && TARGET_MIN_VLEN > 32))
#define HAVE_pred_slideupvnx1df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_slidedownvnx1df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_slideupvnx2df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_slidedownvnx2df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_slideupvnx4df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_slidedownvnx4df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_slideupvnx8df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_slidedownvnx8df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_slide1upvnx1qi (TARGET_VECTOR)
#define HAVE_pred_slide1downvnx1qi (TARGET_VECTOR)
#define HAVE_pred_slide1upvnx2qi (TARGET_VECTOR)
#define HAVE_pred_slide1downvnx2qi (TARGET_VECTOR)
#define HAVE_pred_slide1upvnx4qi (TARGET_VECTOR)
#define HAVE_pred_slide1downvnx4qi (TARGET_VECTOR)
#define HAVE_pred_slide1upvnx8qi (TARGET_VECTOR)
#define HAVE_pred_slide1downvnx8qi (TARGET_VECTOR)
#define HAVE_pred_slide1upvnx16qi (TARGET_VECTOR)
#define HAVE_pred_slide1downvnx16qi (TARGET_VECTOR)
#define HAVE_pred_slide1upvnx32qi (TARGET_VECTOR)
#define HAVE_pred_slide1downvnx32qi (TARGET_VECTOR)
#define HAVE_pred_slide1upvnx64qi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_slide1downvnx64qi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_slide1upvnx1hi (TARGET_VECTOR)
#define HAVE_pred_slide1downvnx1hi (TARGET_VECTOR)
#define HAVE_pred_slide1upvnx2hi (TARGET_VECTOR)
#define HAVE_pred_slide1downvnx2hi (TARGET_VECTOR)
#define HAVE_pred_slide1upvnx4hi (TARGET_VECTOR)
#define HAVE_pred_slide1downvnx4hi (TARGET_VECTOR)
#define HAVE_pred_slide1upvnx8hi (TARGET_VECTOR)
#define HAVE_pred_slide1downvnx8hi (TARGET_VECTOR)
#define HAVE_pred_slide1upvnx16hi (TARGET_VECTOR)
#define HAVE_pred_slide1downvnx16hi (TARGET_VECTOR)
#define HAVE_pred_slide1upvnx32hi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_slide1downvnx32hi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_slide1upvnx1si (TARGET_VECTOR)
#define HAVE_pred_slide1downvnx1si (TARGET_VECTOR)
#define HAVE_pred_slide1upvnx2si (TARGET_VECTOR)
#define HAVE_pred_slide1downvnx2si (TARGET_VECTOR)
#define HAVE_pred_slide1upvnx4si (TARGET_VECTOR)
#define HAVE_pred_slide1downvnx4si (TARGET_VECTOR)
#define HAVE_pred_slide1upvnx8si (TARGET_VECTOR)
#define HAVE_pred_slide1downvnx8si (TARGET_VECTOR)
#define HAVE_pred_slide1upvnx16si ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_slide1downvnx16si ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_slide1upvnx1sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_slide1downvnx1sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_slide1upvnx2sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_slide1downvnx2sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_slide1upvnx4sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_slide1downvnx4sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_slide1upvnx8sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_slide1downvnx8sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_slide1upvnx16sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32 && TARGET_MIN_VLEN > 32))
#define HAVE_pred_slide1downvnx16sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32 && TARGET_MIN_VLEN > 32))
#define HAVE_pred_slide1upvnx1df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_slide1downvnx1df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_slide1upvnx2df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_slide1downvnx2df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_slide1upvnx4df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_slide1downvnx4df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_slide1upvnx8df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_slide1downvnx8df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_gathervnx1qi (TARGET_VECTOR)
#define HAVE_pred_gathervnx2qi (TARGET_VECTOR)
#define HAVE_pred_gathervnx4qi (TARGET_VECTOR)
#define HAVE_pred_gathervnx8qi (TARGET_VECTOR)
#define HAVE_pred_gathervnx16qi (TARGET_VECTOR)
#define HAVE_pred_gathervnx32qi (TARGET_VECTOR)
#define HAVE_pred_gathervnx64qi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_gathervnx1hi (TARGET_VECTOR)
#define HAVE_pred_gathervnx2hi (TARGET_VECTOR)
#define HAVE_pred_gathervnx4hi (TARGET_VECTOR)
#define HAVE_pred_gathervnx8hi (TARGET_VECTOR)
#define HAVE_pred_gathervnx16hi (TARGET_VECTOR)
#define HAVE_pred_gathervnx32hi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_gathervnx1si (TARGET_VECTOR)
#define HAVE_pred_gathervnx2si (TARGET_VECTOR)
#define HAVE_pred_gathervnx4si (TARGET_VECTOR)
#define HAVE_pred_gathervnx8si (TARGET_VECTOR)
#define HAVE_pred_gathervnx16si ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_gathervnx1di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_gathervnx2di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_gathervnx4di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_gathervnx8di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_gathervnx1sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_gathervnx2sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_gathervnx4sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_gathervnx8sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_gathervnx16sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32 && TARGET_MIN_VLEN > 32))
#define HAVE_pred_gathervnx1df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_gathervnx2df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_gathervnx4df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_gathervnx8df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_gathervnx1qi_scalar (TARGET_VECTOR)
#define HAVE_pred_gathervnx2qi_scalar (TARGET_VECTOR)
#define HAVE_pred_gathervnx4qi_scalar (TARGET_VECTOR)
#define HAVE_pred_gathervnx8qi_scalar (TARGET_VECTOR)
#define HAVE_pred_gathervnx16qi_scalar (TARGET_VECTOR)
#define HAVE_pred_gathervnx32qi_scalar (TARGET_VECTOR)
#define HAVE_pred_gathervnx64qi_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_gathervnx1hi_scalar (TARGET_VECTOR)
#define HAVE_pred_gathervnx2hi_scalar (TARGET_VECTOR)
#define HAVE_pred_gathervnx4hi_scalar (TARGET_VECTOR)
#define HAVE_pred_gathervnx8hi_scalar (TARGET_VECTOR)
#define HAVE_pred_gathervnx16hi_scalar (TARGET_VECTOR)
#define HAVE_pred_gathervnx32hi_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_gathervnx1si_scalar (TARGET_VECTOR)
#define HAVE_pred_gathervnx2si_scalar (TARGET_VECTOR)
#define HAVE_pred_gathervnx4si_scalar (TARGET_VECTOR)
#define HAVE_pred_gathervnx8si_scalar (TARGET_VECTOR)
#define HAVE_pred_gathervnx16si_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_gathervnx1di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_gathervnx2di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_gathervnx4di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_gathervnx8di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_gathervnx1sf_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_gathervnx2sf_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_gathervnx4sf_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_gathervnx8sf_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_gathervnx16sf_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32 && TARGET_MIN_VLEN > 32))
#define HAVE_pred_gathervnx1df_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_gathervnx2df_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_gathervnx4df_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_gathervnx8df_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_gatherei16vnx1qi (TARGET_VECTOR)
#define HAVE_pred_gatherei16vnx2qi (TARGET_VECTOR)
#define HAVE_pred_gatherei16vnx4qi (TARGET_VECTOR)
#define HAVE_pred_gatherei16vnx8qi (TARGET_VECTOR)
#define HAVE_pred_gatherei16vnx16qi (TARGET_VECTOR)
#define HAVE_pred_gatherei16vnx32qi (TARGET_VECTOR)
#define HAVE_pred_gatherei16vnx1hi (TARGET_VECTOR)
#define HAVE_pred_gatherei16vnx2hi (TARGET_VECTOR)
#define HAVE_pred_gatherei16vnx4hi (TARGET_VECTOR)
#define HAVE_pred_gatherei16vnx8hi (TARGET_VECTOR)
#define HAVE_pred_gatherei16vnx16hi (TARGET_VECTOR)
#define HAVE_pred_gatherei16vnx32hi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_gatherei16vnx1si (TARGET_VECTOR)
#define HAVE_pred_gatherei16vnx2si (TARGET_VECTOR)
#define HAVE_pred_gatherei16vnx4si (TARGET_VECTOR)
#define HAVE_pred_gatherei16vnx8si (TARGET_VECTOR)
#define HAVE_pred_gatherei16vnx16si ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_gatherei16vnx1di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_gatherei16vnx2di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_gatherei16vnx4di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_gatherei16vnx8di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_gatherei16vnx1sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_gatherei16vnx2sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_gatherei16vnx4sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_gatherei16vnx8sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_gatherei16vnx16sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32 && TARGET_MIN_VLEN > 32))
#define HAVE_pred_gatherei16vnx1df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_gatherei16vnx2df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_gatherei16vnx4df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_gatherei16vnx8df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_compressvnx1qi (TARGET_VECTOR)
#define HAVE_pred_compressvnx2qi (TARGET_VECTOR)
#define HAVE_pred_compressvnx4qi (TARGET_VECTOR)
#define HAVE_pred_compressvnx8qi (TARGET_VECTOR)
#define HAVE_pred_compressvnx16qi (TARGET_VECTOR)
#define HAVE_pred_compressvnx32qi (TARGET_VECTOR)
#define HAVE_pred_compressvnx64qi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_compressvnx1hi (TARGET_VECTOR)
#define HAVE_pred_compressvnx2hi (TARGET_VECTOR)
#define HAVE_pred_compressvnx4hi (TARGET_VECTOR)
#define HAVE_pred_compressvnx8hi (TARGET_VECTOR)
#define HAVE_pred_compressvnx16hi (TARGET_VECTOR)
#define HAVE_pred_compressvnx32hi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_compressvnx1si (TARGET_VECTOR)
#define HAVE_pred_compressvnx2si (TARGET_VECTOR)
#define HAVE_pred_compressvnx4si (TARGET_VECTOR)
#define HAVE_pred_compressvnx8si (TARGET_VECTOR)
#define HAVE_pred_compressvnx16si ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_compressvnx1di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_compressvnx2di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_compressvnx4di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_compressvnx8di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_compressvnx1sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_compressvnx2sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_compressvnx4sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_compressvnx8sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_compressvnx16sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32 && TARGET_MIN_VLEN > 32))
#define HAVE_pred_compressvnx1df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_compressvnx2df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_compressvnx4df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_compressvnx8df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_read_vlsi (TARGET_VECTOR)
#define HAVE_read_vldi_zero_extend (TARGET_VECTOR && TARGET_64BIT)
#define HAVE_pred_fault_loadvnx1qi (TARGET_VECTOR)
#define HAVE_pred_fault_loadvnx2qi (TARGET_VECTOR)
#define HAVE_pred_fault_loadvnx4qi (TARGET_VECTOR)
#define HAVE_pred_fault_loadvnx8qi (TARGET_VECTOR)
#define HAVE_pred_fault_loadvnx16qi (TARGET_VECTOR)
#define HAVE_pred_fault_loadvnx32qi (TARGET_VECTOR)
#define HAVE_pred_fault_loadvnx64qi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_fault_loadvnx1hi (TARGET_VECTOR)
#define HAVE_pred_fault_loadvnx2hi (TARGET_VECTOR)
#define HAVE_pred_fault_loadvnx4hi (TARGET_VECTOR)
#define HAVE_pred_fault_loadvnx8hi (TARGET_VECTOR)
#define HAVE_pred_fault_loadvnx16hi (TARGET_VECTOR)
#define HAVE_pred_fault_loadvnx32hi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_fault_loadvnx1si (TARGET_VECTOR)
#define HAVE_pred_fault_loadvnx2si (TARGET_VECTOR)
#define HAVE_pred_fault_loadvnx4si (TARGET_VECTOR)
#define HAVE_pred_fault_loadvnx8si (TARGET_VECTOR)
#define HAVE_pred_fault_loadvnx16si ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_fault_loadvnx1di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_fault_loadvnx2di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_fault_loadvnx4di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_fault_loadvnx8di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_fault_loadvnx1sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_fault_loadvnx2sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_fault_loadvnx4sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_fault_loadvnx8sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_fault_loadvnx16sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32 && TARGET_MIN_VLEN > 32))
#define HAVE_pred_fault_loadvnx1df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_fault_loadvnx2df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_fault_loadvnx4df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_fault_loadvnx8df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_addvsi4 1
#define HAVE_addvdi4 (TARGET_64BIT)
#define HAVE_uaddvsi4 1
#define HAVE_uaddvdi4 (TARGET_64BIT)
#define HAVE_subvsi4 1
#define HAVE_subvdi4 (TARGET_64BIT)
#define HAVE_usubvsi4 1
#define HAVE_usubvdi4 (TARGET_64BIT)
#define HAVE_mulvsi4 (TARGET_ZMMUL || TARGET_MUL)
#define HAVE_mulvdi4 ((TARGET_ZMMUL || TARGET_MUL) && (TARGET_64BIT))
#define HAVE_umulvsi4 (TARGET_ZMMUL || TARGET_MUL)
#define HAVE_umulvdi4 ((TARGET_ZMMUL || TARGET_MUL) && (TARGET_64BIT))
#define HAVE_mulditi3 ((TARGET_ZMMUL || TARGET_MUL) && TARGET_64BIT)
#define HAVE_umulditi3 ((TARGET_ZMMUL || TARGET_MUL) && TARGET_64BIT)
#define HAVE_usmulditi3 ((TARGET_ZMMUL || TARGET_MUL) && TARGET_64BIT)
#define HAVE_mulsidi3 ((TARGET_ZMMUL || TARGET_MUL) && !TARGET_64BIT)
#define HAVE_umulsidi3 ((TARGET_ZMMUL || TARGET_MUL) && !TARGET_64BIT)
#define HAVE_usmulsidi3 ((TARGET_ZMMUL || TARGET_MUL) && !TARGET_64BIT)
#define HAVE_zero_extendsidi2 (TARGET_64BIT)
#define HAVE_zero_extendhisi2 1
#define HAVE_zero_extendhidi2 (TARGET_64BIT)
#define HAVE_extendqihi2 1
#define HAVE_extendqisi2 1
#define HAVE_extendqidi2 (TARGET_64BIT)
#define HAVE_extendhihi2 1
#define HAVE_extendhisi2 1
#define HAVE_extendhidi2 (TARGET_64BIT)
#define HAVE_movhf 1
#define HAVE_movdi 1
#define HAVE_movsi 1
#define HAVE_movhi 1
#define HAVE_movqi 1
#define HAVE_movsf 1
#define HAVE_movdf 1
#define HAVE_cpymemsi 1
#define HAVE_clear_cache 1
#define HAVE_movsicc (TARGET_SFB_ALU || TARGET_XTHEADCONDMOV)
#define HAVE_movdicc ((TARGET_SFB_ALU || TARGET_XTHEADCONDMOV) && (TARGET_64BIT))
#define HAVE_condjump 1
#define HAVE_cbranchqi4 (TARGET_64BIT)
#define HAVE_cbranchsi4 1
#define HAVE_cbranchdi4 (TARGET_64BIT)
#define HAVE_cbranchsf4 (TARGET_HARD_FLOAT || TARGET_ZFINX)
#define HAVE_cbranchdf4 ((TARGET_HARD_FLOAT || TARGET_ZFINX) && (TARGET_DOUBLE_FLOAT || TARGET_ZDINX))
#define HAVE_cbranchhf4 ((TARGET_HARD_FLOAT || TARGET_ZFINX) && (TARGET_ZFH || TARGET_ZHINX))
#define HAVE_cstoresi4 1
#define HAVE_cstoredi4 (TARGET_64BIT)
#define HAVE_cstoresf4 (TARGET_HARD_FLOAT || TARGET_ZFINX)
#define HAVE_cstoredf4 ((TARGET_HARD_FLOAT || TARGET_ZFINX) && (TARGET_DOUBLE_FLOAT || TARGET_ZDINX))
#define HAVE_cstorehf4 ((TARGET_HARD_FLOAT || TARGET_ZFINX) && (TARGET_ZFH || TARGET_ZHINX))
#define HAVE_flt_quietsfsi4 ((TARGET_HARD_FLOAT || TARGET_ZFINX) && (((!TARGET_64BIT) && (TARGET_HARD_FLOAT || TARGET_ZFINX)) && (TARGET_HARD_FLOAT || TARGET_ZFINX)))
#define HAVE_fle_quietsfsi4 ((TARGET_HARD_FLOAT || TARGET_ZFINX) && (((!TARGET_64BIT) && (TARGET_HARD_FLOAT || TARGET_ZFINX)) && (TARGET_HARD_FLOAT || TARGET_ZFINX)))
#define HAVE_flt_quietsfdi4 ((TARGET_HARD_FLOAT || TARGET_ZFINX) && (((TARGET_64BIT) && (TARGET_HARD_FLOAT || TARGET_ZFINX)) && (TARGET_HARD_FLOAT || TARGET_ZFINX)))
#define HAVE_fle_quietsfdi4 ((TARGET_HARD_FLOAT || TARGET_ZFINX) && (((TARGET_64BIT) && (TARGET_HARD_FLOAT || TARGET_ZFINX)) && (TARGET_HARD_FLOAT || TARGET_ZFINX)))
#define HAVE_flt_quietdfsi4 ((TARGET_HARD_FLOAT || TARGET_ZFINX) && (((!TARGET_64BIT) && (TARGET_DOUBLE_FLOAT || TARGET_ZDINX)) && (TARGET_DOUBLE_FLOAT || TARGET_ZDINX)))
#define HAVE_fle_quietdfsi4 ((TARGET_HARD_FLOAT || TARGET_ZFINX) && (((!TARGET_64BIT) && (TARGET_DOUBLE_FLOAT || TARGET_ZDINX)) && (TARGET_DOUBLE_FLOAT || TARGET_ZDINX)))
#define HAVE_flt_quietdfdi4 ((TARGET_HARD_FLOAT || TARGET_ZFINX) && (((TARGET_64BIT) && (TARGET_DOUBLE_FLOAT || TARGET_ZDINX)) && (TARGET_DOUBLE_FLOAT || TARGET_ZDINX)))
#define HAVE_fle_quietdfdi4 ((TARGET_HARD_FLOAT || TARGET_ZFINX) && (((TARGET_64BIT) && (TARGET_DOUBLE_FLOAT || TARGET_ZDINX)) && (TARGET_DOUBLE_FLOAT || TARGET_ZDINX)))
#define HAVE_flt_quiethfsi4 ((TARGET_HARD_FLOAT || TARGET_ZFINX) && (((!TARGET_64BIT) && (TARGET_ZFH || TARGET_ZHINX)) && (TARGET_ZFH || TARGET_ZHINX)))
#define HAVE_fle_quiethfsi4 ((TARGET_HARD_FLOAT || TARGET_ZFINX) && (((!TARGET_64BIT) && (TARGET_ZFH || TARGET_ZHINX)) && (TARGET_ZFH || TARGET_ZHINX)))
#define HAVE_flt_quiethfdi4 ((TARGET_HARD_FLOAT || TARGET_ZFINX) && (((TARGET_64BIT) && (TARGET_ZFH || TARGET_ZHINX)) && (TARGET_ZFH || TARGET_ZHINX)))
#define HAVE_fle_quiethfdi4 ((TARGET_HARD_FLOAT || TARGET_ZFINX) && (((TARGET_64BIT) && (TARGET_ZFH || TARGET_ZHINX)) && (TARGET_ZFH || TARGET_ZHINX)))
#define HAVE_indirect_jump 1
#define HAVE_tablejump 1
#define HAVE_prologue 1
#define HAVE_epilogue 1
#define HAVE_sibcall_epilogue 1
#define HAVE_return (riscv_can_use_return_insn ())
#define HAVE_eh_return 1
#define HAVE_sibcall 1
#define HAVE_sibcall_value 1
#define HAVE_call 1
#define HAVE_call_value 1
#define HAVE_untyped_call 1
#define HAVE_restore_stack_nonlocal 1
#define HAVE_get_thread_pointersi (Pmode == SImode)
#define HAVE_get_thread_pointerdi (Pmode == DImode)
#define HAVE_stack_protect_set 1
#define HAVE_stack_protect_test 1
#define HAVE_extvsi (TARGET_XTHEADBB)
#define HAVE_extvdi ((TARGET_XTHEADBB) && (TARGET_64BIT))
#define HAVE_extzvsi (TARGET_XTHEADBB)
#define HAVE_extzvdi ((TARGET_XTHEADBB) && (TARGET_64BIT))
#define HAVE_maddhisi4 (TARGET_XTHEADMAC)
#define HAVE_msubhisi4 (TARGET_XTHEADMAC)
#define HAVE_clzdi2 (TARGET_64BIT && (TARGET_ZBB || TARGET_XTHEADBB))
#define HAVE_clzsi2 (TARGET_ZBB || (!TARGET_64BIT && TARGET_XTHEADBB))
#define HAVE_ctzsi2 (TARGET_ZBB)
#define HAVE_ctzdi2 ((TARGET_ZBB) && (TARGET_64BIT))
#define HAVE_popcountsi2 (TARGET_ZBB)
#define HAVE_popcountdi2 ((TARGET_ZBB) && (TARGET_64BIT))
#define HAVE_rotrsi3 (TARGET_ZBB || TARGET_XTHEADBB)
#define HAVE_rotrdi3 ((TARGET_ZBB || TARGET_XTHEADBB) && (TARGET_64BIT))
#define HAVE_bswapdi2 (TARGET_64BIT && (TARGET_ZBB || TARGET_XTHEADBB))
#define HAVE_bswapsi2 ((!TARGET_64BIT && TARGET_ZBB) || TARGET_XTHEADBB)
#define HAVE_bswaphi2 (TARGET_ZBB)
#define HAVE_mem_thread_fence 1
#define HAVE_atomic_compare_and_swapsi (TARGET_ATOMIC)
#define HAVE_atomic_compare_and_swapdi ((TARGET_ATOMIC) && (TARGET_64BIT))
#define HAVE_atomic_test_and_set (TARGET_ATOMIC)
#define HAVE_vreinterpretvnx1qi (TARGET_VECTOR)
#define HAVE_vreinterpretvnx2qi (TARGET_VECTOR)
#define HAVE_vreinterpretvnx4qi (TARGET_VECTOR)
#define HAVE_vreinterpretvnx8qi (TARGET_VECTOR)
#define HAVE_vreinterpretvnx16qi (TARGET_VECTOR)
#define HAVE_vreinterpretvnx32qi (TARGET_VECTOR)
#define HAVE_vreinterpretvnx64qi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_vreinterpretvnx1hi (TARGET_VECTOR)
#define HAVE_vreinterpretvnx2hi (TARGET_VECTOR)
#define HAVE_vreinterpretvnx4hi (TARGET_VECTOR)
#define HAVE_vreinterpretvnx8hi (TARGET_VECTOR)
#define HAVE_vreinterpretvnx16hi (TARGET_VECTOR)
#define HAVE_vreinterpretvnx32hi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_vreinterpretvnx1si (TARGET_VECTOR)
#define HAVE_vreinterpretvnx2si (TARGET_VECTOR)
#define HAVE_vreinterpretvnx4si (TARGET_VECTOR)
#define HAVE_vreinterpretvnx8si (TARGET_VECTOR)
#define HAVE_vreinterpretvnx16si ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_vreinterpretvnx1di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_vreinterpretvnx2di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_vreinterpretvnx4di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_vreinterpretvnx8di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_vreinterpretvnx1sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_vreinterpretvnx2sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_vreinterpretvnx4sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_vreinterpretvnx8sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_vreinterpretvnx16sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32 && TARGET_MIN_VLEN > 32))
#define HAVE_vreinterpretvnx1df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_vreinterpretvnx2df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_vreinterpretvnx4df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_vreinterpretvnx8df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_vlmul_extx2vnx1qi (TARGET_VECTOR)
#define HAVE_vlmul_extx2vnx2qi (TARGET_VECTOR)
#define HAVE_vlmul_extx2vnx4qi (TARGET_VECTOR)
#define HAVE_vlmul_extx2vnx8qi (TARGET_VECTOR)
#define HAVE_vlmul_extx2vnx16qi (TARGET_VECTOR)
#define HAVE_vlmul_extx2vnx32qi (TARGET_VECTOR)
#define HAVE_vlmul_extx2vnx1hi (TARGET_VECTOR)
#define HAVE_vlmul_extx2vnx2hi (TARGET_VECTOR)
#define HAVE_vlmul_extx2vnx4hi (TARGET_VECTOR)
#define HAVE_vlmul_extx2vnx8hi (TARGET_VECTOR)
#define HAVE_vlmul_extx2vnx16hi (TARGET_VECTOR)
#define HAVE_vlmul_extx2vnx1si (TARGET_VECTOR)
#define HAVE_vlmul_extx2vnx2si (TARGET_VECTOR)
#define HAVE_vlmul_extx2vnx4si (TARGET_VECTOR)
#define HAVE_vlmul_extx2vnx8si (TARGET_VECTOR)
#define HAVE_vlmul_extx2vnx1di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_vlmul_extx2vnx2di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_vlmul_extx2vnx4di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_vlmul_extx2vnx1sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_vlmul_extx2vnx2sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_vlmul_extx2vnx4sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_vlmul_extx2vnx8sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_vlmul_extx2vnx1df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_vlmul_extx2vnx2df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_vlmul_extx2vnx4df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_vlmul_extx4vnx1qi (TARGET_VECTOR)
#define HAVE_vlmul_extx4vnx2qi (TARGET_VECTOR)
#define HAVE_vlmul_extx4vnx4qi (TARGET_VECTOR)
#define HAVE_vlmul_extx4vnx8qi (TARGET_VECTOR)
#define HAVE_vlmul_extx4vnx16qi (TARGET_VECTOR)
#define HAVE_vlmul_extx4vnx1hi (TARGET_VECTOR)
#define HAVE_vlmul_extx4vnx2hi (TARGET_VECTOR)
#define HAVE_vlmul_extx4vnx4hi (TARGET_VECTOR)
#define HAVE_vlmul_extx4vnx8hi (TARGET_VECTOR)
#define HAVE_vlmul_extx4vnx1si (TARGET_VECTOR)
#define HAVE_vlmul_extx4vnx2si (TARGET_VECTOR)
#define HAVE_vlmul_extx4vnx4si (TARGET_VECTOR)
#define HAVE_vlmul_extx4vnx1di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_vlmul_extx4vnx2di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_vlmul_extx4vnx1sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_vlmul_extx4vnx2sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_vlmul_extx4vnx4sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_vlmul_extx4vnx1df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_vlmul_extx4vnx2df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_vlmul_extx8vnx1qi (TARGET_VECTOR)
#define HAVE_vlmul_extx8vnx2qi (TARGET_VECTOR)
#define HAVE_vlmul_extx8vnx4qi (TARGET_VECTOR)
#define HAVE_vlmul_extx8vnx8qi (TARGET_VECTOR)
#define HAVE_vlmul_extx8vnx1hi (TARGET_VECTOR)
#define HAVE_vlmul_extx8vnx2hi (TARGET_VECTOR)
#define HAVE_vlmul_extx8vnx4hi (TARGET_VECTOR)
#define HAVE_vlmul_extx8vnx1si (TARGET_VECTOR)
#define HAVE_vlmul_extx8vnx2si (TARGET_VECTOR)
#define HAVE_vlmul_extx8vnx1di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_vlmul_extx8vnx1sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_vlmul_extx8vnx2sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_vlmul_extx8vnx1df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_vlmul_extx16vnx1qi (TARGET_VECTOR)
#define HAVE_vlmul_extx16vnx2qi (TARGET_VECTOR)
#define HAVE_vlmul_extx16vnx4qi (TARGET_VECTOR)
#define HAVE_vlmul_extx16vnx1hi (TARGET_VECTOR)
#define HAVE_vlmul_extx16vnx2hi (TARGET_VECTOR)
#define HAVE_vlmul_extx16vnx1si (TARGET_VECTOR)
#define HAVE_vlmul_extx16vnx1sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_vlmul_extx32vnx1qi (TARGET_VECTOR)
#define HAVE_vlmul_extx32vnx2qi (TARGET_VECTOR)
#define HAVE_vlmul_extx32vnx1hi (TARGET_VECTOR)
#define HAVE_vlmul_extx64vnx1qi (TARGET_VECTOR)
#define HAVE_movvnx1qi (TARGET_VECTOR)
#define HAVE_movvnx2qi (TARGET_VECTOR)
#define HAVE_movvnx4qi (TARGET_VECTOR)
#define HAVE_movvnx8qi (TARGET_VECTOR)
#define HAVE_movvnx16qi (TARGET_VECTOR)
#define HAVE_movvnx32qi (TARGET_VECTOR)
#define HAVE_movvnx64qi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_movvnx1hi (TARGET_VECTOR)
#define HAVE_movvnx2hi (TARGET_VECTOR)
#define HAVE_movvnx4hi (TARGET_VECTOR)
#define HAVE_movvnx8hi (TARGET_VECTOR)
#define HAVE_movvnx16hi (TARGET_VECTOR)
#define HAVE_movvnx32hi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_movvnx1si (TARGET_VECTOR)
#define HAVE_movvnx2si (TARGET_VECTOR)
#define HAVE_movvnx4si (TARGET_VECTOR)
#define HAVE_movvnx8si (TARGET_VECTOR)
#define HAVE_movvnx16si ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_movvnx1di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_movvnx2di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_movvnx4di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_movvnx8di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_movvnx1sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_movvnx2sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_movvnx4sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_movvnx8sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_movvnx16sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32 && TARGET_MIN_VLEN > 32))
#define HAVE_movvnx1df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_movvnx2df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_movvnx4df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_movvnx8df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_movvnx1bi (TARGET_VECTOR)
#define HAVE_movvnx2bi (TARGET_VECTOR)
#define HAVE_movvnx4bi (TARGET_VECTOR)
#define HAVE_movvnx8bi (TARGET_VECTOR)
#define HAVE_movvnx16bi (TARGET_VECTOR)
#define HAVE_movvnx32bi (TARGET_VECTOR)
#define HAVE_movvnx64bi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_movvnx1qisi_lra ((TARGET_VECTOR && (lra_in_progress || reload_completed)) && (Pmode == SImode))
#define HAVE_movvnx1qidi_lra ((TARGET_VECTOR && (lra_in_progress || reload_completed)) && (Pmode == DImode))
#define HAVE_movvnx2qisi_lra ((TARGET_VECTOR && (lra_in_progress || reload_completed)) && (Pmode == SImode))
#define HAVE_movvnx2qidi_lra ((TARGET_VECTOR && (lra_in_progress || reload_completed)) && (Pmode == DImode))
#define HAVE_movvnx4qisi_lra ((TARGET_VECTOR && (lra_in_progress || reload_completed)) && ((TARGET_MIN_VLEN > 32) && (Pmode == SImode)))
#define HAVE_movvnx4qidi_lra ((TARGET_VECTOR && (lra_in_progress || reload_completed)) && ((TARGET_MIN_VLEN > 32) && (Pmode == DImode)))
#define HAVE_movvnx1hisi_lra ((TARGET_VECTOR && (lra_in_progress || reload_completed)) && (Pmode == SImode))
#define HAVE_movvnx1hidi_lra ((TARGET_VECTOR && (lra_in_progress || reload_completed)) && (Pmode == DImode))
#define HAVE_movvnx2hisi_lra ((TARGET_VECTOR && (lra_in_progress || reload_completed)) && ((TARGET_MIN_VLEN > 32) && (Pmode == SImode)))
#define HAVE_movvnx2hidi_lra ((TARGET_VECTOR && (lra_in_progress || reload_completed)) && ((TARGET_MIN_VLEN > 32) && (Pmode == DImode)))
#define HAVE_movvnx1sisi_lra ((TARGET_VECTOR && (lra_in_progress || reload_completed)) && ((TARGET_MIN_VLEN > 32) && (Pmode == SImode)))
#define HAVE_movvnx1sidi_lra ((TARGET_VECTOR && (lra_in_progress || reload_completed)) && ((TARGET_MIN_VLEN > 32) && (Pmode == DImode)))
#define HAVE_movvnx1sfsi_lra ((TARGET_VECTOR && (lra_in_progress || reload_completed)) && ((TARGET_VECTOR_ELEN_FP_32 && TARGET_MIN_VLEN > 32) && (Pmode == SImode)))
#define HAVE_movvnx1sfdi_lra ((TARGET_VECTOR && (lra_in_progress || reload_completed)) && ((TARGET_VECTOR_ELEN_FP_32 && TARGET_MIN_VLEN > 32) && (Pmode == DImode)))
#define HAVE_movvnx1bisi_lra ((TARGET_VECTOR && (lra_in_progress || reload_completed)) && (Pmode == SImode))
#define HAVE_movvnx2bisi_lra ((TARGET_VECTOR && (lra_in_progress || reload_completed)) && (Pmode == SImode))
#define HAVE_movvnx4bisi_lra ((TARGET_VECTOR && (lra_in_progress || reload_completed)) && (Pmode == SImode))
#define HAVE_movvnx8bisi_lra ((TARGET_VECTOR && (lra_in_progress || reload_completed)) && (Pmode == SImode))
#define HAVE_movvnx16bisi_lra ((TARGET_VECTOR && (lra_in_progress || reload_completed)) && (Pmode == SImode))
#define HAVE_movvnx32bisi_lra ((TARGET_VECTOR && (lra_in_progress || reload_completed)) && (Pmode == SImode))
#define HAVE_movvnx64bisi_lra ((TARGET_VECTOR && (lra_in_progress || reload_completed)) && ((TARGET_MIN_VLEN > 32) && (Pmode == SImode)))
#define HAVE_movvnx1bidi_lra ((TARGET_VECTOR && (lra_in_progress || reload_completed)) && (Pmode == DImode))
#define HAVE_movvnx2bidi_lra ((TARGET_VECTOR && (lra_in_progress || reload_completed)) && (Pmode == DImode))
#define HAVE_movvnx4bidi_lra ((TARGET_VECTOR && (lra_in_progress || reload_completed)) && (Pmode == DImode))
#define HAVE_movvnx8bidi_lra ((TARGET_VECTOR && (lra_in_progress || reload_completed)) && (Pmode == DImode))
#define HAVE_movvnx16bidi_lra ((TARGET_VECTOR && (lra_in_progress || reload_completed)) && (Pmode == DImode))
#define HAVE_movvnx32bidi_lra ((TARGET_VECTOR && (lra_in_progress || reload_completed)) && (Pmode == DImode))
#define HAVE_movvnx64bidi_lra ((TARGET_VECTOR && (lra_in_progress || reload_completed)) && ((TARGET_MIN_VLEN > 32) && (Pmode == DImode)))
#define HAVE_vec_duplicatevnx1qi (TARGET_VECTOR)
#define HAVE_vec_duplicatevnx2qi (TARGET_VECTOR)
#define HAVE_vec_duplicatevnx4qi (TARGET_VECTOR)
#define HAVE_vec_duplicatevnx8qi (TARGET_VECTOR)
#define HAVE_vec_duplicatevnx16qi (TARGET_VECTOR)
#define HAVE_vec_duplicatevnx32qi (TARGET_VECTOR)
#define HAVE_vec_duplicatevnx64qi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_vec_duplicatevnx1hi (TARGET_VECTOR)
#define HAVE_vec_duplicatevnx2hi (TARGET_VECTOR)
#define HAVE_vec_duplicatevnx4hi (TARGET_VECTOR)
#define HAVE_vec_duplicatevnx8hi (TARGET_VECTOR)
#define HAVE_vec_duplicatevnx16hi (TARGET_VECTOR)
#define HAVE_vec_duplicatevnx32hi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_vec_duplicatevnx1si (TARGET_VECTOR)
#define HAVE_vec_duplicatevnx2si (TARGET_VECTOR)
#define HAVE_vec_duplicatevnx4si (TARGET_VECTOR)
#define HAVE_vec_duplicatevnx8si (TARGET_VECTOR)
#define HAVE_vec_duplicatevnx16si ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_vec_duplicatevnx1di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_vec_duplicatevnx2di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_vec_duplicatevnx4di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_vec_duplicatevnx8di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_vec_duplicatevnx1sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_vec_duplicatevnx2sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_vec_duplicatevnx4sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_vec_duplicatevnx8sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_vec_duplicatevnx16sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32 && TARGET_MIN_VLEN > 32))
#define HAVE_vec_duplicatevnx1df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_vec_duplicatevnx2df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_vec_duplicatevnx4df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_vec_duplicatevnx8df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_mergevnx1di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_mergevnx2di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_mergevnx4di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_mergevnx8di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_broadcastvnx1qi (TARGET_VECTOR)
#define HAVE_pred_broadcastvnx2qi (TARGET_VECTOR)
#define HAVE_pred_broadcastvnx4qi (TARGET_VECTOR)
#define HAVE_pred_broadcastvnx8qi (TARGET_VECTOR)
#define HAVE_pred_broadcastvnx16qi (TARGET_VECTOR)
#define HAVE_pred_broadcastvnx32qi (TARGET_VECTOR)
#define HAVE_pred_broadcastvnx64qi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_broadcastvnx1hi (TARGET_VECTOR)
#define HAVE_pred_broadcastvnx2hi (TARGET_VECTOR)
#define HAVE_pred_broadcastvnx4hi (TARGET_VECTOR)
#define HAVE_pred_broadcastvnx8hi (TARGET_VECTOR)
#define HAVE_pred_broadcastvnx16hi (TARGET_VECTOR)
#define HAVE_pred_broadcastvnx32hi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_broadcastvnx1si (TARGET_VECTOR)
#define HAVE_pred_broadcastvnx2si (TARGET_VECTOR)
#define HAVE_pred_broadcastvnx4si (TARGET_VECTOR)
#define HAVE_pred_broadcastvnx8si (TARGET_VECTOR)
#define HAVE_pred_broadcastvnx16si ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_broadcastvnx1di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_broadcastvnx2di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_broadcastvnx4di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_broadcastvnx8di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_broadcastvnx1sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_broadcastvnx2sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_broadcastvnx4sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_broadcastvnx8sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_broadcastvnx16sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32 && TARGET_MIN_VLEN > 32))
#define HAVE_pred_broadcastvnx1df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_broadcastvnx2df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_broadcastvnx4df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_broadcastvnx8df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_addvnx1di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_andvnx1di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_iorvnx1di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_xorvnx1di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_smaxvnx1di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_umaxvnx1di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_sminvnx1di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_uminvnx1di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_mulvnx1di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_addvnx2di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_andvnx2di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_iorvnx2di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_xorvnx2di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_smaxvnx2di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_umaxvnx2di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_sminvnx2di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_uminvnx2di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_mulvnx2di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_addvnx4di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_andvnx4di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_iorvnx4di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_xorvnx4di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_smaxvnx4di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_umaxvnx4di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_sminvnx4di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_uminvnx4di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_mulvnx4di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_addvnx8di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_andvnx8di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_iorvnx8di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_xorvnx8di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_smaxvnx8di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_umaxvnx8di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_sminvnx8di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_uminvnx8di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_mulvnx8di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_subvnx1di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_divvnx1di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_udivvnx1di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_modvnx1di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_umodvnx1di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_subvnx2di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_divvnx2di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_udivvnx2di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_modvnx2di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_umodvnx2di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_subvnx4di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_divvnx4di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_udivvnx4di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_modvnx4di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_umodvnx4di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_subvnx8di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_divvnx8di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_udivvnx8di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_modvnx8di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_umodvnx8di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_subvnx1di_reverse_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_subvnx2di_reverse_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_subvnx4di_reverse_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_subvnx8di_reverse_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_mulhvnx1di_scalar ((TARGET_VECTOR) && (TARGET_FULL_V))
#define HAVE_pred_mulhuvnx1di_scalar ((TARGET_VECTOR) && (TARGET_FULL_V))
#define HAVE_pred_mulhsuvnx1di_scalar ((TARGET_VECTOR) && (TARGET_FULL_V))
#define HAVE_pred_mulhvnx2di_scalar ((TARGET_VECTOR) && (TARGET_FULL_V))
#define HAVE_pred_mulhuvnx2di_scalar ((TARGET_VECTOR) && (TARGET_FULL_V))
#define HAVE_pred_mulhsuvnx2di_scalar ((TARGET_VECTOR) && (TARGET_FULL_V))
#define HAVE_pred_mulhvnx4di_scalar ((TARGET_VECTOR) && (TARGET_FULL_V))
#define HAVE_pred_mulhuvnx4di_scalar ((TARGET_VECTOR) && (TARGET_FULL_V))
#define HAVE_pred_mulhsuvnx4di_scalar ((TARGET_VECTOR) && (TARGET_FULL_V))
#define HAVE_pred_mulhvnx8di_scalar ((TARGET_VECTOR) && (TARGET_FULL_V))
#define HAVE_pred_mulhuvnx8di_scalar ((TARGET_VECTOR) && (TARGET_FULL_V))
#define HAVE_pred_mulhsuvnx8di_scalar ((TARGET_VECTOR) && (TARGET_FULL_V))
#define HAVE_pred_adcvnx1di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_adcvnx2di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_adcvnx4di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_adcvnx8di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_sbcvnx1di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_sbcvnx2di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_sbcvnx4di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_sbcvnx8di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_madcvnx1di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_madcvnx2di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_madcvnx4di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_madcvnx8di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_msbcvnx1di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_msbcvnx2di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_msbcvnx4di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_msbcvnx8di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_madcvnx1di_overflow_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_madcvnx2di_overflow_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_madcvnx4di_overflow_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_madcvnx8di_overflow_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_msbcvnx1di_overflow_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_msbcvnx2di_overflow_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_msbcvnx4di_overflow_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_msbcvnx8di_overflow_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_ssaddvnx1di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_usaddvnx1di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_ssaddvnx2di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_usaddvnx2di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_ssaddvnx4di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_usaddvnx4di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_ssaddvnx8di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_usaddvnx8di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_sssubvnx1di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_ussubvnx1di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_sssubvnx2di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_ussubvnx2di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_sssubvnx4di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_ussubvnx4di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_sssubvnx8di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_ussubvnx8di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_aadduvnx1di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_aaddvnx1di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_asubuvnx1di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_asubvnx1di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_smulvnx1di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_aadduvnx2di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_aaddvnx2di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_asubuvnx2di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_asubvnx2di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_smulvnx2di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_aadduvnx4di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_aaddvnx4di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_asubuvnx4di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_asubvnx4di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_smulvnx4di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_aadduvnx8di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_aaddvnx8di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_asubuvnx8di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_asubvnx8di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_smulvnx8di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_cmpvnx1qi (TARGET_VECTOR)
#define HAVE_pred_cmpvnx2qi (TARGET_VECTOR)
#define HAVE_pred_cmpvnx4qi (TARGET_VECTOR)
#define HAVE_pred_cmpvnx8qi (TARGET_VECTOR)
#define HAVE_pred_cmpvnx16qi (TARGET_VECTOR)
#define HAVE_pred_cmpvnx32qi (TARGET_VECTOR)
#define HAVE_pred_cmpvnx64qi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_cmpvnx1hi (TARGET_VECTOR)
#define HAVE_pred_cmpvnx2hi (TARGET_VECTOR)
#define HAVE_pred_cmpvnx4hi (TARGET_VECTOR)
#define HAVE_pred_cmpvnx8hi (TARGET_VECTOR)
#define HAVE_pred_cmpvnx16hi (TARGET_VECTOR)
#define HAVE_pred_cmpvnx32hi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_cmpvnx1si (TARGET_VECTOR)
#define HAVE_pred_cmpvnx2si (TARGET_VECTOR)
#define HAVE_pred_cmpvnx4si (TARGET_VECTOR)
#define HAVE_pred_cmpvnx8si (TARGET_VECTOR)
#define HAVE_pred_cmpvnx16si ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_cmpvnx1di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_cmpvnx2di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_cmpvnx4di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_cmpvnx8di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_ltgevnx1qi (TARGET_VECTOR)
#define HAVE_pred_ltgevnx2qi (TARGET_VECTOR)
#define HAVE_pred_ltgevnx4qi (TARGET_VECTOR)
#define HAVE_pred_ltgevnx8qi (TARGET_VECTOR)
#define HAVE_pred_ltgevnx16qi (TARGET_VECTOR)
#define HAVE_pred_ltgevnx32qi (TARGET_VECTOR)
#define HAVE_pred_ltgevnx64qi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_ltgevnx1hi (TARGET_VECTOR)
#define HAVE_pred_ltgevnx2hi (TARGET_VECTOR)
#define HAVE_pred_ltgevnx4hi (TARGET_VECTOR)
#define HAVE_pred_ltgevnx8hi (TARGET_VECTOR)
#define HAVE_pred_ltgevnx16hi (TARGET_VECTOR)
#define HAVE_pred_ltgevnx32hi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_ltgevnx1si (TARGET_VECTOR)
#define HAVE_pred_ltgevnx2si (TARGET_VECTOR)
#define HAVE_pred_ltgevnx4si (TARGET_VECTOR)
#define HAVE_pred_ltgevnx8si (TARGET_VECTOR)
#define HAVE_pred_ltgevnx16si ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_ltgevnx1di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_ltgevnx2di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_ltgevnx4di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_ltgevnx8di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_cmpvnx1qi_scalar (TARGET_VECTOR)
#define HAVE_pred_cmpvnx2qi_scalar (TARGET_VECTOR)
#define HAVE_pred_cmpvnx4qi_scalar (TARGET_VECTOR)
#define HAVE_pred_cmpvnx8qi_scalar (TARGET_VECTOR)
#define HAVE_pred_cmpvnx16qi_scalar (TARGET_VECTOR)
#define HAVE_pred_cmpvnx32qi_scalar (TARGET_VECTOR)
#define HAVE_pred_cmpvnx64qi_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_cmpvnx1hi_scalar (TARGET_VECTOR)
#define HAVE_pred_cmpvnx2hi_scalar (TARGET_VECTOR)
#define HAVE_pred_cmpvnx4hi_scalar (TARGET_VECTOR)
#define HAVE_pred_cmpvnx8hi_scalar (TARGET_VECTOR)
#define HAVE_pred_cmpvnx16hi_scalar (TARGET_VECTOR)
#define HAVE_pred_cmpvnx32hi_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_cmpvnx1si_scalar (TARGET_VECTOR)
#define HAVE_pred_cmpvnx2si_scalar (TARGET_VECTOR)
#define HAVE_pred_cmpvnx4si_scalar (TARGET_VECTOR)
#define HAVE_pred_cmpvnx8si_scalar (TARGET_VECTOR)
#define HAVE_pred_cmpvnx16si_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_eqnevnx1qi_scalar (TARGET_VECTOR)
#define HAVE_pred_eqnevnx2qi_scalar (TARGET_VECTOR)
#define HAVE_pred_eqnevnx4qi_scalar (TARGET_VECTOR)
#define HAVE_pred_eqnevnx8qi_scalar (TARGET_VECTOR)
#define HAVE_pred_eqnevnx16qi_scalar (TARGET_VECTOR)
#define HAVE_pred_eqnevnx32qi_scalar (TARGET_VECTOR)
#define HAVE_pred_eqnevnx64qi_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_eqnevnx1hi_scalar (TARGET_VECTOR)
#define HAVE_pred_eqnevnx2hi_scalar (TARGET_VECTOR)
#define HAVE_pred_eqnevnx4hi_scalar (TARGET_VECTOR)
#define HAVE_pred_eqnevnx8hi_scalar (TARGET_VECTOR)
#define HAVE_pred_eqnevnx16hi_scalar (TARGET_VECTOR)
#define HAVE_pred_eqnevnx32hi_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_eqnevnx1si_scalar (TARGET_VECTOR)
#define HAVE_pred_eqnevnx2si_scalar (TARGET_VECTOR)
#define HAVE_pred_eqnevnx4si_scalar (TARGET_VECTOR)
#define HAVE_pred_eqnevnx8si_scalar (TARGET_VECTOR)
#define HAVE_pred_eqnevnx16si_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_cmpvnx1di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_cmpvnx2di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_cmpvnx4di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_cmpvnx8di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_eqnevnx1di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_eqnevnx2di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_eqnevnx4di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_eqnevnx8di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_gevnx1qi_scalar (TARGET_VECTOR)
#define HAVE_pred_gevnx2qi_scalar (TARGET_VECTOR)
#define HAVE_pred_gevnx4qi_scalar (TARGET_VECTOR)
#define HAVE_pred_gevnx8qi_scalar (TARGET_VECTOR)
#define HAVE_pred_gevnx16qi_scalar (TARGET_VECTOR)
#define HAVE_pred_gevnx32qi_scalar (TARGET_VECTOR)
#define HAVE_pred_gevnx64qi_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_gevnx1hi_scalar (TARGET_VECTOR)
#define HAVE_pred_gevnx2hi_scalar (TARGET_VECTOR)
#define HAVE_pred_gevnx4hi_scalar (TARGET_VECTOR)
#define HAVE_pred_gevnx8hi_scalar (TARGET_VECTOR)
#define HAVE_pred_gevnx16hi_scalar (TARGET_VECTOR)
#define HAVE_pred_gevnx32hi_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_gevnx1si_scalar (TARGET_VECTOR)
#define HAVE_pred_gevnx2si_scalar (TARGET_VECTOR)
#define HAVE_pred_gevnx4si_scalar (TARGET_VECTOR)
#define HAVE_pred_gevnx8si_scalar (TARGET_VECTOR)
#define HAVE_pred_gevnx16si_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_gevnx1di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_gevnx2di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_gevnx4di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_gevnx8di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_mul_plusvnx1qi (TARGET_VECTOR)
#define HAVE_pred_mul_plusvnx2qi (TARGET_VECTOR)
#define HAVE_pred_mul_plusvnx4qi (TARGET_VECTOR)
#define HAVE_pred_mul_plusvnx8qi (TARGET_VECTOR)
#define HAVE_pred_mul_plusvnx16qi (TARGET_VECTOR)
#define HAVE_pred_mul_plusvnx32qi (TARGET_VECTOR)
#define HAVE_pred_mul_plusvnx64qi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_mul_plusvnx1hi (TARGET_VECTOR)
#define HAVE_pred_mul_plusvnx2hi (TARGET_VECTOR)
#define HAVE_pred_mul_plusvnx4hi (TARGET_VECTOR)
#define HAVE_pred_mul_plusvnx8hi (TARGET_VECTOR)
#define HAVE_pred_mul_plusvnx16hi (TARGET_VECTOR)
#define HAVE_pred_mul_plusvnx32hi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_mul_plusvnx1si (TARGET_VECTOR)
#define HAVE_pred_mul_plusvnx2si (TARGET_VECTOR)
#define HAVE_pred_mul_plusvnx4si (TARGET_VECTOR)
#define HAVE_pred_mul_plusvnx8si (TARGET_VECTOR)
#define HAVE_pred_mul_plusvnx16si ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_mul_plusvnx1di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_mul_plusvnx2di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_mul_plusvnx4di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_mul_plusvnx8di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_mul_plusvnx1qi_scalar (TARGET_VECTOR)
#define HAVE_pred_mul_plusvnx2qi_scalar (TARGET_VECTOR)
#define HAVE_pred_mul_plusvnx4qi_scalar (TARGET_VECTOR)
#define HAVE_pred_mul_plusvnx8qi_scalar (TARGET_VECTOR)
#define HAVE_pred_mul_plusvnx16qi_scalar (TARGET_VECTOR)
#define HAVE_pred_mul_plusvnx32qi_scalar (TARGET_VECTOR)
#define HAVE_pred_mul_plusvnx64qi_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_mul_plusvnx1hi_scalar (TARGET_VECTOR)
#define HAVE_pred_mul_plusvnx2hi_scalar (TARGET_VECTOR)
#define HAVE_pred_mul_plusvnx4hi_scalar (TARGET_VECTOR)
#define HAVE_pred_mul_plusvnx8hi_scalar (TARGET_VECTOR)
#define HAVE_pred_mul_plusvnx16hi_scalar (TARGET_VECTOR)
#define HAVE_pred_mul_plusvnx32hi_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_mul_plusvnx1si_scalar (TARGET_VECTOR)
#define HAVE_pred_mul_plusvnx2si_scalar (TARGET_VECTOR)
#define HAVE_pred_mul_plusvnx4si_scalar (TARGET_VECTOR)
#define HAVE_pred_mul_plusvnx8si_scalar (TARGET_VECTOR)
#define HAVE_pred_mul_plusvnx16si_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_mul_plusvnx1di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_mul_plusvnx2di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_mul_plusvnx4di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_mul_plusvnx8di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_minus_mulvnx1qi (TARGET_VECTOR)
#define HAVE_pred_minus_mulvnx2qi (TARGET_VECTOR)
#define HAVE_pred_minus_mulvnx4qi (TARGET_VECTOR)
#define HAVE_pred_minus_mulvnx8qi (TARGET_VECTOR)
#define HAVE_pred_minus_mulvnx16qi (TARGET_VECTOR)
#define HAVE_pred_minus_mulvnx32qi (TARGET_VECTOR)
#define HAVE_pred_minus_mulvnx64qi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_minus_mulvnx1hi (TARGET_VECTOR)
#define HAVE_pred_minus_mulvnx2hi (TARGET_VECTOR)
#define HAVE_pred_minus_mulvnx4hi (TARGET_VECTOR)
#define HAVE_pred_minus_mulvnx8hi (TARGET_VECTOR)
#define HAVE_pred_minus_mulvnx16hi (TARGET_VECTOR)
#define HAVE_pred_minus_mulvnx32hi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_minus_mulvnx1si (TARGET_VECTOR)
#define HAVE_pred_minus_mulvnx2si (TARGET_VECTOR)
#define HAVE_pred_minus_mulvnx4si (TARGET_VECTOR)
#define HAVE_pred_minus_mulvnx8si (TARGET_VECTOR)
#define HAVE_pred_minus_mulvnx16si ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_minus_mulvnx1di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_minus_mulvnx2di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_minus_mulvnx4di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_minus_mulvnx8di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_minus_mulvnx1qi_scalar (TARGET_VECTOR)
#define HAVE_pred_minus_mulvnx2qi_scalar (TARGET_VECTOR)
#define HAVE_pred_minus_mulvnx4qi_scalar (TARGET_VECTOR)
#define HAVE_pred_minus_mulvnx8qi_scalar (TARGET_VECTOR)
#define HAVE_pred_minus_mulvnx16qi_scalar (TARGET_VECTOR)
#define HAVE_pred_minus_mulvnx32qi_scalar (TARGET_VECTOR)
#define HAVE_pred_minus_mulvnx64qi_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_minus_mulvnx1hi_scalar (TARGET_VECTOR)
#define HAVE_pred_minus_mulvnx2hi_scalar (TARGET_VECTOR)
#define HAVE_pred_minus_mulvnx4hi_scalar (TARGET_VECTOR)
#define HAVE_pred_minus_mulvnx8hi_scalar (TARGET_VECTOR)
#define HAVE_pred_minus_mulvnx16hi_scalar (TARGET_VECTOR)
#define HAVE_pred_minus_mulvnx32hi_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_minus_mulvnx1si_scalar (TARGET_VECTOR)
#define HAVE_pred_minus_mulvnx2si_scalar (TARGET_VECTOR)
#define HAVE_pred_minus_mulvnx4si_scalar (TARGET_VECTOR)
#define HAVE_pred_minus_mulvnx8si_scalar (TARGET_VECTOR)
#define HAVE_pred_minus_mulvnx16si_scalar ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_minus_mulvnx1di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_minus_mulvnx2di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_minus_mulvnx4di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_minus_mulvnx8di_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_mul_addvnx1sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_mul_subvnx1sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_mul_addvnx2sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_mul_subvnx2sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_mul_addvnx4sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_mul_subvnx4sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_mul_addvnx8sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_mul_subvnx8sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_mul_addvnx16sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32 && TARGET_MIN_VLEN > 32))
#define HAVE_pred_mul_subvnx16sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32 && TARGET_MIN_VLEN > 32))
#define HAVE_pred_mul_addvnx1df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_mul_subvnx1df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_mul_addvnx2df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_mul_subvnx2df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_mul_addvnx4df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_mul_subvnx4df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_mul_addvnx8df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_mul_subvnx8df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_mul_addvnx1sf_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_mul_subvnx1sf_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_mul_addvnx2sf_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_mul_subvnx2sf_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_mul_addvnx4sf_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_mul_subvnx4sf_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_mul_addvnx8sf_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_mul_subvnx8sf_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_mul_addvnx16sf_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32 && TARGET_MIN_VLEN > 32))
#define HAVE_pred_mul_subvnx16sf_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32 && TARGET_MIN_VLEN > 32))
#define HAVE_pred_mul_addvnx1df_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_mul_subvnx1df_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_mul_addvnx2df_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_mul_subvnx2df_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_mul_addvnx4df_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_mul_subvnx4df_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_mul_addvnx8df_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_mul_subvnx8df_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_mul_neg_addvnx1sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_mul_neg_subvnx1sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_mul_neg_addvnx2sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_mul_neg_subvnx2sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_mul_neg_addvnx4sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_mul_neg_subvnx4sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_mul_neg_addvnx8sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_mul_neg_subvnx8sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_mul_neg_addvnx16sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32 && TARGET_MIN_VLEN > 32))
#define HAVE_pred_mul_neg_subvnx16sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32 && TARGET_MIN_VLEN > 32))
#define HAVE_pred_mul_neg_addvnx1df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_mul_neg_subvnx1df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_mul_neg_addvnx2df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_mul_neg_subvnx2df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_mul_neg_addvnx4df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_mul_neg_subvnx4df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_mul_neg_addvnx8df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_mul_neg_subvnx8df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_mul_neg_addvnx1sf_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_mul_neg_subvnx1sf_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_mul_neg_addvnx2sf_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_mul_neg_subvnx2sf_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_mul_neg_addvnx4sf_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_mul_neg_subvnx4sf_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_mul_neg_addvnx8sf_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_mul_neg_subvnx8sf_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_mul_neg_addvnx16sf_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32 && TARGET_MIN_VLEN > 32))
#define HAVE_pred_mul_neg_subvnx16sf_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32 && TARGET_MIN_VLEN > 32))
#define HAVE_pred_mul_neg_addvnx1df_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_mul_neg_subvnx1df_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_mul_neg_addvnx2df_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_mul_neg_subvnx2df_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_mul_neg_addvnx4df_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_mul_neg_subvnx4df_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_mul_neg_addvnx8df_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_mul_neg_subvnx8df_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_cmpvnx1sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_cmpvnx2sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_cmpvnx4sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_cmpvnx8sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_cmpvnx16sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32 && TARGET_MIN_VLEN > 32))
#define HAVE_pred_cmpvnx1df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_cmpvnx2df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_cmpvnx4df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_cmpvnx8df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_cmpvnx1sf_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_cmpvnx2sf_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_cmpvnx4sf_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_cmpvnx8sf_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_cmpvnx16sf_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32 && TARGET_MIN_VLEN > 32))
#define HAVE_pred_cmpvnx1df_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_cmpvnx2df_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_cmpvnx4df_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_cmpvnx8df_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_eqnevnx1sf_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_eqnevnx2sf_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_eqnevnx4sf_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_eqnevnx8sf_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_eqnevnx16sf_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32 && TARGET_MIN_VLEN > 32))
#define HAVE_pred_eqnevnx1df_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_eqnevnx2df_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_eqnevnx4df_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_eqnevnx8df_scalar ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_extract_firstvnx1qi (TARGET_VECTOR)
#define HAVE_pred_extract_firstvnx2qi (TARGET_VECTOR)
#define HAVE_pred_extract_firstvnx4qi (TARGET_VECTOR)
#define HAVE_pred_extract_firstvnx8qi (TARGET_VECTOR)
#define HAVE_pred_extract_firstvnx16qi (TARGET_VECTOR)
#define HAVE_pred_extract_firstvnx32qi (TARGET_VECTOR)
#define HAVE_pred_extract_firstvnx64qi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_extract_firstvnx1hi (TARGET_VECTOR)
#define HAVE_pred_extract_firstvnx2hi (TARGET_VECTOR)
#define HAVE_pred_extract_firstvnx4hi (TARGET_VECTOR)
#define HAVE_pred_extract_firstvnx8hi (TARGET_VECTOR)
#define HAVE_pred_extract_firstvnx16hi (TARGET_VECTOR)
#define HAVE_pred_extract_firstvnx32hi ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_extract_firstvnx1si (TARGET_VECTOR)
#define HAVE_pred_extract_firstvnx2si (TARGET_VECTOR)
#define HAVE_pred_extract_firstvnx4si (TARGET_VECTOR)
#define HAVE_pred_extract_firstvnx8si (TARGET_VECTOR)
#define HAVE_pred_extract_firstvnx16si ((TARGET_VECTOR) && (TARGET_MIN_VLEN > 32))
#define HAVE_pred_extract_firstvnx1di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_extract_firstvnx2di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_extract_firstvnx4di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_extract_firstvnx8di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_extract_firstvnx1sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_extract_firstvnx2sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_extract_firstvnx4sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_extract_firstvnx8sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32))
#define HAVE_pred_extract_firstvnx16sf ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_32 && TARGET_MIN_VLEN > 32))
#define HAVE_pred_extract_firstvnx1df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_extract_firstvnx2df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_extract_firstvnx4df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_extract_firstvnx8df ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_FP_64))
#define HAVE_pred_slide1upvnx1di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_slide1downvnx1di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_slide1upvnx2di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_slide1downvnx2di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_slide1upvnx4di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_slide1downvnx4di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_slide1upvnx8di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
#define HAVE_pred_slide1downvnx8di ((TARGET_VECTOR) && (TARGET_VECTOR_ELEN_64))
extern rtx        gen_addsf3                                   (rtx, rtx, rtx);
extern rtx        gen_adddf3                                   (rtx, rtx, rtx);
extern rtx        gen_addhf3                                   (rtx, rtx, rtx);
extern rtx        gen_addsi3                                   (rtx, rtx, rtx);
extern rtx        gen_adddi3                                   (rtx, rtx, rtx);
extern rtx        gen_subsf3                                   (rtx, rtx, rtx);
extern rtx        gen_subdf3                                   (rtx, rtx, rtx);
extern rtx        gen_subhf3                                   (rtx, rtx, rtx);
extern rtx        gen_subdi3                                   (rtx, rtx, rtx);
extern rtx        gen_subsi3                                   (rtx, rtx, rtx);
extern rtx        gen_negdi2                                   (rtx, rtx);
extern rtx        gen_negsi2                                   (rtx, rtx);
extern rtx        gen_mulsf3                                   (rtx, rtx, rtx);
extern rtx        gen_muldf3                                   (rtx, rtx, rtx);
extern rtx        gen_mulhf3                                   (rtx, rtx, rtx);
extern rtx        gen_mulsi3                                   (rtx, rtx, rtx);
extern rtx        gen_muldi3                                   (rtx, rtx, rtx);
extern rtx        gen_smuldi3_highpart                         (rtx, rtx, rtx);
extern rtx        gen_umuldi3_highpart                         (rtx, rtx, rtx);
extern rtx        gen_usmuldi3_highpart                        (rtx, rtx, rtx);
extern rtx        gen_smulsi3_highpart                         (rtx, rtx, rtx);
extern rtx        gen_umulsi3_highpart                         (rtx, rtx, rtx);
extern rtx        gen_usmulsi3_highpart                        (rtx, rtx, rtx);
extern rtx        gen_divsi3                                   (rtx, rtx, rtx);
extern rtx        gen_udivsi3                                  (rtx, rtx, rtx);
extern rtx        gen_modsi3                                   (rtx, rtx, rtx);
extern rtx        gen_umodsi3                                  (rtx, rtx, rtx);
extern rtx        gen_divdi3                                   (rtx, rtx, rtx);
extern rtx        gen_udivdi3                                  (rtx, rtx, rtx);
extern rtx        gen_moddi3                                   (rtx, rtx, rtx);
extern rtx        gen_umoddi3                                  (rtx, rtx, rtx);
extern rtx        gen_divsf3                                   (rtx, rtx, rtx);
extern rtx        gen_divdf3                                   (rtx, rtx, rtx);
extern rtx        gen_divhf3                                   (rtx, rtx, rtx);
extern rtx        gen_sqrtsf2                                  (rtx, rtx);
extern rtx        gen_sqrtdf2                                  (rtx, rtx);
extern rtx        gen_sqrthf2                                  (rtx, rtx);
extern rtx        gen_fmasf4                                   (rtx, rtx, rtx, rtx);
extern rtx        gen_fmadf4                                   (rtx, rtx, rtx, rtx);
extern rtx        gen_fmahf4                                   (rtx, rtx, rtx, rtx);
extern rtx        gen_fmssf4                                   (rtx, rtx, rtx, rtx);
extern rtx        gen_fmsdf4                                   (rtx, rtx, rtx, rtx);
extern rtx        gen_fmshf4                                   (rtx, rtx, rtx, rtx);
extern rtx        gen_fnmssf4                                  (rtx, rtx, rtx, rtx);
extern rtx        gen_fnmsdf4                                  (rtx, rtx, rtx, rtx);
extern rtx        gen_fnmshf4                                  (rtx, rtx, rtx, rtx);
extern rtx        gen_fnmasf4                                  (rtx, rtx, rtx, rtx);
extern rtx        gen_fnmadf4                                  (rtx, rtx, rtx, rtx);
extern rtx        gen_fnmahf4                                  (rtx, rtx, rtx, rtx);
extern rtx        gen_abssf2                                   (rtx, rtx);
extern rtx        gen_absdf2                                   (rtx, rtx);
extern rtx        gen_abshf2                                   (rtx, rtx);
extern rtx        gen_copysignsf3                              (rtx, rtx, rtx);
extern rtx        gen_copysigndf3                              (rtx, rtx, rtx);
extern rtx        gen_copysignhf3                              (rtx, rtx, rtx);
extern rtx        gen_negsf2                                   (rtx, rtx);
extern rtx        gen_negdf2                                   (rtx, rtx);
extern rtx        gen_neghf2                                   (rtx, rtx);
extern rtx        gen_fminsf3                                  (rtx, rtx, rtx);
extern rtx        gen_fmindf3                                  (rtx, rtx, rtx);
extern rtx        gen_fminhf3                                  (rtx, rtx, rtx);
extern rtx        gen_fmaxsf3                                  (rtx, rtx, rtx);
extern rtx        gen_fmaxdf3                                  (rtx, rtx, rtx);
extern rtx        gen_fmaxhf3                                  (rtx, rtx, rtx);
extern rtx        gen_sminsf3                                  (rtx, rtx, rtx);
extern rtx        gen_smindf3                                  (rtx, rtx, rtx);
extern rtx        gen_sminhf3                                  (rtx, rtx, rtx);
extern rtx        gen_smaxsf3                                  (rtx, rtx, rtx);
extern rtx        gen_smaxdf3                                  (rtx, rtx, rtx);
extern rtx        gen_smaxhf3                                  (rtx, rtx, rtx);
extern rtx        gen_andsi3                                   (rtx, rtx, rtx);
extern rtx        gen_iorsi3                                   (rtx, rtx, rtx);
extern rtx        gen_xorsi3                                   (rtx, rtx, rtx);
extern rtx        gen_anddi3                                   (rtx, rtx, rtx);
extern rtx        gen_iordi3                                   (rtx, rtx, rtx);
extern rtx        gen_xordi3                                   (rtx, rtx, rtx);
extern rtx        gen_one_cmplsi2                              (rtx, rtx);
extern rtx        gen_one_cmpldi2                              (rtx, rtx);
extern rtx        gen_truncdfsf2                               (rtx, rtx);
extern rtx        gen_truncsfhf2                               (rtx, rtx);
extern rtx        gen_truncdfhf2                               (rtx, rtx);
extern rtx        gen_zero_extendqihi2                         (rtx, rtx);
extern rtx        gen_zero_extendqisi2                         (rtx, rtx);
extern rtx        gen_zero_extendqidi2                         (rtx, rtx);
extern rtx        gen_extendsidi2                              (rtx, rtx);
extern rtx        gen_extendhfsf2                              (rtx, rtx);
extern rtx        gen_extendsfdf2                              (rtx, rtx);
extern rtx        gen_extendhfdf2                              (rtx, rtx);
extern rtx        gen_fix_truncsfsi2                           (rtx, rtx);
extern rtx        gen_fix_truncsfdi2                           (rtx, rtx);
extern rtx        gen_fix_truncdfsi2                           (rtx, rtx);
extern rtx        gen_fix_truncdfdi2                           (rtx, rtx);
extern rtx        gen_fix_trunchfsi2                           (rtx, rtx);
extern rtx        gen_fix_trunchfdi2                           (rtx, rtx);
extern rtx        gen_fixuns_truncsfsi2                        (rtx, rtx);
extern rtx        gen_fixuns_truncsfdi2                        (rtx, rtx);
extern rtx        gen_fixuns_truncdfsi2                        (rtx, rtx);
extern rtx        gen_fixuns_truncdfdi2                        (rtx, rtx);
extern rtx        gen_fixuns_trunchfsi2                        (rtx, rtx);
extern rtx        gen_fixuns_trunchfdi2                        (rtx, rtx);
extern rtx        gen_floatsisf2                               (rtx, rtx);
extern rtx        gen_floatdisf2                               (rtx, rtx);
extern rtx        gen_floatsidf2                               (rtx, rtx);
extern rtx        gen_floatdidf2                               (rtx, rtx);
extern rtx        gen_floatsihf2                               (rtx, rtx);
extern rtx        gen_floatdihf2                               (rtx, rtx);
extern rtx        gen_floatunssisf2                            (rtx, rtx);
extern rtx        gen_floatunsdisf2                            (rtx, rtx);
extern rtx        gen_floatunssidf2                            (rtx, rtx);
extern rtx        gen_floatunsdidf2                            (rtx, rtx);
extern rtx        gen_floatunssihf2                            (rtx, rtx);
extern rtx        gen_floatunsdihf2                            (rtx, rtx);
extern rtx        gen_lrintsfsi2                               (rtx, rtx);
extern rtx        gen_lroundsfsi2                              (rtx, rtx);
extern rtx        gen_lrintsfdi2                               (rtx, rtx);
extern rtx        gen_lroundsfdi2                              (rtx, rtx);
extern rtx        gen_lrintdfsi2                               (rtx, rtx);
extern rtx        gen_lrounddfsi2                              (rtx, rtx);
extern rtx        gen_lrintdfdi2                               (rtx, rtx);
extern rtx        gen_lrounddfdi2                              (rtx, rtx);
extern rtx        gen_lrinthfsi2                               (rtx, rtx);
extern rtx        gen_lroundhfsi2                              (rtx, rtx);
extern rtx        gen_lrinthfdi2                               (rtx, rtx);
extern rtx        gen_lroundhfdi2                              (rtx, rtx);
extern rtx        gen_got_loadsi                               (rtx, rtx);
extern rtx        gen_got_loaddi                               (rtx, rtx);
extern rtx        gen_tls_add_tp_lesi                          (rtx, rtx, rtx, rtx);
extern rtx        gen_tls_add_tp_ledi                          (rtx, rtx, rtx, rtx);
extern rtx        gen_got_load_tls_gdsi                        (rtx, rtx);
extern rtx        gen_got_load_tls_gddi                        (rtx, rtx);
extern rtx        gen_got_load_tls_iesi                        (rtx, rtx);
extern rtx        gen_got_load_tls_iedi                        (rtx, rtx);
extern rtx        gen_auipcsi                                  (rtx, rtx, rtx);
extern rtx        gen_auipcdi                                  (rtx, rtx, rtx);
extern rtx        gen_fence                                    (void);
extern rtx        gen_fence_i                                  (void);
extern rtx        gen_riscv_pause                              (void);
extern rtx        gen_ashlsi3                                  (rtx, rtx, rtx);
extern rtx        gen_ashrsi3                                  (rtx, rtx, rtx);
extern rtx        gen_lshrsi3                                  (rtx, rtx, rtx);
extern rtx        gen_ashldi3                                  (rtx, rtx, rtx);
extern rtx        gen_ashrdi3                                  (rtx, rtx, rtx);
extern rtx        gen_lshrdi3                                  (rtx, rtx, rtx);
extern rtx        gen_zero_extendsidi2_shifted                 (rtx, rtx, rtx, rtx);
extern rtx        gen_jump                                     (rtx);
extern rtx        gen_indirect_jumpsi                          (rtx);
extern rtx        gen_indirect_jumpdi                          (rtx);
extern rtx        gen_tablejumpsi                              (rtx, rtx);
extern rtx        gen_tablejumpdi                              (rtx, rtx);
extern rtx        gen_blockage                                 (void);
extern rtx        gen_simple_return                            (void);
extern rtx        gen_simple_return_internal                   (rtx);
extern rtx        gen_eh_set_lr_si                             (rtx);
extern rtx        gen_eh_set_lr_di                             (rtx);
extern rtx        gen_eh_return_internal                       (void);
extern rtx        gen_sibcall_internal                         (rtx, rtx);
extern rtx        gen_sibcall_value_internal                   (rtx, rtx, rtx);
extern rtx        gen_call_internal                            (rtx, rtx);
extern rtx        gen_call_value_internal                      (rtx, rtx, rtx);
extern rtx        gen_nop                                      (void);
extern rtx        gen_trap                                     (void);
extern rtx        gen_gpr_save                                 (rtx, rtx);
extern rtx        gen_gpr_restore                              (rtx);
extern rtx        gen_gpr_restore_return                       (rtx);
extern rtx        gen_riscv_frflags                            (rtx);
extern rtx        gen_riscv_fsflags                            (rtx);
extern rtx        gen_riscv_mret                               (void);
extern rtx        gen_riscv_sret                               (void);
extern rtx        gen_riscv_uret                               (void);
extern rtx        gen_stack_tiesi                              (rtx, rtx);
extern rtx        gen_stack_tiedi                              (rtx, rtx);
extern rtx        gen_stack_protect_set_si                     (rtx, rtx);
extern rtx        gen_stack_protect_set_di                     (rtx, rtx);
extern rtx        gen_stack_protect_test_si                    (rtx, rtx, rtx);
extern rtx        gen_stack_protect_test_di                    (rtx, rtx, rtx);
extern rtx        gen_riscv_clean_si                           (rtx);
extern rtx        gen_riscv_clean_di                           (rtx);
extern rtx        gen_riscv_flush_si                           (rtx);
extern rtx        gen_riscv_flush_di                           (rtx);
extern rtx        gen_riscv_inval_si                           (rtx);
extern rtx        gen_riscv_inval_di                           (rtx);
extern rtx        gen_riscv_zero_si                            (rtx);
extern rtx        gen_riscv_zero_di                            (rtx);
extern rtx        gen_prefetch                                 (rtx, rtx, rtx);
extern rtx        gen_riscv_prefetchi_si                       (rtx, rtx);
extern rtx        gen_riscv_prefetchi_di                       (rtx, rtx);
extern rtx        gen_rotlsi3                                  (rtx, rtx, rtx);
extern rtx        gen_rotldi3                                  (rtx, rtx, rtx);
extern rtx        gen_rotlsi3_sext                             (rtx, rtx, rtx);
extern rtx        gen_orcbsi2                                  (rtx, rtx);
extern rtx        gen_orcbdi2                                  (rtx, rtx);
extern rtx        gen_sminsi3                                  (rtx, rtx, rtx);
extern rtx        gen_uminsi3                                  (rtx, rtx, rtx);
extern rtx        gen_smaxsi3                                  (rtx, rtx, rtx);
extern rtx        gen_umaxsi3                                  (rtx, rtx, rtx);
extern rtx        gen_smindi3                                  (rtx, rtx, rtx);
extern rtx        gen_umindi3                                  (rtx, rtx, rtx);
extern rtx        gen_smaxdi3                                  (rtx, rtx, rtx);
extern rtx        gen_umaxdi3                                  (rtx, rtx, rtx);
extern rtx        gen_riscv_brev8_si                           (rtx, rtx);
extern rtx        gen_riscv_brev8_di                           (rtx, rtx);
extern rtx        gen_riscv_zip                                (rtx, rtx);
extern rtx        gen_riscv_unzip                              (rtx, rtx);
extern rtx        gen_riscv_pack_sihi                          (rtx, rtx, rtx);
extern rtx        gen_riscv_pack_sisi                          (rtx, rtx, rtx);
extern rtx        gen_riscv_pack_dihi                          (rtx, rtx, rtx);
extern rtx        gen_riscv_pack_disi                          (rtx, rtx, rtx);
extern rtx        gen_riscv_packh_si                           (rtx, rtx, rtx);
extern rtx        gen_riscv_packh_di                           (rtx, rtx, rtx);
extern rtx        gen_riscv_packw                              (rtx, rtx, rtx);
extern rtx        gen_riscv_clmul_si                           (rtx, rtx, rtx);
extern rtx        gen_riscv_clmul_di                           (rtx, rtx, rtx);
extern rtx        gen_riscv_clmulh_si                          (rtx, rtx, rtx);
extern rtx        gen_riscv_clmulh_di                          (rtx, rtx, rtx);
extern rtx        gen_riscv_xperm4_si                          (rtx, rtx, rtx);
extern rtx        gen_riscv_xperm4_di                          (rtx, rtx, rtx);
extern rtx        gen_riscv_xperm8_si                          (rtx, rtx, rtx);
extern rtx        gen_riscv_xperm8_di                          (rtx, rtx, rtx);
extern rtx        gen_riscv_aes32dsi                           (rtx, rtx, rtx, rtx);
extern rtx        gen_riscv_aes32dsmi                          (rtx, rtx, rtx, rtx);
extern rtx        gen_riscv_aes64ds                            (rtx, rtx, rtx);
extern rtx        gen_riscv_aes64dsm                           (rtx, rtx, rtx);
extern rtx        gen_riscv_aes64im                            (rtx, rtx);
extern rtx        gen_riscv_aes64ks1i                          (rtx, rtx, rtx);
extern rtx        gen_riscv_aes64ks2                           (rtx, rtx, rtx);
extern rtx        gen_riscv_aes32esi                           (rtx, rtx, rtx, rtx);
extern rtx        gen_riscv_aes32esmi                          (rtx, rtx, rtx, rtx);
extern rtx        gen_riscv_aes64es                            (rtx, rtx, rtx);
extern rtx        gen_riscv_aes64esm                           (rtx, rtx, rtx);
extern rtx        gen_riscv_sha256sig0_si                      (rtx, rtx);
extern rtx        gen_riscv_sha256sig0_di                      (rtx, rtx);
extern rtx        gen_riscv_sha256sig1_si                      (rtx, rtx);
extern rtx        gen_riscv_sha256sig1_di                      (rtx, rtx);
extern rtx        gen_riscv_sha256sum0_si                      (rtx, rtx);
extern rtx        gen_riscv_sha256sum0_di                      (rtx, rtx);
extern rtx        gen_riscv_sha256sum1_si                      (rtx, rtx);
extern rtx        gen_riscv_sha256sum1_di                      (rtx, rtx);
extern rtx        gen_riscv_sha512sig0h                        (rtx, rtx, rtx);
extern rtx        gen_riscv_sha512sig0l                        (rtx, rtx, rtx);
extern rtx        gen_riscv_sha512sig1h                        (rtx, rtx, rtx);
extern rtx        gen_riscv_sha512sig1l                        (rtx, rtx, rtx);
extern rtx        gen_riscv_sha512sum0r                        (rtx, rtx, rtx);
extern rtx        gen_riscv_sha512sum1r                        (rtx, rtx, rtx);
extern rtx        gen_riscv_sha512sig0                         (rtx, rtx);
extern rtx        gen_riscv_sha512sig1                         (rtx, rtx);
extern rtx        gen_riscv_sha512sum0                         (rtx, rtx);
extern rtx        gen_riscv_sha512sum1                         (rtx, rtx);
extern rtx        gen_riscv_sm3p0_si                           (rtx, rtx);
extern rtx        gen_riscv_sm3p0_di                           (rtx, rtx);
extern rtx        gen_riscv_sm3p1_si                           (rtx, rtx);
extern rtx        gen_riscv_sm3p1_di                           (rtx, rtx);
extern rtx        gen_riscv_sm4ed_si                           (rtx, rtx, rtx, rtx);
extern rtx        gen_riscv_sm4ed_di                           (rtx, rtx, rtx, rtx);
extern rtx        gen_riscv_sm4ks_si                           (rtx, rtx, rtx, rtx);
extern rtx        gen_riscv_sm4ks_di                           (rtx, rtx, rtx, rtx);
extern rtx        gen_mem_thread_fence_1                       (rtx, rtx);
extern rtx        gen_atomic_storesi                           (rtx, rtx, rtx);
extern rtx        gen_atomic_storedi                           (rtx, rtx, rtx);
extern rtx        gen_atomic_addsi                             (rtx, rtx, rtx);
extern rtx        gen_atomic_orsi                              (rtx, rtx, rtx);
extern rtx        gen_atomic_xorsi                             (rtx, rtx, rtx);
extern rtx        gen_atomic_andsi                             (rtx, rtx, rtx);
extern rtx        gen_atomic_adddi                             (rtx, rtx, rtx);
extern rtx        gen_atomic_ordi                              (rtx, rtx, rtx);
extern rtx        gen_atomic_xordi                             (rtx, rtx, rtx);
extern rtx        gen_atomic_anddi                             (rtx, rtx, rtx);
extern rtx        gen_atomic_fetch_addsi                       (rtx, rtx, rtx, rtx);
extern rtx        gen_atomic_fetch_orsi                        (rtx, rtx, rtx, rtx);
extern rtx        gen_atomic_fetch_xorsi                       (rtx, rtx, rtx, rtx);
extern rtx        gen_atomic_fetch_andsi                       (rtx, rtx, rtx, rtx);
extern rtx        gen_atomic_fetch_adddi                       (rtx, rtx, rtx, rtx);
extern rtx        gen_atomic_fetch_ordi                        (rtx, rtx, rtx, rtx);
extern rtx        gen_atomic_fetch_xordi                       (rtx, rtx, rtx, rtx);
extern rtx        gen_atomic_fetch_anddi                       (rtx, rtx, rtx, rtx);
extern rtx        gen_atomic_exchangesi                        (rtx, rtx, rtx, rtx);
extern rtx        gen_atomic_exchangedi                        (rtx, rtx, rtx, rtx);
extern rtx        gen_atomic_cas_value_strongsi                (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_atomic_cas_value_strongdi                (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_th_fmv_hw_w_x                            (rtx, rtx, rtx);
extern rtx        gen_th_fmv_x_w                               (rtx, rtx);
extern rtx        gen_th_fmv_x_hw                              (rtx, rtx);
extern rtx        gen_vundefinedvnx1qi                         (rtx);
extern rtx        gen_vundefinedvnx2qi                         (rtx);
extern rtx        gen_vundefinedvnx4qi                         (rtx);
extern rtx        gen_vundefinedvnx8qi                         (rtx);
extern rtx        gen_vundefinedvnx16qi                        (rtx);
extern rtx        gen_vundefinedvnx32qi                        (rtx);
extern rtx        gen_vundefinedvnx64qi                        (rtx);
extern rtx        gen_vundefinedvnx1hi                         (rtx);
extern rtx        gen_vundefinedvnx2hi                         (rtx);
extern rtx        gen_vundefinedvnx4hi                         (rtx);
extern rtx        gen_vundefinedvnx8hi                         (rtx);
extern rtx        gen_vundefinedvnx16hi                        (rtx);
extern rtx        gen_vundefinedvnx32hi                        (rtx);
extern rtx        gen_vundefinedvnx1si                         (rtx);
extern rtx        gen_vundefinedvnx2si                         (rtx);
extern rtx        gen_vundefinedvnx4si                         (rtx);
extern rtx        gen_vundefinedvnx8si                         (rtx);
extern rtx        gen_vundefinedvnx16si                        (rtx);
extern rtx        gen_vundefinedvnx1di                         (rtx);
extern rtx        gen_vundefinedvnx2di                         (rtx);
extern rtx        gen_vundefinedvnx4di                         (rtx);
extern rtx        gen_vundefinedvnx8di                         (rtx);
extern rtx        gen_vundefinedvnx1sf                         (rtx);
extern rtx        gen_vundefinedvnx2sf                         (rtx);
extern rtx        gen_vundefinedvnx4sf                         (rtx);
extern rtx        gen_vundefinedvnx8sf                         (rtx);
extern rtx        gen_vundefinedvnx16sf                        (rtx);
extern rtx        gen_vundefinedvnx1df                         (rtx);
extern rtx        gen_vundefinedvnx2df                         (rtx);
extern rtx        gen_vundefinedvnx4df                         (rtx);
extern rtx        gen_vundefinedvnx8df                         (rtx);
extern rtx        gen_vundefinedvnx1bi                         (rtx);
extern rtx        gen_vundefinedvnx2bi                         (rtx);
extern rtx        gen_vundefinedvnx4bi                         (rtx);
extern rtx        gen_vundefinedvnx8bi                         (rtx);
extern rtx        gen_vundefinedvnx16bi                        (rtx);
extern rtx        gen_vundefinedvnx32bi                        (rtx);
extern rtx        gen_vundefinedvnx64bi                        (rtx);
extern rtx        gen_vlmax_avlsi                              (rtx, rtx);
extern rtx        gen_vlmax_avldi                              (rtx, rtx);
extern rtx        gen_vsetvlsi                                 (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_vsetvldi                                 (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_vsetvl_vtype_change_only                 (rtx, rtx, rtx, rtx);
extern rtx        gen_vsetvl_discard_resultsi                  (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_vsetvl_discard_resultdi                  (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_vsetvlsi_no_side_effects                 (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_vsetvldi_no_side_effects                 (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_movvnx1qi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_movvnx2qi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_movvnx4qi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_movvnx8qi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_movvnx16qi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_movvnx32qi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_movvnx64qi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_movvnx1hi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_movvnx2hi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_movvnx4hi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_movvnx8hi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_movvnx16hi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_movvnx32hi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_movvnx1si                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_movvnx2si                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_movvnx4si                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_movvnx8si                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_movvnx16si                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_movvnx1di                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_movvnx2di                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_movvnx4di                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_movvnx8di                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_movvnx1sf                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_movvnx2sf                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_movvnx4sf                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_movvnx8sf                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_movvnx16sf                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_movvnx1df                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_movvnx2df                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_movvnx4df                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_movvnx8df                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_storevnx1qi                         (rtx, rtx, rtx, rtx);
extern rtx        gen_pred_storevnx2qi                         (rtx, rtx, rtx, rtx);
extern rtx        gen_pred_storevnx4qi                         (rtx, rtx, rtx, rtx);
extern rtx        gen_pred_storevnx8qi                         (rtx, rtx, rtx, rtx);
extern rtx        gen_pred_storevnx16qi                        (rtx, rtx, rtx, rtx);
extern rtx        gen_pred_storevnx32qi                        (rtx, rtx, rtx, rtx);
extern rtx        gen_pred_storevnx64qi                        (rtx, rtx, rtx, rtx);
extern rtx        gen_pred_storevnx1hi                         (rtx, rtx, rtx, rtx);
extern rtx        gen_pred_storevnx2hi                         (rtx, rtx, rtx, rtx);
extern rtx        gen_pred_storevnx4hi                         (rtx, rtx, rtx, rtx);
extern rtx        gen_pred_storevnx8hi                         (rtx, rtx, rtx, rtx);
extern rtx        gen_pred_storevnx16hi                        (rtx, rtx, rtx, rtx);
extern rtx        gen_pred_storevnx32hi                        (rtx, rtx, rtx, rtx);
extern rtx        gen_pred_storevnx1si                         (rtx, rtx, rtx, rtx);
extern rtx        gen_pred_storevnx2si                         (rtx, rtx, rtx, rtx);
extern rtx        gen_pred_storevnx4si                         (rtx, rtx, rtx, rtx);
extern rtx        gen_pred_storevnx8si                         (rtx, rtx, rtx, rtx);
extern rtx        gen_pred_storevnx16si                        (rtx, rtx, rtx, rtx);
extern rtx        gen_pred_storevnx1di                         (rtx, rtx, rtx, rtx);
extern rtx        gen_pred_storevnx2di                         (rtx, rtx, rtx, rtx);
extern rtx        gen_pred_storevnx4di                         (rtx, rtx, rtx, rtx);
extern rtx        gen_pred_storevnx8di                         (rtx, rtx, rtx, rtx);
extern rtx        gen_pred_storevnx1sf                         (rtx, rtx, rtx, rtx);
extern rtx        gen_pred_storevnx2sf                         (rtx, rtx, rtx, rtx);
extern rtx        gen_pred_storevnx4sf                         (rtx, rtx, rtx, rtx);
extern rtx        gen_pred_storevnx8sf                         (rtx, rtx, rtx, rtx);
extern rtx        gen_pred_storevnx16sf                        (rtx, rtx, rtx, rtx);
extern rtx        gen_pred_storevnx1df                         (rtx, rtx, rtx, rtx);
extern rtx        gen_pred_storevnx2df                         (rtx, rtx, rtx, rtx);
extern rtx        gen_pred_storevnx4df                         (rtx, rtx, rtx, rtx);
extern rtx        gen_pred_storevnx8df                         (rtx, rtx, rtx, rtx);
extern rtx        gen_pred_movvnx1bi                           (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_movvnx2bi                           (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_movvnx4bi                           (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_movvnx8bi                           (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_movvnx16bi                          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_movvnx32bi                          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_movvnx64bi                          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_storevnx1bi                         (rtx, rtx, rtx, rtx);
extern rtx        gen_pred_storevnx2bi                         (rtx, rtx, rtx, rtx);
extern rtx        gen_pred_storevnx4bi                         (rtx, rtx, rtx, rtx);
extern rtx        gen_pred_storevnx8bi                         (rtx, rtx, rtx, rtx);
extern rtx        gen_pred_storevnx16bi                        (rtx, rtx, rtx, rtx);
extern rtx        gen_pred_storevnx32bi                        (rtx, rtx, rtx, rtx);
extern rtx        gen_pred_storevnx64bi                        (rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mergevnx1qi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mergevnx2qi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mergevnx4qi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mergevnx8qi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mergevnx16qi                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mergevnx32qi                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mergevnx64qi                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mergevnx1hi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mergevnx2hi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mergevnx4hi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mergevnx8hi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mergevnx16hi                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mergevnx32hi                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mergevnx1si                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mergevnx2si                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mergevnx4si                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mergevnx8si                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mergevnx16si                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mergevnx1di                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mergevnx2di                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mergevnx4di                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mergevnx8di                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mergevnx1sf                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mergevnx2sf                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mergevnx4sf                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mergevnx8sf                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mergevnx16sf                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mergevnx1df                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mergevnx2df                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mergevnx4df                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mergevnx8df                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mergevnx1qi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mergevnx2qi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mergevnx4qi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mergevnx8qi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mergevnx16qi_scalar                 (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mergevnx32qi_scalar                 (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mergevnx64qi_scalar                 (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mergevnx1hi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mergevnx2hi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mergevnx4hi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mergevnx8hi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mergevnx16hi_scalar                 (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mergevnx32hi_scalar                 (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mergevnx1si_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mergevnx2si_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mergevnx4si_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mergevnx8si_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mergevnx16si_scalar                 (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_strided_loadvnx1qi                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_strided_loadvnx2qi                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_strided_loadvnx4qi                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_strided_loadvnx8qi                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_strided_loadvnx16qi                 (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_strided_loadvnx32qi                 (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_strided_loadvnx64qi                 (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_strided_loadvnx1hi                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_strided_loadvnx2hi                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_strided_loadvnx4hi                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_strided_loadvnx8hi                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_strided_loadvnx16hi                 (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_strided_loadvnx32hi                 (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_strided_loadvnx1si                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_strided_loadvnx2si                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_strided_loadvnx4si                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_strided_loadvnx8si                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_strided_loadvnx16si                 (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_strided_loadvnx1di                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_strided_loadvnx2di                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_strided_loadvnx4di                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_strided_loadvnx8di                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_strided_loadvnx1sf                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_strided_loadvnx2sf                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_strided_loadvnx4sf                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_strided_loadvnx8sf                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_strided_loadvnx16sf                 (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_strided_loadvnx1df                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_strided_loadvnx2df                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_strided_loadvnx4df                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_strided_loadvnx8df                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_strided_storevnx1qi                 (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_strided_storevnx2qi                 (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_strided_storevnx4qi                 (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_strided_storevnx8qi                 (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_strided_storevnx16qi                (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_strided_storevnx32qi                (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_strided_storevnx64qi                (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_strided_storevnx1hi                 (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_strided_storevnx2hi                 (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_strided_storevnx4hi                 (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_strided_storevnx8hi                 (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_strided_storevnx16hi                (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_strided_storevnx32hi                (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_strided_storevnx1si                 (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_strided_storevnx2si                 (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_strided_storevnx4si                 (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_strided_storevnx8si                 (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_strided_storevnx16si                (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_strided_storevnx1di                 (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_strided_storevnx2di                 (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_strided_storevnx4di                 (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_strided_storevnx8di                 (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_strided_storevnx1sf                 (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_strided_storevnx2sf                 (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_strided_storevnx4sf                 (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_strided_storevnx8sf                 (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_strided_storevnx16sf                (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_strided_storevnx1df                 (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_strided_storevnx2df                 (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_strided_storevnx4df                 (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_strided_storevnx8df                 (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_oloadvnx1qi_same_eew        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_uloadvnx1qi_same_eew        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_oloadvnx2qi_same_eew        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_uloadvnx2qi_same_eew        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_oloadvnx4qi_same_eew        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_uloadvnx4qi_same_eew        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_oloadvnx8qi_same_eew        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_uloadvnx8qi_same_eew        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_oloadvnx16qi_same_eew       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_uloadvnx16qi_same_eew       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_oloadvnx32qi_same_eew       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_uloadvnx32qi_same_eew       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_oloadvnx64qi_same_eew       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_uloadvnx64qi_same_eew       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_oloadvnx1hi_same_eew        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_uloadvnx1hi_same_eew        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_oloadvnx2hi_same_eew        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_uloadvnx2hi_same_eew        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_oloadvnx4hi_same_eew        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_uloadvnx4hi_same_eew        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_oloadvnx8hi_same_eew        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_uloadvnx8hi_same_eew        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_oloadvnx16hi_same_eew       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_uloadvnx16hi_same_eew       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_oloadvnx32hi_same_eew       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_uloadvnx32hi_same_eew       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_oloadvnx1si_same_eew        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_uloadvnx1si_same_eew        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_oloadvnx2si_same_eew        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_uloadvnx2si_same_eew        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_oloadvnx4si_same_eew        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_uloadvnx4si_same_eew        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_oloadvnx8si_same_eew        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_uloadvnx8si_same_eew        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_oloadvnx16si_same_eew       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_uloadvnx16si_same_eew       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_oloadvnx1di_same_eew        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_uloadvnx1di_same_eew        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_oloadvnx2di_same_eew        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_uloadvnx2di_same_eew        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_oloadvnx4di_same_eew        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_uloadvnx4di_same_eew        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_oloadvnx8di_same_eew        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_uloadvnx8di_same_eew        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_oloadvnx1sf_same_eew        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_uloadvnx1sf_same_eew        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_oloadvnx2sf_same_eew        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_uloadvnx2sf_same_eew        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_oloadvnx4sf_same_eew        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_uloadvnx4sf_same_eew        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_oloadvnx8sf_same_eew        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_uloadvnx8sf_same_eew        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_oloadvnx16sf_same_eew       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_uloadvnx16sf_same_eew       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_oloadvnx1df_same_eew        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_uloadvnx1df_same_eew        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_oloadvnx2df_same_eew        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_uloadvnx2df_same_eew        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_oloadvnx4df_same_eew        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_uloadvnx4df_same_eew        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_oloadvnx8df_same_eew        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_uloadvnx8df_same_eew        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_oloadvnx1hi_x2_greater_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_uloadvnx1hi_x2_greater_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_oloadvnx2hi_x2_greater_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_uloadvnx2hi_x2_greater_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_oloadvnx4hi_x2_greater_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_uloadvnx4hi_x2_greater_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_oloadvnx8hi_x2_greater_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_uloadvnx8hi_x2_greater_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_oloadvnx16hi_x2_greater_eew (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_uloadvnx16hi_x2_greater_eew (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_oloadvnx32hi_x2_greater_eew (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_uloadvnx32hi_x2_greater_eew (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_oloadvnx1si_x2_greater_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_uloadvnx1si_x2_greater_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_oloadvnx2si_x2_greater_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_uloadvnx2si_x2_greater_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_oloadvnx4si_x2_greater_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_uloadvnx4si_x2_greater_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_oloadvnx8si_x2_greater_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_uloadvnx8si_x2_greater_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_oloadvnx16si_x2_greater_eew (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_uloadvnx16si_x2_greater_eew (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_oloadvnx1di_x2_greater_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_uloadvnx1di_x2_greater_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_oloadvnx2di_x2_greater_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_uloadvnx2di_x2_greater_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_oloadvnx4di_x2_greater_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_uloadvnx4di_x2_greater_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_oloadvnx8di_x2_greater_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_uloadvnx8di_x2_greater_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_oloadvnx1sf_x2_greater_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_uloadvnx1sf_x2_greater_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_oloadvnx2sf_x2_greater_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_uloadvnx2sf_x2_greater_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_oloadvnx4sf_x2_greater_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_uloadvnx4sf_x2_greater_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_oloadvnx8sf_x2_greater_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_uloadvnx8sf_x2_greater_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_oloadvnx16sf_x2_greater_eew (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_uloadvnx16sf_x2_greater_eew (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_oloadvnx1df_x2_greater_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_uloadvnx1df_x2_greater_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_oloadvnx2df_x2_greater_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_uloadvnx2df_x2_greater_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_oloadvnx4df_x2_greater_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_uloadvnx4df_x2_greater_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_oloadvnx8df_x2_greater_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_uloadvnx8df_x2_greater_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_oloadvnx1si_x4_greater_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_uloadvnx1si_x4_greater_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_oloadvnx2si_x4_greater_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_uloadvnx2si_x4_greater_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_oloadvnx4si_x4_greater_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_uloadvnx4si_x4_greater_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_oloadvnx8si_x4_greater_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_uloadvnx8si_x4_greater_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_oloadvnx16si_x4_greater_eew (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_uloadvnx16si_x4_greater_eew (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_oloadvnx1di_x4_greater_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_uloadvnx1di_x4_greater_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_oloadvnx2di_x4_greater_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_uloadvnx2di_x4_greater_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_oloadvnx4di_x4_greater_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_uloadvnx4di_x4_greater_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_oloadvnx8di_x4_greater_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_uloadvnx8di_x4_greater_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_oloadvnx1sf_x4_greater_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_uloadvnx1sf_x4_greater_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_oloadvnx2sf_x4_greater_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_uloadvnx2sf_x4_greater_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_oloadvnx4sf_x4_greater_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_uloadvnx4sf_x4_greater_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_oloadvnx8sf_x4_greater_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_uloadvnx8sf_x4_greater_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_oloadvnx16sf_x4_greater_eew (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_uloadvnx16sf_x4_greater_eew (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_oloadvnx1df_x4_greater_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_uloadvnx1df_x4_greater_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_oloadvnx2df_x4_greater_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_uloadvnx2df_x4_greater_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_oloadvnx4df_x4_greater_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_uloadvnx4df_x4_greater_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_oloadvnx8df_x4_greater_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_uloadvnx8df_x4_greater_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_oloadvnx1di_x8_greater_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_uloadvnx1di_x8_greater_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_oloadvnx2di_x8_greater_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_uloadvnx2di_x8_greater_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_oloadvnx4di_x8_greater_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_uloadvnx4di_x8_greater_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_oloadvnx8di_x8_greater_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_uloadvnx8di_x8_greater_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_oloadvnx1df_x8_greater_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_uloadvnx1df_x8_greater_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_oloadvnx2df_x8_greater_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_uloadvnx2df_x8_greater_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_oloadvnx4df_x8_greater_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_uloadvnx4df_x8_greater_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_oloadvnx8df_x8_greater_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_uloadvnx8df_x8_greater_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_oloadvnx1qi_x2_smaller_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_uloadvnx1qi_x2_smaller_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_oloadvnx2qi_x2_smaller_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_uloadvnx2qi_x2_smaller_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_oloadvnx4qi_x2_smaller_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_uloadvnx4qi_x2_smaller_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_oloadvnx8qi_x2_smaller_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_uloadvnx8qi_x2_smaller_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_oloadvnx16qi_x2_smaller_eew (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_uloadvnx16qi_x2_smaller_eew (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_oloadvnx32qi_x2_smaller_eew (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_uloadvnx32qi_x2_smaller_eew (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_oloadvnx1hi_x2_smaller_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_uloadvnx1hi_x2_smaller_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_oloadvnx2hi_x2_smaller_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_uloadvnx2hi_x2_smaller_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_oloadvnx4hi_x2_smaller_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_uloadvnx4hi_x2_smaller_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_oloadvnx8hi_x2_smaller_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_uloadvnx8hi_x2_smaller_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_oloadvnx16hi_x2_smaller_eew (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_uloadvnx16hi_x2_smaller_eew (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_oloadvnx1si_x2_smaller_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_uloadvnx1si_x2_smaller_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_oloadvnx2si_x2_smaller_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_uloadvnx2si_x2_smaller_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_oloadvnx4si_x2_smaller_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_uloadvnx4si_x2_smaller_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_oloadvnx8si_x2_smaller_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_uloadvnx8si_x2_smaller_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_oloadvnx1sf_x2_smaller_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_uloadvnx1sf_x2_smaller_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_oloadvnx2sf_x2_smaller_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_uloadvnx2sf_x2_smaller_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_oloadvnx4sf_x2_smaller_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_uloadvnx4sf_x2_smaller_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_oloadvnx8sf_x2_smaller_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_uloadvnx8sf_x2_smaller_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_oloadvnx1qi_x4_smaller_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_uloadvnx1qi_x4_smaller_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_oloadvnx2qi_x4_smaller_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_uloadvnx2qi_x4_smaller_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_oloadvnx4qi_x4_smaller_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_uloadvnx4qi_x4_smaller_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_oloadvnx8qi_x4_smaller_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_uloadvnx8qi_x4_smaller_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_oloadvnx16qi_x4_smaller_eew (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_uloadvnx16qi_x4_smaller_eew (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_oloadvnx1hi_x4_smaller_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_uloadvnx1hi_x4_smaller_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_oloadvnx2hi_x4_smaller_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_uloadvnx2hi_x4_smaller_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_oloadvnx4hi_x4_smaller_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_uloadvnx4hi_x4_smaller_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_oloadvnx8hi_x4_smaller_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_uloadvnx8hi_x4_smaller_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_oloadvnx1qi_x8_smaller_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_uloadvnx1qi_x8_smaller_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_oloadvnx2qi_x8_smaller_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_uloadvnx2qi_x8_smaller_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_oloadvnx4qi_x8_smaller_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_uloadvnx4qi_x8_smaller_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_oloadvnx8qi_x8_smaller_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_uloadvnx8qi_x8_smaller_eew  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ostorevnx1qivnx1qi          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ustorevnx1qivnx1qi          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ostorevnx1qivnx1hi          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ustorevnx1qivnx1hi          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ostorevnx1qivnx1si          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ustorevnx1qivnx1si          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ostorevnx1qivnx1di          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ustorevnx1qivnx1di          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ostorevnx1hivnx1qi          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ustorevnx1hivnx1qi          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ostorevnx1hivnx1hi          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ustorevnx1hivnx1hi          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ostorevnx1hivnx1si          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ustorevnx1hivnx1si          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ostorevnx1hivnx1di          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ustorevnx1hivnx1di          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ostorevnx1sivnx1qi          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ustorevnx1sivnx1qi          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ostorevnx1sivnx1hi          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ustorevnx1sivnx1hi          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ostorevnx1sivnx1si          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ustorevnx1sivnx1si          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ostorevnx1sivnx1di          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ustorevnx1sivnx1di          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ostorevnx1divnx1qi          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ustorevnx1divnx1qi          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ostorevnx1divnx1hi          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ustorevnx1divnx1hi          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ostorevnx1divnx1si          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ustorevnx1divnx1si          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ostorevnx1divnx1di          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ustorevnx1divnx1di          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ostorevnx1sfvnx1qi          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ustorevnx1sfvnx1qi          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ostorevnx1sfvnx1hi          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ustorevnx1sfvnx1hi          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ostorevnx1sfvnx1si          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ustorevnx1sfvnx1si          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ostorevnx1sfvnx1di          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ustorevnx1sfvnx1di          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ostorevnx1dfvnx1qi          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ustorevnx1dfvnx1qi          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ostorevnx1dfvnx1hi          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ustorevnx1dfvnx1hi          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ostorevnx1dfvnx1si          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ustorevnx1dfvnx1si          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ostorevnx1dfvnx1di          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ustorevnx1dfvnx1di          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ostorevnx2qivnx2qi          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ustorevnx2qivnx2qi          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ostorevnx2hivnx2qi          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ustorevnx2hivnx2qi          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ostorevnx2sivnx2qi          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ustorevnx2sivnx2qi          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ostorevnx2divnx2qi          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ustorevnx2divnx2qi          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ostorevnx2sfvnx2qi          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ustorevnx2sfvnx2qi          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ostorevnx2dfvnx2qi          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ustorevnx2dfvnx2qi          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ostorevnx2qivnx2hi          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ustorevnx2qivnx2hi          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ostorevnx2hivnx2hi          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ustorevnx2hivnx2hi          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ostorevnx2sivnx2hi          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ustorevnx2sivnx2hi          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ostorevnx2divnx2hi          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ustorevnx2divnx2hi          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ostorevnx2sfvnx2hi          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ustorevnx2sfvnx2hi          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ostorevnx2dfvnx2hi          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ustorevnx2dfvnx2hi          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ostorevnx2qivnx2si          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ustorevnx2qivnx2si          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ostorevnx2hivnx2si          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ustorevnx2hivnx2si          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ostorevnx2sivnx2si          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ustorevnx2sivnx2si          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ostorevnx2divnx2si          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ustorevnx2divnx2si          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ostorevnx2sfvnx2si          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ustorevnx2sfvnx2si          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ostorevnx2dfvnx2si          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ustorevnx2dfvnx2si          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ostorevnx2qivnx2di          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ustorevnx2qivnx2di          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ostorevnx2hivnx2di          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ustorevnx2hivnx2di          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ostorevnx2sivnx2di          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ustorevnx2sivnx2di          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ostorevnx2divnx2di          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ustorevnx2divnx2di          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ostorevnx2sfvnx2di          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ustorevnx2sfvnx2di          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ostorevnx2dfvnx2di          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ustorevnx2dfvnx2di          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ostorevnx4qivnx4qi          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ustorevnx4qivnx4qi          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ostorevnx4hivnx4qi          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ustorevnx4hivnx4qi          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ostorevnx4sivnx4qi          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ustorevnx4sivnx4qi          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ostorevnx4divnx4qi          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ustorevnx4divnx4qi          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ostorevnx4sfvnx4qi          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ustorevnx4sfvnx4qi          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ostorevnx4dfvnx4qi          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ustorevnx4dfvnx4qi          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ostorevnx4qivnx4hi          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ustorevnx4qivnx4hi          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ostorevnx4hivnx4hi          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ustorevnx4hivnx4hi          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ostorevnx4sivnx4hi          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ustorevnx4sivnx4hi          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ostorevnx4divnx4hi          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ustorevnx4divnx4hi          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ostorevnx4sfvnx4hi          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ustorevnx4sfvnx4hi          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ostorevnx4dfvnx4hi          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ustorevnx4dfvnx4hi          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ostorevnx4qivnx4si          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ustorevnx4qivnx4si          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ostorevnx4hivnx4si          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ustorevnx4hivnx4si          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ostorevnx4sivnx4si          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ustorevnx4sivnx4si          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ostorevnx4divnx4si          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ustorevnx4divnx4si          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ostorevnx4sfvnx4si          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ustorevnx4sfvnx4si          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ostorevnx4dfvnx4si          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ustorevnx4dfvnx4si          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ostorevnx4qivnx4di          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ustorevnx4qivnx4di          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ostorevnx4hivnx4di          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ustorevnx4hivnx4di          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ostorevnx4sivnx4di          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ustorevnx4sivnx4di          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ostorevnx4divnx4di          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ustorevnx4divnx4di          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ostorevnx4sfvnx4di          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ustorevnx4sfvnx4di          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ostorevnx4dfvnx4di          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ustorevnx4dfvnx4di          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ostorevnx8qivnx8qi          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ustorevnx8qivnx8qi          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ostorevnx8hivnx8qi          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ustorevnx8hivnx8qi          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ostorevnx8sivnx8qi          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ustorevnx8sivnx8qi          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ostorevnx8divnx8qi          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ustorevnx8divnx8qi          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ostorevnx8sfvnx8qi          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ustorevnx8sfvnx8qi          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ostorevnx8dfvnx8qi          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ustorevnx8dfvnx8qi          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ostorevnx8qivnx8hi          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ustorevnx8qivnx8hi          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ostorevnx8hivnx8hi          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ustorevnx8hivnx8hi          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ostorevnx8sivnx8hi          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ustorevnx8sivnx8hi          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ostorevnx8divnx8hi          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ustorevnx8divnx8hi          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ostorevnx8sfvnx8hi          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ustorevnx8sfvnx8hi          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ostorevnx8dfvnx8hi          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ustorevnx8dfvnx8hi          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ostorevnx8qivnx8si          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ustorevnx8qivnx8si          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ostorevnx8hivnx8si          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ustorevnx8hivnx8si          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ostorevnx8sivnx8si          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ustorevnx8sivnx8si          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ostorevnx8divnx8si          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ustorevnx8divnx8si          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ostorevnx8sfvnx8si          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ustorevnx8sfvnx8si          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ostorevnx8dfvnx8si          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ustorevnx8dfvnx8si          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ostorevnx8qivnx8di          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ustorevnx8qivnx8di          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ostorevnx8hivnx8di          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ustorevnx8hivnx8di          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ostorevnx8sivnx8di          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ustorevnx8sivnx8di          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ostorevnx8divnx8di          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ustorevnx8divnx8di          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ostorevnx8sfvnx8di          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ustorevnx8sfvnx8di          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ostorevnx8dfvnx8di          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ustorevnx8dfvnx8di          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ostorevnx16qivnx16qi        (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ustorevnx16qivnx16qi        (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ostorevnx16hivnx16qi        (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ustorevnx16hivnx16qi        (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ostorevnx16sivnx16qi        (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ustorevnx16sivnx16qi        (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ostorevnx16sfvnx16qi        (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ustorevnx16sfvnx16qi        (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ostorevnx16qivnx16hi        (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ustorevnx16qivnx16hi        (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ostorevnx16hivnx16hi        (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ustorevnx16hivnx16hi        (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ostorevnx16sivnx16hi        (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ustorevnx16sivnx16hi        (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ostorevnx16sfvnx16hi        (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ustorevnx16sfvnx16hi        (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ostorevnx16qivnx16si        (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ustorevnx16qivnx16si        (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ostorevnx16hivnx16si        (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ustorevnx16hivnx16si        (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ostorevnx16sivnx16si        (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ustorevnx16sivnx16si        (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ostorevnx16sfvnx16si        (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ustorevnx16sfvnx16si        (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ostorevnx32qivnx32qi        (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ustorevnx32qivnx32qi        (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ostorevnx32qivnx32hi        (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ustorevnx32qivnx32hi        (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ostorevnx32hivnx32qi        (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ustorevnx32hivnx32qi        (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ostorevnx32hivnx32hi        (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ustorevnx32hivnx32hi        (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ostorevnx64qivnx64qi        (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_indexed_ustorevnx64qivnx64qi        (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_addvnx1qi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_subvnx1qi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_andvnx1qi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_iorvnx1qi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_xorvnx1qi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ashlvnx1qi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ashrvnx1qi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_lshrvnx1qi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_smaxvnx1qi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_umaxvnx1qi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sminvnx1qi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_uminvnx1qi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulvnx1qi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_divvnx1qi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_udivvnx1qi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_modvnx1qi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_umodvnx1qi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_addvnx2qi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_subvnx2qi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_andvnx2qi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_iorvnx2qi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_xorvnx2qi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ashlvnx2qi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ashrvnx2qi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_lshrvnx2qi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_smaxvnx2qi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_umaxvnx2qi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sminvnx2qi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_uminvnx2qi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulvnx2qi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_divvnx2qi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_udivvnx2qi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_modvnx2qi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_umodvnx2qi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_addvnx4qi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_subvnx4qi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_andvnx4qi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_iorvnx4qi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_xorvnx4qi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ashlvnx4qi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ashrvnx4qi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_lshrvnx4qi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_smaxvnx4qi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_umaxvnx4qi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sminvnx4qi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_uminvnx4qi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulvnx4qi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_divvnx4qi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_udivvnx4qi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_modvnx4qi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_umodvnx4qi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_addvnx8qi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_subvnx8qi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_andvnx8qi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_iorvnx8qi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_xorvnx8qi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ashlvnx8qi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ashrvnx8qi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_lshrvnx8qi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_smaxvnx8qi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_umaxvnx8qi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sminvnx8qi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_uminvnx8qi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulvnx8qi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_divvnx8qi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_udivvnx8qi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_modvnx8qi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_umodvnx8qi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_addvnx16qi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_subvnx16qi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_andvnx16qi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_iorvnx16qi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_xorvnx16qi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ashlvnx16qi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ashrvnx16qi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_lshrvnx16qi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_smaxvnx16qi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_umaxvnx16qi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sminvnx16qi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_uminvnx16qi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulvnx16qi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_divvnx16qi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_udivvnx16qi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_modvnx16qi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_umodvnx16qi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_addvnx32qi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_subvnx32qi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_andvnx32qi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_iorvnx32qi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_xorvnx32qi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ashlvnx32qi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ashrvnx32qi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_lshrvnx32qi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_smaxvnx32qi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_umaxvnx32qi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sminvnx32qi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_uminvnx32qi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulvnx32qi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_divvnx32qi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_udivvnx32qi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_modvnx32qi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_umodvnx32qi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_addvnx64qi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_subvnx64qi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_andvnx64qi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_iorvnx64qi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_xorvnx64qi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ashlvnx64qi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ashrvnx64qi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_lshrvnx64qi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_smaxvnx64qi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_umaxvnx64qi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sminvnx64qi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_uminvnx64qi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulvnx64qi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_divvnx64qi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_udivvnx64qi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_modvnx64qi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_umodvnx64qi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_addvnx1hi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_subvnx1hi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_andvnx1hi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_iorvnx1hi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_xorvnx1hi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ashlvnx1hi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ashrvnx1hi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_lshrvnx1hi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_smaxvnx1hi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_umaxvnx1hi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sminvnx1hi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_uminvnx1hi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulvnx1hi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_divvnx1hi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_udivvnx1hi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_modvnx1hi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_umodvnx1hi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_addvnx2hi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_subvnx2hi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_andvnx2hi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_iorvnx2hi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_xorvnx2hi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ashlvnx2hi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ashrvnx2hi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_lshrvnx2hi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_smaxvnx2hi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_umaxvnx2hi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sminvnx2hi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_uminvnx2hi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulvnx2hi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_divvnx2hi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_udivvnx2hi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_modvnx2hi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_umodvnx2hi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_addvnx4hi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_subvnx4hi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_andvnx4hi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_iorvnx4hi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_xorvnx4hi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ashlvnx4hi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ashrvnx4hi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_lshrvnx4hi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_smaxvnx4hi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_umaxvnx4hi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sminvnx4hi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_uminvnx4hi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulvnx4hi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_divvnx4hi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_udivvnx4hi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_modvnx4hi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_umodvnx4hi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_addvnx8hi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_subvnx8hi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_andvnx8hi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_iorvnx8hi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_xorvnx8hi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ashlvnx8hi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ashrvnx8hi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_lshrvnx8hi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_smaxvnx8hi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_umaxvnx8hi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sminvnx8hi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_uminvnx8hi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulvnx8hi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_divvnx8hi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_udivvnx8hi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_modvnx8hi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_umodvnx8hi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_addvnx16hi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_subvnx16hi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_andvnx16hi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_iorvnx16hi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_xorvnx16hi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ashlvnx16hi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ashrvnx16hi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_lshrvnx16hi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_smaxvnx16hi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_umaxvnx16hi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sminvnx16hi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_uminvnx16hi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulvnx16hi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_divvnx16hi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_udivvnx16hi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_modvnx16hi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_umodvnx16hi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_addvnx32hi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_subvnx32hi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_andvnx32hi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_iorvnx32hi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_xorvnx32hi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ashlvnx32hi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ashrvnx32hi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_lshrvnx32hi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_smaxvnx32hi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_umaxvnx32hi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sminvnx32hi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_uminvnx32hi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulvnx32hi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_divvnx32hi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_udivvnx32hi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_modvnx32hi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_umodvnx32hi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_addvnx1si                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_subvnx1si                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_andvnx1si                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_iorvnx1si                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_xorvnx1si                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ashlvnx1si                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ashrvnx1si                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_lshrvnx1si                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_smaxvnx1si                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_umaxvnx1si                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sminvnx1si                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_uminvnx1si                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulvnx1si                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_divvnx1si                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_udivvnx1si                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_modvnx1si                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_umodvnx1si                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_addvnx2si                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_subvnx2si                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_andvnx2si                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_iorvnx2si                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_xorvnx2si                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ashlvnx2si                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ashrvnx2si                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_lshrvnx2si                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_smaxvnx2si                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_umaxvnx2si                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sminvnx2si                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_uminvnx2si                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulvnx2si                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_divvnx2si                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_udivvnx2si                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_modvnx2si                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_umodvnx2si                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_addvnx4si                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_subvnx4si                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_andvnx4si                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_iorvnx4si                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_xorvnx4si                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ashlvnx4si                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ashrvnx4si                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_lshrvnx4si                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_smaxvnx4si                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_umaxvnx4si                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sminvnx4si                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_uminvnx4si                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulvnx4si                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_divvnx4si                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_udivvnx4si                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_modvnx4si                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_umodvnx4si                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_addvnx8si                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_subvnx8si                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_andvnx8si                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_iorvnx8si                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_xorvnx8si                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ashlvnx8si                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ashrvnx8si                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_lshrvnx8si                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_smaxvnx8si                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_umaxvnx8si                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sminvnx8si                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_uminvnx8si                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulvnx8si                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_divvnx8si                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_udivvnx8si                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_modvnx8si                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_umodvnx8si                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_addvnx16si                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_subvnx16si                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_andvnx16si                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_iorvnx16si                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_xorvnx16si                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ashlvnx16si                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ashrvnx16si                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_lshrvnx16si                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_smaxvnx16si                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_umaxvnx16si                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sminvnx16si                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_uminvnx16si                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulvnx16si                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_divvnx16si                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_udivvnx16si                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_modvnx16si                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_umodvnx16si                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_addvnx1di                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_subvnx1di                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_andvnx1di                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_iorvnx1di                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_xorvnx1di                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ashlvnx1di                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ashrvnx1di                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_lshrvnx1di                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_smaxvnx1di                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_umaxvnx1di                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sminvnx1di                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_uminvnx1di                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulvnx1di                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_divvnx1di                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_udivvnx1di                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_modvnx1di                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_umodvnx1di                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_addvnx2di                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_subvnx2di                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_andvnx2di                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_iorvnx2di                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_xorvnx2di                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ashlvnx2di                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ashrvnx2di                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_lshrvnx2di                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_smaxvnx2di                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_umaxvnx2di                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sminvnx2di                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_uminvnx2di                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulvnx2di                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_divvnx2di                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_udivvnx2di                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_modvnx2di                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_umodvnx2di                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_addvnx4di                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_subvnx4di                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_andvnx4di                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_iorvnx4di                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_xorvnx4di                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ashlvnx4di                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ashrvnx4di                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_lshrvnx4di                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_smaxvnx4di                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_umaxvnx4di                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sminvnx4di                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_uminvnx4di                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulvnx4di                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_divvnx4di                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_udivvnx4di                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_modvnx4di                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_umodvnx4di                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_addvnx8di                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_subvnx8di                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_andvnx8di                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_iorvnx8di                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_xorvnx8di                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ashlvnx8di                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ashrvnx8di                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_lshrvnx8di                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_smaxvnx8di                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_umaxvnx8di                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sminvnx8di                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_uminvnx8di                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulvnx8di                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_divvnx8di                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_udivvnx8di                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_modvnx8di                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_umodvnx8di                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ashlvnx1qi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ashrvnx1qi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_lshrvnx1qi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ashlvnx2qi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ashrvnx2qi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_lshrvnx2qi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ashlvnx4qi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ashrvnx4qi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_lshrvnx4qi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ashlvnx8qi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ashrvnx8qi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_lshrvnx8qi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ashlvnx16qi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ashrvnx16qi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_lshrvnx16qi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ashlvnx32qi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ashrvnx32qi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_lshrvnx32qi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ashlvnx64qi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ashrvnx64qi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_lshrvnx64qi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ashlvnx1hi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ashrvnx1hi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_lshrvnx1hi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ashlvnx2hi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ashrvnx2hi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_lshrvnx2hi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ashlvnx4hi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ashrvnx4hi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_lshrvnx4hi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ashlvnx8hi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ashrvnx8hi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_lshrvnx8hi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ashlvnx16hi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ashrvnx16hi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_lshrvnx16hi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ashlvnx32hi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ashrvnx32hi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_lshrvnx32hi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ashlvnx1si_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ashrvnx1si_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_lshrvnx1si_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ashlvnx2si_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ashrvnx2si_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_lshrvnx2si_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ashlvnx4si_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ashrvnx4si_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_lshrvnx4si_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ashlvnx8si_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ashrvnx8si_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_lshrvnx8si_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ashlvnx16si_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ashrvnx16si_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_lshrvnx16si_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ashlvnx1di_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ashrvnx1di_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_lshrvnx1di_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ashlvnx2di_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ashrvnx2di_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_lshrvnx2di_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ashlvnx4di_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ashrvnx4di_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_lshrvnx4di_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ashlvnx8di_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ashrvnx8di_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_lshrvnx8di_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_addvnx1qi_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_andvnx1qi_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_iorvnx1qi_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_xorvnx1qi_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_smaxvnx1qi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_umaxvnx1qi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sminvnx1qi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_uminvnx1qi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulvnx1qi_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_addvnx2qi_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_andvnx2qi_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_iorvnx2qi_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_xorvnx2qi_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_smaxvnx2qi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_umaxvnx2qi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sminvnx2qi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_uminvnx2qi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulvnx2qi_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_addvnx4qi_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_andvnx4qi_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_iorvnx4qi_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_xorvnx4qi_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_smaxvnx4qi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_umaxvnx4qi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sminvnx4qi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_uminvnx4qi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulvnx4qi_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_addvnx8qi_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_andvnx8qi_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_iorvnx8qi_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_xorvnx8qi_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_smaxvnx8qi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_umaxvnx8qi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sminvnx8qi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_uminvnx8qi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulvnx8qi_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_addvnx16qi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_andvnx16qi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_iorvnx16qi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_xorvnx16qi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_smaxvnx16qi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_umaxvnx16qi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sminvnx16qi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_uminvnx16qi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulvnx16qi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_addvnx32qi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_andvnx32qi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_iorvnx32qi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_xorvnx32qi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_smaxvnx32qi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_umaxvnx32qi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sminvnx32qi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_uminvnx32qi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulvnx32qi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_addvnx64qi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_andvnx64qi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_iorvnx64qi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_xorvnx64qi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_smaxvnx64qi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_umaxvnx64qi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sminvnx64qi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_uminvnx64qi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulvnx64qi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_addvnx1hi_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_andvnx1hi_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_iorvnx1hi_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_xorvnx1hi_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_smaxvnx1hi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_umaxvnx1hi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sminvnx1hi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_uminvnx1hi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulvnx1hi_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_addvnx2hi_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_andvnx2hi_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_iorvnx2hi_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_xorvnx2hi_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_smaxvnx2hi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_umaxvnx2hi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sminvnx2hi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_uminvnx2hi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulvnx2hi_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_addvnx4hi_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_andvnx4hi_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_iorvnx4hi_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_xorvnx4hi_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_smaxvnx4hi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_umaxvnx4hi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sminvnx4hi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_uminvnx4hi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulvnx4hi_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_addvnx8hi_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_andvnx8hi_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_iorvnx8hi_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_xorvnx8hi_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_smaxvnx8hi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_umaxvnx8hi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sminvnx8hi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_uminvnx8hi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulvnx8hi_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_addvnx16hi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_andvnx16hi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_iorvnx16hi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_xorvnx16hi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_smaxvnx16hi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_umaxvnx16hi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sminvnx16hi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_uminvnx16hi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulvnx16hi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_addvnx32hi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_andvnx32hi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_iorvnx32hi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_xorvnx32hi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_smaxvnx32hi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_umaxvnx32hi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sminvnx32hi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_uminvnx32hi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulvnx32hi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_addvnx1si_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_andvnx1si_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_iorvnx1si_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_xorvnx1si_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_smaxvnx1si_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_umaxvnx1si_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sminvnx1si_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_uminvnx1si_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulvnx1si_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_addvnx2si_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_andvnx2si_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_iorvnx2si_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_xorvnx2si_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_smaxvnx2si_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_umaxvnx2si_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sminvnx2si_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_uminvnx2si_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulvnx2si_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_addvnx4si_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_andvnx4si_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_iorvnx4si_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_xorvnx4si_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_smaxvnx4si_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_umaxvnx4si_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sminvnx4si_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_uminvnx4si_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulvnx4si_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_addvnx8si_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_andvnx8si_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_iorvnx8si_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_xorvnx8si_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_smaxvnx8si_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_umaxvnx8si_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sminvnx8si_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_uminvnx8si_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulvnx8si_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_addvnx16si_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_andvnx16si_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_iorvnx16si_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_xorvnx16si_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_smaxvnx16si_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_umaxvnx16si_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sminvnx16si_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_uminvnx16si_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulvnx16si_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_subvnx1qi_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_divvnx1qi_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_udivvnx1qi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_modvnx1qi_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_umodvnx1qi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_subvnx2qi_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_divvnx2qi_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_udivvnx2qi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_modvnx2qi_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_umodvnx2qi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_subvnx4qi_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_divvnx4qi_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_udivvnx4qi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_modvnx4qi_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_umodvnx4qi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_subvnx8qi_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_divvnx8qi_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_udivvnx8qi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_modvnx8qi_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_umodvnx8qi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_subvnx16qi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_divvnx16qi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_udivvnx16qi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_modvnx16qi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_umodvnx16qi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_subvnx32qi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_divvnx32qi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_udivvnx32qi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_modvnx32qi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_umodvnx32qi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_subvnx64qi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_divvnx64qi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_udivvnx64qi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_modvnx64qi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_umodvnx64qi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_subvnx1hi_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_divvnx1hi_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_udivvnx1hi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_modvnx1hi_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_umodvnx1hi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_subvnx2hi_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_divvnx2hi_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_udivvnx2hi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_modvnx2hi_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_umodvnx2hi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_subvnx4hi_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_divvnx4hi_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_udivvnx4hi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_modvnx4hi_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_umodvnx4hi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_subvnx8hi_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_divvnx8hi_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_udivvnx8hi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_modvnx8hi_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_umodvnx8hi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_subvnx16hi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_divvnx16hi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_udivvnx16hi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_modvnx16hi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_umodvnx16hi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_subvnx32hi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_divvnx32hi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_udivvnx32hi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_modvnx32hi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_umodvnx32hi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_subvnx1si_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_divvnx1si_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_udivvnx1si_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_modvnx1si_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_umodvnx1si_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_subvnx2si_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_divvnx2si_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_udivvnx2si_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_modvnx2si_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_umodvnx2si_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_subvnx4si_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_divvnx4si_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_udivvnx4si_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_modvnx4si_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_umodvnx4si_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_subvnx8si_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_divvnx8si_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_udivvnx8si_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_modvnx8si_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_umodvnx8si_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_subvnx16si_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_divvnx16si_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_udivvnx16si_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_modvnx16si_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_umodvnx16si_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_subvnx1qi_reverse_scalar            (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_subvnx2qi_reverse_scalar            (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_subvnx4qi_reverse_scalar            (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_subvnx8qi_reverse_scalar            (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_subvnx16qi_reverse_scalar           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_subvnx32qi_reverse_scalar           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_subvnx64qi_reverse_scalar           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_subvnx1hi_reverse_scalar            (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_subvnx2hi_reverse_scalar            (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_subvnx4hi_reverse_scalar            (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_subvnx8hi_reverse_scalar            (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_subvnx16hi_reverse_scalar           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_subvnx32hi_reverse_scalar           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_subvnx1si_reverse_scalar            (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_subvnx2si_reverse_scalar            (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_subvnx4si_reverse_scalar            (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_subvnx8si_reverse_scalar            (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_subvnx16si_reverse_scalar           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhvnx1qi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhuvnx1qi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhsuvnx1qi                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhvnx2qi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhuvnx2qi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhsuvnx2qi                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhvnx4qi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhuvnx4qi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhsuvnx4qi                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhvnx8qi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhuvnx8qi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhsuvnx8qi                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhvnx16qi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhuvnx16qi                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhsuvnx16qi                       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhvnx32qi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhuvnx32qi                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhsuvnx32qi                       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhvnx64qi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhuvnx64qi                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhsuvnx64qi                       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhvnx1hi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhuvnx1hi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhsuvnx1hi                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhvnx2hi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhuvnx2hi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhsuvnx2hi                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhvnx4hi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhuvnx4hi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhsuvnx4hi                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhvnx8hi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhuvnx8hi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhsuvnx8hi                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhvnx16hi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhuvnx16hi                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhsuvnx16hi                       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhvnx32hi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhuvnx32hi                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhsuvnx32hi                       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhvnx1si                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhuvnx1si                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhsuvnx1si                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhvnx2si                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhuvnx2si                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhsuvnx2si                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhvnx4si                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhuvnx4si                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhsuvnx4si                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhvnx8si                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhuvnx8si                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhsuvnx8si                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhvnx16si                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhuvnx16si                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhsuvnx16si                       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhvnx1di                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhuvnx1di                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhsuvnx1di                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhvnx2di                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhuvnx2di                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhsuvnx2di                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhvnx4di                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhuvnx4di                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhsuvnx4di                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhvnx8di                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhuvnx8di                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhsuvnx8di                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhvnx1qi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhuvnx1qi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhsuvnx1qi_scalar                 (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhvnx2qi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhuvnx2qi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhsuvnx2qi_scalar                 (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhvnx4qi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhuvnx4qi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhsuvnx4qi_scalar                 (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhvnx8qi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhuvnx8qi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhsuvnx8qi_scalar                 (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhvnx16qi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhuvnx16qi_scalar                 (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhsuvnx16qi_scalar                (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhvnx32qi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhuvnx32qi_scalar                 (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhsuvnx32qi_scalar                (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhvnx64qi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhuvnx64qi_scalar                 (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhsuvnx64qi_scalar                (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhvnx1hi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhuvnx1hi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhsuvnx1hi_scalar                 (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhvnx2hi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhuvnx2hi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhsuvnx2hi_scalar                 (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhvnx4hi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhuvnx4hi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhsuvnx4hi_scalar                 (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhvnx8hi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhuvnx8hi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhsuvnx8hi_scalar                 (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhvnx16hi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhuvnx16hi_scalar                 (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhsuvnx16hi_scalar                (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhvnx32hi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhuvnx32hi_scalar                 (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhsuvnx32hi_scalar                (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhvnx1si_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhuvnx1si_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhsuvnx1si_scalar                 (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhvnx2si_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhuvnx2si_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhsuvnx2si_scalar                 (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhvnx4si_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhuvnx4si_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhsuvnx4si_scalar                 (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhvnx8si_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhuvnx8si_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhsuvnx8si_scalar                 (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhvnx16si_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhuvnx16si_scalar                 (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhsuvnx16si_scalar                (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_adcvnx1qi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_adcvnx2qi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_adcvnx4qi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_adcvnx8qi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_adcvnx16qi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_adcvnx32qi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_adcvnx64qi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_adcvnx1hi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_adcvnx2hi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_adcvnx4hi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_adcvnx8hi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_adcvnx16hi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_adcvnx32hi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_adcvnx1si                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_adcvnx2si                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_adcvnx4si                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_adcvnx8si                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_adcvnx16si                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_adcvnx1di                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_adcvnx2di                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_adcvnx4di                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_adcvnx8di                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sbcvnx1qi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sbcvnx2qi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sbcvnx4qi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sbcvnx8qi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sbcvnx16qi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sbcvnx32qi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sbcvnx64qi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sbcvnx1hi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sbcvnx2hi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sbcvnx4hi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sbcvnx8hi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sbcvnx16hi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sbcvnx32hi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sbcvnx1si                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sbcvnx2si                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sbcvnx4si                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sbcvnx8si                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sbcvnx16si                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sbcvnx1di                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sbcvnx2di                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sbcvnx4di                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sbcvnx8di                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_adcvnx1qi_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_adcvnx2qi_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_adcvnx4qi_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_adcvnx8qi_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_adcvnx16qi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_adcvnx32qi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_adcvnx64qi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_adcvnx1hi_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_adcvnx2hi_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_adcvnx4hi_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_adcvnx8hi_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_adcvnx16hi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_adcvnx32hi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_adcvnx1si_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_adcvnx2si_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_adcvnx4si_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_adcvnx8si_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_adcvnx16si_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sbcvnx1qi_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sbcvnx2qi_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sbcvnx4qi_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sbcvnx8qi_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sbcvnx16qi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sbcvnx32qi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sbcvnx64qi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sbcvnx1hi_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sbcvnx2hi_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sbcvnx4hi_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sbcvnx8hi_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sbcvnx16hi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sbcvnx32hi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sbcvnx1si_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sbcvnx2si_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sbcvnx4si_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sbcvnx8si_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sbcvnx16si_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_madcvnx1qi                          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_madcvnx2qi                          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_madcvnx4qi                          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_madcvnx8qi                          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_madcvnx16qi                         (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_madcvnx32qi                         (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_madcvnx64qi                         (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_madcvnx1hi                          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_madcvnx2hi                          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_madcvnx4hi                          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_madcvnx8hi                          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_madcvnx16hi                         (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_madcvnx32hi                         (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_madcvnx1si                          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_madcvnx2si                          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_madcvnx4si                          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_madcvnx8si                          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_madcvnx16si                         (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_madcvnx1di                          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_madcvnx2di                          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_madcvnx4di                          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_madcvnx8di                          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_msbcvnx1qi                          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_msbcvnx2qi                          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_msbcvnx4qi                          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_msbcvnx8qi                          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_msbcvnx16qi                         (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_msbcvnx32qi                         (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_msbcvnx64qi                         (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_msbcvnx1hi                          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_msbcvnx2hi                          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_msbcvnx4hi                          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_msbcvnx8hi                          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_msbcvnx16hi                         (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_msbcvnx32hi                         (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_msbcvnx1si                          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_msbcvnx2si                          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_msbcvnx4si                          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_msbcvnx8si                          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_msbcvnx16si                         (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_msbcvnx1di                          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_msbcvnx2di                          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_msbcvnx4di                          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_msbcvnx8di                          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_madcvnx1qi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_madcvnx2qi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_madcvnx4qi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_madcvnx8qi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_madcvnx16qi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_madcvnx32qi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_madcvnx64qi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_madcvnx1hi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_madcvnx2hi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_madcvnx4hi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_madcvnx8hi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_madcvnx16hi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_madcvnx32hi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_madcvnx1si_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_madcvnx2si_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_madcvnx4si_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_madcvnx8si_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_madcvnx16si_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_msbcvnx1qi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_msbcvnx2qi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_msbcvnx4qi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_msbcvnx8qi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_msbcvnx16qi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_msbcvnx32qi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_msbcvnx64qi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_msbcvnx1hi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_msbcvnx2hi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_msbcvnx4hi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_msbcvnx8hi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_msbcvnx16hi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_msbcvnx32hi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_msbcvnx1si_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_msbcvnx2si_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_msbcvnx4si_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_msbcvnx8si_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_msbcvnx16si_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_madcvnx1qi_overflow                 (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_madcvnx2qi_overflow                 (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_madcvnx4qi_overflow                 (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_madcvnx8qi_overflow                 (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_madcvnx16qi_overflow                (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_madcvnx32qi_overflow                (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_madcvnx64qi_overflow                (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_madcvnx1hi_overflow                 (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_madcvnx2hi_overflow                 (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_madcvnx4hi_overflow                 (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_madcvnx8hi_overflow                 (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_madcvnx16hi_overflow                (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_madcvnx32hi_overflow                (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_madcvnx1si_overflow                 (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_madcvnx2si_overflow                 (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_madcvnx4si_overflow                 (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_madcvnx8si_overflow                 (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_madcvnx16si_overflow                (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_madcvnx1di_overflow                 (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_madcvnx2di_overflow                 (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_madcvnx4di_overflow                 (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_madcvnx8di_overflow                 (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_msbcvnx1qi_overflow                 (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_msbcvnx2qi_overflow                 (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_msbcvnx4qi_overflow                 (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_msbcvnx8qi_overflow                 (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_msbcvnx16qi_overflow                (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_msbcvnx32qi_overflow                (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_msbcvnx64qi_overflow                (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_msbcvnx1hi_overflow                 (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_msbcvnx2hi_overflow                 (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_msbcvnx4hi_overflow                 (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_msbcvnx8hi_overflow                 (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_msbcvnx16hi_overflow                (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_msbcvnx32hi_overflow                (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_msbcvnx1si_overflow                 (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_msbcvnx2si_overflow                 (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_msbcvnx4si_overflow                 (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_msbcvnx8si_overflow                 (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_msbcvnx16si_overflow                (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_msbcvnx1di_overflow                 (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_msbcvnx2di_overflow                 (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_msbcvnx4di_overflow                 (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_msbcvnx8di_overflow                 (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_madcvnx1qi_overflow_scalar          (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_madcvnx2qi_overflow_scalar          (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_madcvnx4qi_overflow_scalar          (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_madcvnx8qi_overflow_scalar          (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_madcvnx16qi_overflow_scalar         (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_madcvnx32qi_overflow_scalar         (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_madcvnx64qi_overflow_scalar         (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_madcvnx1hi_overflow_scalar          (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_madcvnx2hi_overflow_scalar          (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_madcvnx4hi_overflow_scalar          (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_madcvnx8hi_overflow_scalar          (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_madcvnx16hi_overflow_scalar         (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_madcvnx32hi_overflow_scalar         (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_madcvnx1si_overflow_scalar          (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_madcvnx2si_overflow_scalar          (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_madcvnx4si_overflow_scalar          (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_madcvnx8si_overflow_scalar          (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_madcvnx16si_overflow_scalar         (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_msbcvnx1qi_overflow_scalar          (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_msbcvnx2qi_overflow_scalar          (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_msbcvnx4qi_overflow_scalar          (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_msbcvnx8qi_overflow_scalar          (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_msbcvnx16qi_overflow_scalar         (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_msbcvnx32qi_overflow_scalar         (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_msbcvnx64qi_overflow_scalar         (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_msbcvnx1hi_overflow_scalar          (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_msbcvnx2hi_overflow_scalar          (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_msbcvnx4hi_overflow_scalar          (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_msbcvnx8hi_overflow_scalar          (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_msbcvnx16hi_overflow_scalar         (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_msbcvnx32hi_overflow_scalar         (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_msbcvnx1si_overflow_scalar          (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_msbcvnx2si_overflow_scalar          (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_msbcvnx4si_overflow_scalar          (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_msbcvnx8si_overflow_scalar          (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_msbcvnx16si_overflow_scalar         (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_negvnx1qi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_one_cmplvnx1qi                      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_negvnx2qi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_one_cmplvnx2qi                      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_negvnx4qi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_one_cmplvnx4qi                      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_negvnx8qi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_one_cmplvnx8qi                      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_negvnx16qi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_one_cmplvnx16qi                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_negvnx32qi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_one_cmplvnx32qi                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_negvnx64qi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_one_cmplvnx64qi                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_negvnx1hi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_one_cmplvnx1hi                      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_negvnx2hi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_one_cmplvnx2hi                      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_negvnx4hi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_one_cmplvnx4hi                      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_negvnx8hi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_one_cmplvnx8hi                      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_negvnx16hi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_one_cmplvnx16hi                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_negvnx32hi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_one_cmplvnx32hi                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_negvnx1si                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_one_cmplvnx1si                      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_negvnx2si                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_one_cmplvnx2si                      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_negvnx4si                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_one_cmplvnx4si                      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_negvnx8si                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_one_cmplvnx8si                      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_negvnx16si                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_one_cmplvnx16si                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_negvnx1di                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_one_cmplvnx1di                      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_negvnx2di                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_one_cmplvnx2di                      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_negvnx4di                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_one_cmplvnx4di                      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_negvnx8di                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_one_cmplvnx8di                      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_extendvnx1hi_vf2                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_zero_extendvnx1hi_vf2               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_extendvnx2hi_vf2                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_zero_extendvnx2hi_vf2               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_extendvnx4hi_vf2                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_zero_extendvnx4hi_vf2               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_extendvnx8hi_vf2                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_zero_extendvnx8hi_vf2               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_extendvnx16hi_vf2                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_zero_extendvnx16hi_vf2              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_extendvnx32hi_vf2                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_zero_extendvnx32hi_vf2              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_extendvnx1si_vf2                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_zero_extendvnx1si_vf2               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_extendvnx2si_vf2                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_zero_extendvnx2si_vf2               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_extendvnx4si_vf2                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_zero_extendvnx4si_vf2               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_extendvnx8si_vf2                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_zero_extendvnx8si_vf2               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_extendvnx16si_vf2                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_zero_extendvnx16si_vf2              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_extendvnx1di_vf2                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_zero_extendvnx1di_vf2               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_extendvnx2di_vf2                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_zero_extendvnx2di_vf2               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_extendvnx4di_vf2                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_zero_extendvnx4di_vf2               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_extendvnx8di_vf2                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_zero_extendvnx8di_vf2               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_extendvnx1si_vf4                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_zero_extendvnx1si_vf4               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_extendvnx2si_vf4                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_zero_extendvnx2si_vf4               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_extendvnx4si_vf4                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_zero_extendvnx4si_vf4               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_extendvnx8si_vf4                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_zero_extendvnx8si_vf4               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_extendvnx16si_vf4                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_zero_extendvnx16si_vf4              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_extendvnx1di_vf4                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_zero_extendvnx1di_vf4               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_extendvnx2di_vf4                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_zero_extendvnx2di_vf4               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_extendvnx4di_vf4                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_zero_extendvnx4di_vf4               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_extendvnx8di_vf4                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_zero_extendvnx8di_vf4               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_extendvnx1di_vf8                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_zero_extendvnx1di_vf8               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_extendvnx2di_vf8                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_zero_extendvnx2di_vf8               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_extendvnx4di_vf8                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_zero_extendvnx4di_vf8               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_extendvnx8di_vf8                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_zero_extendvnx8di_vf8               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_addsvnx1hi               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_subsvnx1hi               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_mulsvnx1hi               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_adduvnx1hi               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_subuvnx1hi               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_muluvnx1hi               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_addsvnx2hi               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_subsvnx2hi               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_mulsvnx2hi               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_adduvnx2hi               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_subuvnx2hi               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_muluvnx2hi               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_addsvnx4hi               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_subsvnx4hi               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_mulsvnx4hi               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_adduvnx4hi               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_subuvnx4hi               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_muluvnx4hi               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_addsvnx8hi               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_subsvnx8hi               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_mulsvnx8hi               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_adduvnx8hi               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_subuvnx8hi               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_muluvnx8hi               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_addsvnx16hi              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_subsvnx16hi              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_mulsvnx16hi              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_adduvnx16hi              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_subuvnx16hi              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_muluvnx16hi              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_addsvnx32hi              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_subsvnx32hi              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_mulsvnx32hi              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_adduvnx32hi              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_subuvnx32hi              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_muluvnx32hi              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_addsvnx1si               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_subsvnx1si               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_mulsvnx1si               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_adduvnx1si               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_subuvnx1si               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_muluvnx1si               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_addsvnx2si               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_subsvnx2si               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_mulsvnx2si               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_adduvnx2si               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_subuvnx2si               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_muluvnx2si               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_addsvnx4si               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_subsvnx4si               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_mulsvnx4si               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_adduvnx4si               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_subuvnx4si               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_muluvnx4si               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_addsvnx8si               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_subsvnx8si               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_mulsvnx8si               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_adduvnx8si               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_subuvnx8si               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_muluvnx8si               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_addsvnx16si              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_subsvnx16si              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_mulsvnx16si              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_adduvnx16si              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_subuvnx16si              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_muluvnx16si              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_addsvnx1di               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_subsvnx1di               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_mulsvnx1di               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_adduvnx1di               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_subuvnx1di               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_muluvnx1di               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_addsvnx2di               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_subsvnx2di               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_mulsvnx2di               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_adduvnx2di               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_subuvnx2di               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_muluvnx2di               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_addsvnx4di               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_subsvnx4di               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_mulsvnx4di               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_adduvnx4di               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_subuvnx4di               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_muluvnx4di               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_addsvnx8di               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_subsvnx8di               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_mulsvnx8di               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_adduvnx8di               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_subuvnx8di               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_muluvnx8di               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_addsvnx1hi_scalar        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_subsvnx1hi_scalar        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_mulsvnx1hi_scalar        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_adduvnx1hi_scalar        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_subuvnx1hi_scalar        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_muluvnx1hi_scalar        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_addsvnx2hi_scalar        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_subsvnx2hi_scalar        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_mulsvnx2hi_scalar        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_adduvnx2hi_scalar        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_subuvnx2hi_scalar        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_muluvnx2hi_scalar        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_addsvnx4hi_scalar        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_subsvnx4hi_scalar        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_mulsvnx4hi_scalar        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_adduvnx4hi_scalar        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_subuvnx4hi_scalar        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_muluvnx4hi_scalar        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_addsvnx8hi_scalar        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_subsvnx8hi_scalar        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_mulsvnx8hi_scalar        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_adduvnx8hi_scalar        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_subuvnx8hi_scalar        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_muluvnx8hi_scalar        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_addsvnx16hi_scalar       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_subsvnx16hi_scalar       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_mulsvnx16hi_scalar       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_adduvnx16hi_scalar       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_subuvnx16hi_scalar       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_muluvnx16hi_scalar       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_addsvnx32hi_scalar       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_subsvnx32hi_scalar       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_mulsvnx32hi_scalar       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_adduvnx32hi_scalar       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_subuvnx32hi_scalar       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_muluvnx32hi_scalar       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_addsvnx1si_scalar        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_subsvnx1si_scalar        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_mulsvnx1si_scalar        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_adduvnx1si_scalar        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_subuvnx1si_scalar        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_muluvnx1si_scalar        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_addsvnx2si_scalar        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_subsvnx2si_scalar        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_mulsvnx2si_scalar        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_adduvnx2si_scalar        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_subuvnx2si_scalar        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_muluvnx2si_scalar        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_addsvnx4si_scalar        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_subsvnx4si_scalar        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_mulsvnx4si_scalar        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_adduvnx4si_scalar        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_subuvnx4si_scalar        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_muluvnx4si_scalar        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_addsvnx8si_scalar        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_subsvnx8si_scalar        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_mulsvnx8si_scalar        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_adduvnx8si_scalar        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_subuvnx8si_scalar        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_muluvnx8si_scalar        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_addsvnx16si_scalar       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_subsvnx16si_scalar       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_mulsvnx16si_scalar       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_adduvnx16si_scalar       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_subuvnx16si_scalar       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_muluvnx16si_scalar       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_addsvnx1di_scalar        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_subsvnx1di_scalar        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_mulsvnx1di_scalar        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_adduvnx1di_scalar        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_subuvnx1di_scalar        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_muluvnx1di_scalar        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_addsvnx2di_scalar        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_subsvnx2di_scalar        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_mulsvnx2di_scalar        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_adduvnx2di_scalar        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_subuvnx2di_scalar        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_muluvnx2di_scalar        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_addsvnx4di_scalar        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_subsvnx4di_scalar        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_mulsvnx4di_scalar        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_adduvnx4di_scalar        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_subuvnx4di_scalar        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_muluvnx4di_scalar        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_addsvnx8di_scalar        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_subsvnx8di_scalar        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_mulsvnx8di_scalar        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_adduvnx8di_scalar        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_subuvnx8di_scalar        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_muluvnx8di_scalar        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_addsvnx1hi             (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_subsvnx1hi             (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_adduvnx1hi             (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_subuvnx1hi             (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_addsvnx2hi             (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_subsvnx2hi             (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_adduvnx2hi             (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_subuvnx2hi             (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_addsvnx4hi             (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_subsvnx4hi             (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_adduvnx4hi             (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_subuvnx4hi             (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_addsvnx8hi             (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_subsvnx8hi             (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_adduvnx8hi             (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_subuvnx8hi             (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_addsvnx16hi            (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_subsvnx16hi            (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_adduvnx16hi            (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_subuvnx16hi            (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_addsvnx32hi            (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_subsvnx32hi            (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_adduvnx32hi            (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_subuvnx32hi            (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_addsvnx1si             (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_subsvnx1si             (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_adduvnx1si             (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_subuvnx1si             (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_addsvnx2si             (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_subsvnx2si             (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_adduvnx2si             (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_subuvnx2si             (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_addsvnx4si             (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_subsvnx4si             (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_adduvnx4si             (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_subuvnx4si             (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_addsvnx8si             (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_subsvnx8si             (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_adduvnx8si             (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_subuvnx8si             (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_addsvnx16si            (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_subsvnx16si            (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_adduvnx16si            (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_subuvnx16si            (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_addsvnx1di             (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_subsvnx1di             (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_adduvnx1di             (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_subuvnx1di             (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_addsvnx2di             (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_subsvnx2di             (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_adduvnx2di             (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_subuvnx2di             (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_addsvnx4di             (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_subsvnx4di             (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_adduvnx4di             (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_subuvnx4di             (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_addsvnx8di             (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_subsvnx8di             (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_adduvnx8di             (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_subuvnx8di             (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_addsvnx1hi_scalar      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_subsvnx1hi_scalar      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_adduvnx1hi_scalar      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_subuvnx1hi_scalar      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_addsvnx2hi_scalar      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_subsvnx2hi_scalar      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_adduvnx2hi_scalar      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_subuvnx2hi_scalar      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_addsvnx4hi_scalar      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_subsvnx4hi_scalar      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_adduvnx4hi_scalar      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_subuvnx4hi_scalar      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_addsvnx8hi_scalar      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_subsvnx8hi_scalar      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_adduvnx8hi_scalar      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_subuvnx8hi_scalar      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_addsvnx16hi_scalar     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_subsvnx16hi_scalar     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_adduvnx16hi_scalar     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_subuvnx16hi_scalar     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_addsvnx32hi_scalar     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_subsvnx32hi_scalar     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_adduvnx32hi_scalar     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_subuvnx32hi_scalar     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_addsvnx1si_scalar      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_subsvnx1si_scalar      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_adduvnx1si_scalar      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_subuvnx1si_scalar      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_addsvnx2si_scalar      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_subsvnx2si_scalar      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_adduvnx2si_scalar      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_subuvnx2si_scalar      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_addsvnx4si_scalar      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_subsvnx4si_scalar      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_adduvnx4si_scalar      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_subuvnx4si_scalar      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_addsvnx8si_scalar      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_subsvnx8si_scalar      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_adduvnx8si_scalar      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_subuvnx8si_scalar      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_addsvnx16si_scalar     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_subsvnx16si_scalar     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_adduvnx16si_scalar     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_subuvnx16si_scalar     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_addsvnx1di_scalar      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_subsvnx1di_scalar      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_adduvnx1di_scalar      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_subuvnx1di_scalar      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_addsvnx2di_scalar      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_subsvnx2di_scalar      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_adduvnx2di_scalar      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_subuvnx2di_scalar      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_addsvnx4di_scalar      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_subsvnx4di_scalar      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_adduvnx4di_scalar      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_subuvnx4di_scalar      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_addsvnx8di_scalar      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_subsvnx8di_scalar      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_adduvnx8di_scalar      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_subuvnx8di_scalar      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mulsuvnx1hi                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mulsuvnx2hi                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mulsuvnx4hi                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mulsuvnx8hi                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mulsuvnx16hi                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mulsuvnx32hi                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mulsuvnx1si                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mulsuvnx2si                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mulsuvnx4si                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mulsuvnx8si                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mulsuvnx16si                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mulsuvnx1di                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mulsuvnx2di                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mulsuvnx4di                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mulsuvnx8di                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mulsuvnx1hi_scalar            (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mulsuvnx2hi_scalar            (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mulsuvnx4hi_scalar            (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mulsuvnx8hi_scalar            (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mulsuvnx16hi_scalar           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mulsuvnx32hi_scalar           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mulsuvnx1si_scalar            (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mulsuvnx2si_scalar            (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mulsuvnx4si_scalar            (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mulsuvnx8si_scalar            (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mulsuvnx16si_scalar           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mulsuvnx1di_scalar            (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mulsuvnx2di_scalar            (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mulsuvnx4di_scalar            (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mulsuvnx8di_scalar            (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_extendvnx1hi                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_zero_extendvnx1hi                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_extendvnx2hi                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_zero_extendvnx2hi                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_extendvnx4hi                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_zero_extendvnx4hi                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_extendvnx8hi                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_zero_extendvnx8hi                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_extendvnx16hi                       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_zero_extendvnx16hi                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_extendvnx32hi                       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_zero_extendvnx32hi                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_extendvnx1si                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_zero_extendvnx1si                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_extendvnx2si                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_zero_extendvnx2si                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_extendvnx4si                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_zero_extendvnx4si                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_extendvnx8si                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_zero_extendvnx8si                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_extendvnx16si                       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_zero_extendvnx16si                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_extendvnx1di                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_zero_extendvnx1di                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_extendvnx2di                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_zero_extendvnx2di                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_extendvnx4di                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_zero_extendvnx4di                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_extendvnx8di                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_zero_extendvnx8di                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_ashrvnx1hi                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_lshrvnx1hi                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_ashrvnx2hi                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_lshrvnx2hi                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_ashrvnx4hi                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_lshrvnx4hi                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_ashrvnx8hi                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_lshrvnx8hi                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_ashrvnx16hi                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_lshrvnx16hi                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_ashrvnx32hi                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_lshrvnx32hi                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_ashrvnx1si                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_lshrvnx1si                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_ashrvnx2si                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_lshrvnx2si                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_ashrvnx4si                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_lshrvnx4si                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_ashrvnx8si                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_lshrvnx8si                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_ashrvnx16si                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_lshrvnx16si                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_ashrvnx1di                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_lshrvnx1di                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_ashrvnx2di                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_lshrvnx2di                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_ashrvnx4di                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_lshrvnx4di                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_ashrvnx8di                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_lshrvnx8di                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_ashrvnx1hi_scalar            (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_lshrvnx1hi_scalar            (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_ashrvnx2hi_scalar            (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_lshrvnx2hi_scalar            (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_ashrvnx4hi_scalar            (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_lshrvnx4hi_scalar            (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_ashrvnx8hi_scalar            (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_lshrvnx8hi_scalar            (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_ashrvnx16hi_scalar           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_lshrvnx16hi_scalar           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_ashrvnx32hi_scalar           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_lshrvnx32hi_scalar           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_ashrvnx1si_scalar            (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_lshrvnx1si_scalar            (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_ashrvnx2si_scalar            (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_lshrvnx2si_scalar            (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_ashrvnx4si_scalar            (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_lshrvnx4si_scalar            (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_ashrvnx8si_scalar            (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_lshrvnx8si_scalar            (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_ashrvnx16si_scalar           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_lshrvnx16si_scalar           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_ashrvnx1di_scalar            (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_lshrvnx1di_scalar            (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_ashrvnx2di_scalar            (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_lshrvnx2di_scalar            (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_ashrvnx4di_scalar            (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_lshrvnx4di_scalar            (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_ashrvnx8di_scalar            (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_lshrvnx8di_scalar            (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_truncvnx1hi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_truncvnx2hi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_truncvnx4hi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_truncvnx8hi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_truncvnx16hi                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_truncvnx32hi                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_truncvnx1si                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_truncvnx2si                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_truncvnx4si                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_truncvnx8si                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_truncvnx16si                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_truncvnx1di                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_truncvnx2di                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_truncvnx4di                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_truncvnx8di                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssaddvnx1qi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sssubvnx1qi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_usaddvnx1qi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ussubvnx1qi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssaddvnx2qi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sssubvnx2qi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_usaddvnx2qi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ussubvnx2qi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssaddvnx4qi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sssubvnx4qi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_usaddvnx4qi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ussubvnx4qi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssaddvnx8qi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sssubvnx8qi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_usaddvnx8qi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ussubvnx8qi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssaddvnx16qi                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sssubvnx16qi                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_usaddvnx16qi                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ussubvnx16qi                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssaddvnx32qi                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sssubvnx32qi                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_usaddvnx32qi                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ussubvnx32qi                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssaddvnx64qi                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sssubvnx64qi                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_usaddvnx64qi                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ussubvnx64qi                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssaddvnx1hi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sssubvnx1hi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_usaddvnx1hi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ussubvnx1hi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssaddvnx2hi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sssubvnx2hi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_usaddvnx2hi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ussubvnx2hi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssaddvnx4hi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sssubvnx4hi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_usaddvnx4hi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ussubvnx4hi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssaddvnx8hi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sssubvnx8hi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_usaddvnx8hi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ussubvnx8hi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssaddvnx16hi                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sssubvnx16hi                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_usaddvnx16hi                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ussubvnx16hi                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssaddvnx32hi                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sssubvnx32hi                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_usaddvnx32hi                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ussubvnx32hi                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssaddvnx1si                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sssubvnx1si                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_usaddvnx1si                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ussubvnx1si                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssaddvnx2si                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sssubvnx2si                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_usaddvnx2si                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ussubvnx2si                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssaddvnx4si                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sssubvnx4si                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_usaddvnx4si                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ussubvnx4si                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssaddvnx8si                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sssubvnx8si                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_usaddvnx8si                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ussubvnx8si                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssaddvnx16si                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sssubvnx16si                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_usaddvnx16si                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ussubvnx16si                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssaddvnx1di                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sssubvnx1di                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_usaddvnx1di                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ussubvnx1di                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssaddvnx2di                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sssubvnx2di                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_usaddvnx2di                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ussubvnx2di                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssaddvnx4di                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sssubvnx4di                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_usaddvnx4di                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ussubvnx4di                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssaddvnx8di                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sssubvnx8di                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_usaddvnx8di                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ussubvnx8di                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssaddvnx1qi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_usaddvnx1qi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssaddvnx2qi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_usaddvnx2qi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssaddvnx4qi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_usaddvnx4qi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssaddvnx8qi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_usaddvnx8qi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssaddvnx16qi_scalar                 (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_usaddvnx16qi_scalar                 (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssaddvnx32qi_scalar                 (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_usaddvnx32qi_scalar                 (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssaddvnx64qi_scalar                 (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_usaddvnx64qi_scalar                 (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssaddvnx1hi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_usaddvnx1hi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssaddvnx2hi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_usaddvnx2hi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssaddvnx4hi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_usaddvnx4hi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssaddvnx8hi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_usaddvnx8hi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssaddvnx16hi_scalar                 (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_usaddvnx16hi_scalar                 (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssaddvnx32hi_scalar                 (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_usaddvnx32hi_scalar                 (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssaddvnx1si_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_usaddvnx1si_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssaddvnx2si_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_usaddvnx2si_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssaddvnx4si_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_usaddvnx4si_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssaddvnx8si_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_usaddvnx8si_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssaddvnx16si_scalar                 (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_usaddvnx16si_scalar                 (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sssubvnx1qi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ussubvnx1qi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sssubvnx2qi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ussubvnx2qi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sssubvnx4qi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ussubvnx4qi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sssubvnx8qi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ussubvnx8qi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sssubvnx16qi_scalar                 (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ussubvnx16qi_scalar                 (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sssubvnx32qi_scalar                 (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ussubvnx32qi_scalar                 (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sssubvnx64qi_scalar                 (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ussubvnx64qi_scalar                 (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sssubvnx1hi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ussubvnx1hi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sssubvnx2hi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ussubvnx2hi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sssubvnx4hi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ussubvnx4hi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sssubvnx8hi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ussubvnx8hi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sssubvnx16hi_scalar                 (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ussubvnx16hi_scalar                 (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sssubvnx32hi_scalar                 (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ussubvnx32hi_scalar                 (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sssubvnx1si_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ussubvnx1si_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sssubvnx2si_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ussubvnx2si_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sssubvnx4si_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ussubvnx4si_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sssubvnx8si_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ussubvnx8si_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sssubvnx16si_scalar                 (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ussubvnx16si_scalar                 (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_aadduvnx1qi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_aaddvnx1qi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_asubuvnx1qi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_asubvnx1qi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_smulvnx1qi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssrlvnx1qi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssravnx1qi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_aadduvnx2qi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_aaddvnx2qi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_asubuvnx2qi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_asubvnx2qi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_smulvnx2qi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssrlvnx2qi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssravnx2qi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_aadduvnx4qi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_aaddvnx4qi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_asubuvnx4qi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_asubvnx4qi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_smulvnx4qi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssrlvnx4qi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssravnx4qi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_aadduvnx8qi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_aaddvnx8qi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_asubuvnx8qi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_asubvnx8qi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_smulvnx8qi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssrlvnx8qi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssravnx8qi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_aadduvnx16qi                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_aaddvnx16qi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_asubuvnx16qi                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_asubvnx16qi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_smulvnx16qi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssrlvnx16qi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssravnx16qi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_aadduvnx32qi                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_aaddvnx32qi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_asubuvnx32qi                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_asubvnx32qi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_smulvnx32qi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssrlvnx32qi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssravnx32qi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_aadduvnx64qi                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_aaddvnx64qi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_asubuvnx64qi                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_asubvnx64qi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_smulvnx64qi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssrlvnx64qi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssravnx64qi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_aadduvnx1hi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_aaddvnx1hi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_asubuvnx1hi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_asubvnx1hi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_smulvnx1hi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssrlvnx1hi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssravnx1hi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_aadduvnx2hi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_aaddvnx2hi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_asubuvnx2hi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_asubvnx2hi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_smulvnx2hi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssrlvnx2hi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssravnx2hi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_aadduvnx4hi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_aaddvnx4hi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_asubuvnx4hi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_asubvnx4hi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_smulvnx4hi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssrlvnx4hi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssravnx4hi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_aadduvnx8hi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_aaddvnx8hi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_asubuvnx8hi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_asubvnx8hi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_smulvnx8hi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssrlvnx8hi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssravnx8hi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_aadduvnx16hi                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_aaddvnx16hi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_asubuvnx16hi                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_asubvnx16hi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_smulvnx16hi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssrlvnx16hi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssravnx16hi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_aadduvnx32hi                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_aaddvnx32hi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_asubuvnx32hi                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_asubvnx32hi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_smulvnx32hi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssrlvnx32hi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssravnx32hi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_aadduvnx1si                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_aaddvnx1si                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_asubuvnx1si                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_asubvnx1si                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_smulvnx1si                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssrlvnx1si                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssravnx1si                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_aadduvnx2si                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_aaddvnx2si                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_asubuvnx2si                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_asubvnx2si                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_smulvnx2si                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssrlvnx2si                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssravnx2si                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_aadduvnx4si                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_aaddvnx4si                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_asubuvnx4si                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_asubvnx4si                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_smulvnx4si                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssrlvnx4si                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssravnx4si                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_aadduvnx8si                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_aaddvnx8si                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_asubuvnx8si                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_asubvnx8si                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_smulvnx8si                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssrlvnx8si                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssravnx8si                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_aadduvnx16si                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_aaddvnx16si                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_asubuvnx16si                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_asubvnx16si                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_smulvnx16si                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssrlvnx16si                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssravnx16si                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_aadduvnx1di                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_aaddvnx1di                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_asubuvnx1di                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_asubvnx1di                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_smulvnx1di                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssrlvnx1di                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssravnx1di                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_aadduvnx2di                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_aaddvnx2di                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_asubuvnx2di                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_asubvnx2di                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_smulvnx2di                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssrlvnx2di                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssravnx2di                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_aadduvnx4di                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_aaddvnx4di                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_asubuvnx4di                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_asubvnx4di                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_smulvnx4di                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssrlvnx4di                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssravnx4di                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_aadduvnx8di                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_aaddvnx8di                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_asubuvnx8di                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_asubvnx8di                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_smulvnx8di                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssrlvnx8di                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssravnx8di                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_aadduvnx1qi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_aaddvnx1qi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_asubuvnx1qi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_asubvnx1qi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_smulvnx1qi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_aadduvnx2qi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_aaddvnx2qi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_asubuvnx2qi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_asubvnx2qi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_smulvnx2qi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_aadduvnx4qi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_aaddvnx4qi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_asubuvnx4qi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_asubvnx4qi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_smulvnx4qi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_aadduvnx8qi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_aaddvnx8qi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_asubuvnx8qi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_asubvnx8qi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_smulvnx8qi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_aadduvnx16qi_scalar                 (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_aaddvnx16qi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_asubuvnx16qi_scalar                 (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_asubvnx16qi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_smulvnx16qi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_aadduvnx32qi_scalar                 (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_aaddvnx32qi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_asubuvnx32qi_scalar                 (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_asubvnx32qi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_smulvnx32qi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_aadduvnx64qi_scalar                 (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_aaddvnx64qi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_asubuvnx64qi_scalar                 (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_asubvnx64qi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_smulvnx64qi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_aadduvnx1hi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_aaddvnx1hi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_asubuvnx1hi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_asubvnx1hi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_smulvnx1hi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_aadduvnx2hi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_aaddvnx2hi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_asubuvnx2hi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_asubvnx2hi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_smulvnx2hi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_aadduvnx4hi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_aaddvnx4hi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_asubuvnx4hi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_asubvnx4hi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_smulvnx4hi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_aadduvnx8hi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_aaddvnx8hi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_asubuvnx8hi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_asubvnx8hi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_smulvnx8hi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_aadduvnx16hi_scalar                 (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_aaddvnx16hi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_asubuvnx16hi_scalar                 (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_asubvnx16hi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_smulvnx16hi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_aadduvnx32hi_scalar                 (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_aaddvnx32hi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_asubuvnx32hi_scalar                 (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_asubvnx32hi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_smulvnx32hi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_aadduvnx1si_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_aaddvnx1si_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_asubuvnx1si_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_asubvnx1si_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_smulvnx1si_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_aadduvnx2si_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_aaddvnx2si_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_asubuvnx2si_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_asubvnx2si_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_smulvnx2si_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_aadduvnx4si_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_aaddvnx4si_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_asubuvnx4si_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_asubvnx4si_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_smulvnx4si_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_aadduvnx8si_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_aaddvnx8si_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_asubuvnx8si_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_asubvnx8si_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_smulvnx8si_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_aadduvnx16si_scalar                 (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_aaddvnx16si_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_asubuvnx16si_scalar                 (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_asubvnx16si_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_smulvnx16si_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssrlvnx1qi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssravnx1qi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssrlvnx2qi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssravnx2qi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssrlvnx4qi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssravnx4qi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssrlvnx8qi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssravnx8qi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssrlvnx16qi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssravnx16qi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssrlvnx32qi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssravnx32qi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssrlvnx64qi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssravnx64qi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssrlvnx1hi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssravnx1hi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssrlvnx2hi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssravnx2hi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssrlvnx4hi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssravnx4hi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssrlvnx8hi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssravnx8hi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssrlvnx16hi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssravnx16hi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssrlvnx32hi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssravnx32hi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssrlvnx1si_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssravnx1si_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssrlvnx2si_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssravnx2si_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssrlvnx4si_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssravnx4si_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssrlvnx8si_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssravnx8si_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssrlvnx16si_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssravnx16si_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssrlvnx1di_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssravnx1di_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssrlvnx2di_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssravnx2di_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssrlvnx4di_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssravnx4di_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssrlvnx8di_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssravnx8di_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_clipvnx1hi                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_clipuvnx1hi                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_clipvnx2hi                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_clipuvnx2hi                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_clipvnx4hi                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_clipuvnx4hi                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_clipvnx8hi                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_clipuvnx8hi                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_clipvnx16hi                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_clipuvnx16hi                 (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_clipvnx32hi                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_clipuvnx32hi                 (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_clipvnx1si                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_clipuvnx1si                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_clipvnx2si                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_clipuvnx2si                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_clipvnx4si                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_clipuvnx4si                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_clipvnx8si                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_clipuvnx8si                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_clipvnx16si                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_clipuvnx16si                 (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_clipvnx1di                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_clipuvnx1di                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_clipvnx2di                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_clipuvnx2di                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_clipvnx4di                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_clipuvnx4di                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_clipvnx8di                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_clipuvnx8di                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_clipvnx1hi_scalar            (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_clipuvnx1hi_scalar           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_clipvnx2hi_scalar            (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_clipuvnx2hi_scalar           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_clipvnx4hi_scalar            (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_clipuvnx4hi_scalar           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_clipvnx8hi_scalar            (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_clipuvnx8hi_scalar           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_clipvnx16hi_scalar           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_clipuvnx16hi_scalar          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_clipvnx32hi_scalar           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_clipuvnx32hi_scalar          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_clipvnx1si_scalar            (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_clipuvnx1si_scalar           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_clipvnx2si_scalar            (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_clipuvnx2si_scalar           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_clipvnx4si_scalar            (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_clipuvnx4si_scalar           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_clipvnx8si_scalar            (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_clipuvnx8si_scalar           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_clipvnx16si_scalar           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_clipuvnx16si_scalar          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_clipvnx1di_scalar            (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_clipuvnx1di_scalar           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_clipvnx2di_scalar            (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_clipuvnx2di_scalar           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_clipvnx4di_scalar            (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_clipuvnx4di_scalar           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_clipvnx8di_scalar            (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_clipuvnx8di_scalar           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_plussvnx1hi               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_plusuvnx1hi               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_plussvnx2hi               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_plusuvnx2hi               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_plussvnx4hi               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_plusuvnx4hi               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_plussvnx8hi               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_plusuvnx8hi               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_plussvnx16hi              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_plusuvnx16hi              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_plussvnx32hi              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_plusuvnx32hi              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_plussvnx1si               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_plusuvnx1si               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_plussvnx2si               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_plusuvnx2si               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_plussvnx4si               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_plusuvnx4si               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_plussvnx8si               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_plusuvnx8si               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_plussvnx16si              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_plusuvnx16si              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_plussvnx1di               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_plusuvnx1di               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_plussvnx2di               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_plusuvnx2di               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_plussvnx4di               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_plusuvnx4di               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_plussvnx8di               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_plusuvnx8di               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_plussvnx1hi_scalar        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_plusuvnx1hi_scalar        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_plussvnx2hi_scalar        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_plusuvnx2hi_scalar        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_plussvnx4hi_scalar        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_plusuvnx4hi_scalar        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_plussvnx8hi_scalar        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_plusuvnx8hi_scalar        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_plussvnx16hi_scalar       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_plusuvnx16hi_scalar       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_plussvnx32hi_scalar       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_plusuvnx32hi_scalar       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_plussvnx1si_scalar        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_plusuvnx1si_scalar        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_plussvnx2si_scalar        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_plusuvnx2si_scalar        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_plussvnx4si_scalar        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_plusuvnx4si_scalar        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_plussvnx8si_scalar        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_plusuvnx8si_scalar        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_plussvnx16si_scalar       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_plusuvnx16si_scalar       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_plussvnx1di_scalar        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_plusuvnx1di_scalar        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_plussvnx2di_scalar        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_plusuvnx2di_scalar        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_plussvnx4di_scalar        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_plusuvnx4di_scalar        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_plussvnx8di_scalar        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_plusuvnx8di_scalar        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_plussuvnx1hi              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_plussuvnx2hi              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_plussuvnx4hi              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_plussuvnx8hi              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_plussuvnx16hi             (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_plussuvnx32hi             (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_plussuvnx1si              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_plussuvnx2si              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_plussuvnx4si              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_plussuvnx8si              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_plussuvnx16si             (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_plussuvnx1di              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_plussuvnx2di              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_plussuvnx4di              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_plussuvnx8di              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_plussuvnx1hi_scalar       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_plussuvnx2hi_scalar       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_plussuvnx4hi_scalar       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_plussuvnx8hi_scalar       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_plussuvnx16hi_scalar      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_plussuvnx32hi_scalar      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_plussuvnx1si_scalar       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_plussuvnx2si_scalar       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_plussuvnx4si_scalar       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_plussuvnx8si_scalar       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_plussuvnx16si_scalar      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_plussuvnx1di_scalar       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_plussuvnx2di_scalar       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_plussuvnx4di_scalar       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_plussuvnx8di_scalar       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_plususvnx1hi_scalar       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_plususvnx2hi_scalar       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_plususvnx4hi_scalar       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_plususvnx8hi_scalar       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_plususvnx16hi_scalar      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_plususvnx32hi_scalar      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_plususvnx1si_scalar       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_plususvnx2si_scalar       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_plususvnx4si_scalar       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_plususvnx8si_scalar       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_plususvnx16si_scalar      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_plususvnx1di_scalar       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_plususvnx2di_scalar       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_plususvnx4di_scalar       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_plususvnx8di_scalar       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_andvnx1bi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_iorvnx1bi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_xorvnx1bi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_andvnx2bi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_iorvnx2bi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_xorvnx2bi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_andvnx4bi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_iorvnx4bi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_xorvnx4bi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_andvnx8bi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_iorvnx8bi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_xorvnx8bi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_andvnx16bi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_iorvnx16bi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_xorvnx16bi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_andvnx32bi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_iorvnx32bi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_xorvnx32bi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_andvnx64bi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_iorvnx64bi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_xorvnx64bi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_nandvnx1bi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_niorvnx1bi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_nxorvnx1bi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_nandvnx2bi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_niorvnx2bi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_nxorvnx2bi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_nandvnx4bi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_niorvnx4bi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_nxorvnx4bi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_nandvnx8bi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_niorvnx8bi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_nxorvnx8bi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_nandvnx16bi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_niorvnx16bi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_nxorvnx16bi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_nandvnx32bi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_niorvnx32bi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_nxorvnx32bi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_nandvnx64bi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_niorvnx64bi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_nxorvnx64bi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_andnotvnx1bi                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_iornotvnx1bi                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_andnotvnx2bi                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_iornotvnx2bi                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_andnotvnx4bi                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_iornotvnx4bi                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_andnotvnx8bi                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_iornotvnx8bi                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_andnotvnx16bi                       (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_iornotvnx16bi                       (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_andnotvnx32bi                       (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_iornotvnx32bi                       (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_andnotvnx64bi                       (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_iornotvnx64bi                       (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_notvnx1bi                           (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_notvnx2bi                           (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_notvnx4bi                           (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_notvnx8bi                           (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_notvnx16bi                          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_notvnx32bi                          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_notvnx64bi                          (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_popcountvnx1bisi                    (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_popcountvnx2bisi                    (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_popcountvnx4bisi                    (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_popcountvnx8bisi                    (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_popcountvnx16bisi                   (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_popcountvnx32bisi                   (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_popcountvnx64bisi                   (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_popcountvnx1bidi                    (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_popcountvnx2bidi                    (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_popcountvnx4bidi                    (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_popcountvnx8bidi                    (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_popcountvnx16bidi                   (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_popcountvnx32bidi                   (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_popcountvnx64bidi                   (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ffsvnx1bisi                         (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ffsvnx2bisi                         (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ffsvnx4bisi                         (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ffsvnx8bisi                         (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ffsvnx16bisi                        (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ffsvnx32bisi                        (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ffsvnx64bisi                        (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ffsvnx1bidi                         (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ffsvnx2bidi                         (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ffsvnx4bidi                         (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ffsvnx8bidi                         (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ffsvnx16bidi                        (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ffsvnx32bidi                        (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ffsvnx64bidi                        (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sbfvnx1bi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sifvnx1bi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sofvnx1bi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sbfvnx2bi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sifvnx2bi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sofvnx2bi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sbfvnx4bi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sifvnx4bi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sofvnx4bi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sbfvnx8bi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sifvnx8bi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sofvnx8bi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sbfvnx16bi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sifvnx16bi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sofvnx16bi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sbfvnx32bi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sifvnx32bi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sofvnx32bi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sbfvnx64bi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sifvnx64bi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sofvnx64bi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_iotavnx1qi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_iotavnx2qi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_iotavnx4qi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_iotavnx8qi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_iotavnx16qi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_iotavnx32qi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_iotavnx64qi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_iotavnx1hi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_iotavnx2hi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_iotavnx4hi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_iotavnx8hi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_iotavnx16hi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_iotavnx32hi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_iotavnx1si                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_iotavnx2si                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_iotavnx4si                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_iotavnx8si                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_iotavnx16si                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_iotavnx1di                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_iotavnx2di                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_iotavnx4di                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_iotavnx8di                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_seriesvnx1qi                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_seriesvnx2qi                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_seriesvnx4qi                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_seriesvnx8qi                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_seriesvnx16qi                       (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_seriesvnx32qi                       (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_seriesvnx64qi                       (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_seriesvnx1hi                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_seriesvnx2hi                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_seriesvnx4hi                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_seriesvnx8hi                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_seriesvnx16hi                       (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_seriesvnx32hi                       (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_seriesvnx1si                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_seriesvnx2si                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_seriesvnx4si                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_seriesvnx8si                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_seriesvnx16si                       (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_seriesvnx1di                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_seriesvnx2di                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_seriesvnx4di                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_seriesvnx8di                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_addvnx1sf                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulvnx1sf                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_smaxvnx1sf                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sminvnx1sf                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_subvnx1sf                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_divvnx1sf                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_addvnx2sf                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulvnx2sf                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_smaxvnx2sf                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sminvnx2sf                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_subvnx2sf                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_divvnx2sf                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_addvnx4sf                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulvnx4sf                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_smaxvnx4sf                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sminvnx4sf                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_subvnx4sf                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_divvnx4sf                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_addvnx8sf                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulvnx8sf                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_smaxvnx8sf                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sminvnx8sf                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_subvnx8sf                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_divvnx8sf                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_addvnx16sf                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulvnx16sf                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_smaxvnx16sf                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sminvnx16sf                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_subvnx16sf                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_divvnx16sf                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_addvnx1df                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulvnx1df                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_smaxvnx1df                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sminvnx1df                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_subvnx1df                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_divvnx1df                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_addvnx2df                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulvnx2df                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_smaxvnx2df                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sminvnx2df                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_subvnx2df                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_divvnx2df                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_addvnx4df                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulvnx4df                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_smaxvnx4df                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sminvnx4df                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_subvnx4df                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_divvnx4df                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_addvnx8df                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulvnx8df                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_smaxvnx8df                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sminvnx8df                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_subvnx8df                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_divvnx8df                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_addvnx1sf_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulvnx1sf_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_smaxvnx1sf_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sminvnx1sf_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_addvnx2sf_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulvnx2sf_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_smaxvnx2sf_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sminvnx2sf_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_addvnx4sf_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulvnx4sf_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_smaxvnx4sf_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sminvnx4sf_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_addvnx8sf_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulvnx8sf_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_smaxvnx8sf_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sminvnx8sf_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_addvnx16sf_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulvnx16sf_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_smaxvnx16sf_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sminvnx16sf_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_addvnx1df_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulvnx1df_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_smaxvnx1df_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sminvnx1df_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_addvnx2df_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulvnx2df_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_smaxvnx2df_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sminvnx2df_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_addvnx4df_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulvnx4df_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_smaxvnx4df_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sminvnx4df_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_addvnx8df_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulvnx8df_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_smaxvnx8df_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sminvnx8df_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_subvnx1sf_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_divvnx1sf_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_subvnx2sf_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_divvnx2sf_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_subvnx4sf_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_divvnx4sf_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_subvnx8sf_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_divvnx8sf_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_subvnx16sf_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_divvnx16sf_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_subvnx1df_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_divvnx1df_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_subvnx2df_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_divvnx2df_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_subvnx4df_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_divvnx4df_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_subvnx8df_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_divvnx8df_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_subvnx1sf_reverse_scalar            (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_divvnx1sf_reverse_scalar            (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_subvnx2sf_reverse_scalar            (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_divvnx2sf_reverse_scalar            (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_subvnx4sf_reverse_scalar            (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_divvnx4sf_reverse_scalar            (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_subvnx8sf_reverse_scalar            (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_divvnx8sf_reverse_scalar            (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_subvnx16sf_reverse_scalar           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_divvnx16sf_reverse_scalar           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_subvnx1df_reverse_scalar            (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_divvnx1df_reverse_scalar            (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_subvnx2df_reverse_scalar            (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_divvnx2df_reverse_scalar            (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_subvnx4df_reverse_scalar            (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_divvnx4df_reverse_scalar            (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_subvnx8df_reverse_scalar            (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_divvnx8df_reverse_scalar            (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_copysignvnx1sf                      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ncopysignvnx1sf                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_xorsignvnx1sf                       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_copysignvnx2sf                      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ncopysignvnx2sf                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_xorsignvnx2sf                       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_copysignvnx4sf                      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ncopysignvnx4sf                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_xorsignvnx4sf                       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_copysignvnx8sf                      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ncopysignvnx8sf                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_xorsignvnx8sf                       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_copysignvnx16sf                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ncopysignvnx16sf                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_xorsignvnx16sf                      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_copysignvnx1df                      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ncopysignvnx1df                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_xorsignvnx1df                       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_copysignvnx2df                      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ncopysignvnx2df                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_xorsignvnx2df                       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_copysignvnx4df                      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ncopysignvnx4df                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_xorsignvnx4df                       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_copysignvnx8df                      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ncopysignvnx8df                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_xorsignvnx8df                       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_copysignvnx1sf_scalar               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ncopysignvnx1sf_scalar              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_xorsignvnx1sf_scalar                (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_copysignvnx2sf_scalar               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ncopysignvnx2sf_scalar              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_xorsignvnx2sf_scalar                (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_copysignvnx4sf_scalar               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ncopysignvnx4sf_scalar              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_xorsignvnx4sf_scalar                (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_copysignvnx8sf_scalar               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ncopysignvnx8sf_scalar              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_xorsignvnx8sf_scalar                (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_copysignvnx16sf_scalar              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ncopysignvnx16sf_scalar             (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_xorsignvnx16sf_scalar               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_copysignvnx1df_scalar               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ncopysignvnx1df_scalar              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_xorsignvnx1df_scalar                (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_copysignvnx2df_scalar               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ncopysignvnx2df_scalar              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_xorsignvnx2df_scalar                (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_copysignvnx4df_scalar               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ncopysignvnx4df_scalar              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_xorsignvnx4df_scalar                (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_copysignvnx8df_scalar               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ncopysignvnx8df_scalar              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_xorsignvnx8df_scalar                (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_negvnx1sf                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_absvnx1sf                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sqrtvnx1sf                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_negvnx2sf                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_absvnx2sf                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sqrtvnx2sf                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_negvnx4sf                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_absvnx4sf                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sqrtvnx4sf                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_negvnx8sf                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_absvnx8sf                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sqrtvnx8sf                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_negvnx16sf                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_absvnx16sf                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sqrtvnx16sf                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_negvnx1df                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_absvnx1df                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sqrtvnx1df                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_negvnx2df                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_absvnx2df                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sqrtvnx2df                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_negvnx4df                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_absvnx4df                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sqrtvnx4df                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_negvnx8df                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_absvnx8df                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sqrtvnx8df                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_rsqrt7vnx1sf                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_rec7vnx1sf                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_rsqrt7vnx2sf                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_rec7vnx2sf                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_rsqrt7vnx4sf                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_rec7vnx4sf                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_rsqrt7vnx8sf                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_rec7vnx8sf                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_rsqrt7vnx16sf                       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_rec7vnx16sf                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_rsqrt7vnx1df                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_rec7vnx1df                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_rsqrt7vnx2df                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_rec7vnx2df                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_rsqrt7vnx4df                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_rec7vnx4df                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_rsqrt7vnx8df                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_rec7vnx8df                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_classvnx1sf                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_classvnx2sf                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_classvnx4sf                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_classvnx8sf                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_classvnx16sf                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_classvnx1df                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_classvnx2df                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_classvnx4df                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_classvnx8df                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_addvnx1df                (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_subvnx1df                (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_mulvnx1df                (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_addvnx2df                (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_subvnx2df                (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_mulvnx2df                (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_addvnx4df                (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_subvnx4df                (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_mulvnx4df                (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_addvnx8df                (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_subvnx8df                (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_mulvnx8df                (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_addvnx1df_scalar         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_subvnx1df_scalar         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_mulvnx1df_scalar         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_addvnx2df_scalar         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_subvnx2df_scalar         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_mulvnx2df_scalar         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_addvnx4df_scalar         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_subvnx4df_scalar         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_mulvnx4df_scalar         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_addvnx8df_scalar         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_subvnx8df_scalar         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_dual_widen_mulvnx8df_scalar         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_addvnx1df              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_subvnx1df              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_addvnx2df              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_subvnx2df              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_addvnx4df              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_subvnx4df              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_addvnx8df              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_subvnx8df              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_addvnx1df_scalar       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_subvnx1df_scalar       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_addvnx2df_scalar       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_subvnx2df_scalar       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_addvnx4df_scalar       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_subvnx4df_scalar       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_addvnx8df_scalar       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_single_widen_subvnx8df_scalar       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_addvnx1df                 (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_subvnx1df                 (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_addvnx2df                 (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_subvnx2df                 (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_addvnx4df                 (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_subvnx4df                 (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_addvnx8df                 (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_subvnx8df                 (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_addvnx1df_scalar          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_subvnx1df_scalar          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_addvnx2df_scalar          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_subvnx2df_scalar          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_addvnx4df_scalar          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_subvnx4df_scalar          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_addvnx8df_scalar          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_subvnx8df_scalar          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_neg_addvnx1df             (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_neg_subvnx1df             (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_neg_addvnx2df             (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_neg_subvnx2df             (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_neg_addvnx4df             (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_neg_subvnx4df             (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_neg_addvnx8df             (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_neg_subvnx8df             (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_neg_addvnx1df_scalar      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_neg_subvnx1df_scalar      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_neg_addvnx2df_scalar      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_neg_subvnx2df_scalar      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_neg_addvnx4df_scalar      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_neg_subvnx4df_scalar      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_neg_addvnx8df_scalar      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_mul_neg_subvnx8df_scalar      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mergevnx1sf_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mergevnx2sf_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mergevnx4sf_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mergevnx8sf_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mergevnx16sf_scalar                 (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mergevnx1df_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mergevnx2df_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mergevnx4df_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mergevnx8df_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_fcvt_x_fvnx1sf                      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_fcvt_xu_fvnx1sf                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_fcvt_x_fvnx2sf                      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_fcvt_xu_fvnx2sf                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_fcvt_x_fvnx4sf                      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_fcvt_xu_fvnx4sf                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_fcvt_x_fvnx8sf                      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_fcvt_xu_fvnx8sf                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_fcvt_x_fvnx16sf                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_fcvt_xu_fvnx16sf                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_fcvt_x_fvnx1df                      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_fcvt_xu_fvnx1df                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_fcvt_x_fvnx2df                      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_fcvt_xu_fvnx2df                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_fcvt_x_fvnx4df                      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_fcvt_xu_fvnx4df                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_fcvt_x_fvnx8df                      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_fcvt_xu_fvnx8df                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_fix_truncvnx1sf                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_fixuns_truncvnx1sf                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_fix_truncvnx2sf                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_fixuns_truncvnx2sf                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_fix_truncvnx4sf                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_fixuns_truncvnx4sf                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_fix_truncvnx8sf                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_fixuns_truncvnx8sf                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_fix_truncvnx16sf                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_fixuns_truncvnx16sf                 (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_fix_truncvnx1df                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_fixuns_truncvnx1df                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_fix_truncvnx2df                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_fixuns_truncvnx2df                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_fix_truncvnx4df                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_fixuns_truncvnx4df                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_fix_truncvnx8df                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_fixuns_truncvnx8df                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_floatvnx1sf                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_floatunsvnx1sf                      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_floatvnx2sf                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_floatunsvnx2sf                      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_floatvnx4sf                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_floatunsvnx4sf                      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_floatvnx8sf                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_floatunsvnx8sf                      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_floatvnx16sf                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_floatunsvnx16sf                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_floatvnx1df                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_floatunsvnx1df                      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_floatvnx2df                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_floatunsvnx2df                      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_floatvnx4df                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_floatunsvnx4df                      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_floatvnx8df                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_floatunsvnx8df                      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_fcvt_x_fvnx1di                (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_fcvt_xu_fvnx1di               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_fcvt_x_fvnx2di                (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_fcvt_xu_fvnx2di               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_fcvt_x_fvnx4di                (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_fcvt_xu_fvnx4di               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_fcvt_x_fvnx8di                (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_fcvt_xu_fvnx8di               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_fix_truncvnx1di               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_fixuns_truncvnx1di            (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_fix_truncvnx2di               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_fixuns_truncvnx2di            (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_fix_truncvnx4di               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_fixuns_truncvnx4di            (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_fix_truncvnx8di               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_fixuns_truncvnx8di            (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_floatvnx1sf                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_floatunsvnx1sf                (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_floatvnx2sf                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_floatunsvnx2sf                (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_floatvnx4sf                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_floatunsvnx4sf                (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_floatvnx8sf                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_floatunsvnx8sf                (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_floatvnx16sf                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_floatunsvnx16sf               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_floatvnx1df                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_floatunsvnx1df                (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_floatvnx2df                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_floatunsvnx2df                (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_floatvnx4df                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_floatunsvnx4df                (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_floatvnx8df                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_floatunsvnx8df                (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_extendvnx1df                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_extendvnx2df                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_extendvnx4df                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_extendvnx8df                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_fcvt_x_fvnx1sf               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_fcvt_xu_fvnx1sf              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_fcvt_x_fvnx2sf               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_fcvt_xu_fvnx2sf              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_fcvt_x_fvnx4sf               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_fcvt_xu_fvnx4sf              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_fcvt_x_fvnx8sf               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_fcvt_xu_fvnx8sf              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_fcvt_x_fvnx16sf              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_fcvt_xu_fvnx16sf             (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_fcvt_x_fvnx1df               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_fcvt_xu_fvnx1df              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_fcvt_x_fvnx2df               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_fcvt_xu_fvnx2df              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_fcvt_x_fvnx4df               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_fcvt_xu_fvnx4df              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_fcvt_x_fvnx8df               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_fcvt_xu_fvnx8df              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_fix_truncvnx1sf              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_fixuns_truncvnx1sf           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_fix_truncvnx2sf              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_fixuns_truncvnx2sf           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_fix_truncvnx4sf              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_fixuns_truncvnx4sf           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_fix_truncvnx8sf              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_fixuns_truncvnx8sf           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_fix_truncvnx16sf             (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_fixuns_truncvnx16sf          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_fix_truncvnx1df              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_fixuns_truncvnx1df           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_fix_truncvnx2df              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_fixuns_truncvnx2df           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_fix_truncvnx4df              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_fixuns_truncvnx4df           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_fix_truncvnx8df              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_fixuns_truncvnx8df           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_floatvnx1di                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_floatunsvnx1di               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_floatvnx2di                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_floatunsvnx2di               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_floatvnx4di                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_floatunsvnx4di               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_floatvnx8di                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_narrow_floatunsvnx8di               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_truncvnx1df                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_truncvnx2df                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_truncvnx4df                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_truncvnx8df                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_rod_truncvnx1df                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_rod_truncvnx2df                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_rod_truncvnx4df                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_rod_truncvnx8df                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_sumvnx1qivnx8qi               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_maxuvnx1qivnx8qi              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_maxvnx1qivnx8qi               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_minuvnx1qivnx8qi              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_minvnx1qivnx8qi               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_andvnx1qivnx8qi               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_orvnx1qivnx8qi                (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_xorvnx1qivnx8qi               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_sumvnx2qivnx8qi               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_maxuvnx2qivnx8qi              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_maxvnx2qivnx8qi               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_minuvnx2qivnx8qi              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_minvnx2qivnx8qi               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_andvnx2qivnx8qi               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_orvnx2qivnx8qi                (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_xorvnx2qivnx8qi               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_sumvnx4qivnx8qi               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_maxuvnx4qivnx8qi              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_maxvnx4qivnx8qi               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_minuvnx4qivnx8qi              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_minvnx4qivnx8qi               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_andvnx4qivnx8qi               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_orvnx4qivnx8qi                (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_xorvnx4qivnx8qi               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_sumvnx8qivnx8qi               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_maxuvnx8qivnx8qi              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_maxvnx8qivnx8qi               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_minuvnx8qivnx8qi              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_minvnx8qivnx8qi               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_andvnx8qivnx8qi               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_orvnx8qivnx8qi                (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_xorvnx8qivnx8qi               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_sumvnx16qivnx8qi              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_maxuvnx16qivnx8qi             (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_maxvnx16qivnx8qi              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_minuvnx16qivnx8qi             (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_minvnx16qivnx8qi              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_andvnx16qivnx8qi              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_orvnx16qivnx8qi               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_xorvnx16qivnx8qi              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_sumvnx32qivnx8qi              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_maxuvnx32qivnx8qi             (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_maxvnx32qivnx8qi              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_minuvnx32qivnx8qi             (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_minvnx32qivnx8qi              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_andvnx32qivnx8qi              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_orvnx32qivnx8qi               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_xorvnx32qivnx8qi              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_sumvnx64qivnx8qi              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_maxuvnx64qivnx8qi             (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_maxvnx64qivnx8qi              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_minuvnx64qivnx8qi             (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_minvnx64qivnx8qi              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_andvnx64qivnx8qi              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_orvnx64qivnx8qi               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_xorvnx64qivnx8qi              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_sumvnx1hivnx4hi               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_maxuvnx1hivnx4hi              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_maxvnx1hivnx4hi               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_minuvnx1hivnx4hi              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_minvnx1hivnx4hi               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_andvnx1hivnx4hi               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_orvnx1hivnx4hi                (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_xorvnx1hivnx4hi               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_sumvnx2hivnx4hi               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_maxuvnx2hivnx4hi              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_maxvnx2hivnx4hi               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_minuvnx2hivnx4hi              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_minvnx2hivnx4hi               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_andvnx2hivnx4hi               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_orvnx2hivnx4hi                (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_xorvnx2hivnx4hi               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_sumvnx4hivnx4hi               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_maxuvnx4hivnx4hi              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_maxvnx4hivnx4hi               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_minuvnx4hivnx4hi              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_minvnx4hivnx4hi               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_andvnx4hivnx4hi               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_orvnx4hivnx4hi                (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_xorvnx4hivnx4hi               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_sumvnx8hivnx4hi               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_maxuvnx8hivnx4hi              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_maxvnx8hivnx4hi               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_minuvnx8hivnx4hi              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_minvnx8hivnx4hi               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_andvnx8hivnx4hi               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_orvnx8hivnx4hi                (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_xorvnx8hivnx4hi               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_sumvnx16hivnx4hi              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_maxuvnx16hivnx4hi             (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_maxvnx16hivnx4hi              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_minuvnx16hivnx4hi             (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_minvnx16hivnx4hi              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_andvnx16hivnx4hi              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_orvnx16hivnx4hi               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_xorvnx16hivnx4hi              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_sumvnx32hivnx4hi              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_maxuvnx32hivnx4hi             (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_maxvnx32hivnx4hi              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_minuvnx32hivnx4hi             (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_minvnx32hivnx4hi              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_andvnx32hivnx4hi              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_orvnx32hivnx4hi               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_xorvnx32hivnx4hi              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_sumvnx1sivnx2si               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_maxuvnx1sivnx2si              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_maxvnx1sivnx2si               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_minuvnx1sivnx2si              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_minvnx1sivnx2si               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_andvnx1sivnx2si               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_orvnx1sivnx2si                (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_xorvnx1sivnx2si               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_sumvnx2sivnx2si               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_maxuvnx2sivnx2si              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_maxvnx2sivnx2si               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_minuvnx2sivnx2si              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_minvnx2sivnx2si               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_andvnx2sivnx2si               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_orvnx2sivnx2si                (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_xorvnx2sivnx2si               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_sumvnx4sivnx2si               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_maxuvnx4sivnx2si              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_maxvnx4sivnx2si               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_minuvnx4sivnx2si              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_minvnx4sivnx2si               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_andvnx4sivnx2si               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_orvnx4sivnx2si                (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_xorvnx4sivnx2si               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_sumvnx8sivnx2si               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_maxuvnx8sivnx2si              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_maxvnx8sivnx2si               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_minuvnx8sivnx2si              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_minvnx8sivnx2si               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_andvnx8sivnx2si               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_orvnx8sivnx2si                (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_xorvnx8sivnx2si               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_sumvnx16sivnx2si              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_maxuvnx16sivnx2si             (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_maxvnx16sivnx2si              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_minuvnx16sivnx2si             (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_minvnx16sivnx2si              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_andvnx16sivnx2si              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_orvnx16sivnx2si               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_xorvnx16sivnx2si              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_sumvnx1divnx1DI               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_maxuvnx1divnx1DI              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_maxvnx1divnx1DI               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_minuvnx1divnx1DI              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_minvnx1divnx1DI               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_andvnx1divnx1DI               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_orvnx1divnx1DI                (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_xorvnx1divnx1DI               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_sumvnx2divnx1DI               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_maxuvnx2divnx1DI              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_maxvnx2divnx1DI               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_minuvnx2divnx1DI              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_minvnx2divnx1DI               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_andvnx2divnx1DI               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_orvnx2divnx1DI                (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_xorvnx2divnx1DI               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_sumvnx4divnx1DI               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_maxuvnx4divnx1DI              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_maxvnx4divnx1DI               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_minuvnx4divnx1DI              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_minvnx4divnx1DI               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_andvnx4divnx1DI               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_orvnx4divnx1DI                (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_xorvnx4divnx1DI               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_sumvnx8divnx1DI               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_maxuvnx8divnx1DI              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_maxvnx8divnx1DI               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_minuvnx8divnx1DI              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_minvnx8divnx1DI               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_andvnx8divnx1DI               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_orvnx8divnx1DI                (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_xorvnx8divnx1DI               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_sumvnx1qivnx4qi               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_maxuvnx1qivnx4qi              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_maxvnx1qivnx4qi               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_minuvnx1qivnx4qi              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_minvnx1qivnx4qi               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_andvnx1qivnx4qi               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_orvnx1qivnx4qi                (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_xorvnx1qivnx4qi               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_sumvnx2qivnx4qi               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_maxuvnx2qivnx4qi              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_maxvnx2qivnx4qi               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_minuvnx2qivnx4qi              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_minvnx2qivnx4qi               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_andvnx2qivnx4qi               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_orvnx2qivnx4qi                (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_xorvnx2qivnx4qi               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_sumvnx4qivnx4qi               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_maxuvnx4qivnx4qi              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_maxvnx4qivnx4qi               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_minuvnx4qivnx4qi              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_minvnx4qivnx4qi               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_andvnx4qivnx4qi               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_orvnx4qivnx4qi                (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_xorvnx4qivnx4qi               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_sumvnx8qivnx4qi               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_maxuvnx8qivnx4qi              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_maxvnx8qivnx4qi               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_minuvnx8qivnx4qi              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_minvnx8qivnx4qi               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_andvnx8qivnx4qi               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_orvnx8qivnx4qi                (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_xorvnx8qivnx4qi               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_sumvnx16qivnx4qi              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_maxuvnx16qivnx4qi             (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_maxvnx16qivnx4qi              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_minuvnx16qivnx4qi             (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_minvnx16qivnx4qi              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_andvnx16qivnx4qi              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_orvnx16qivnx4qi               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_xorvnx16qivnx4qi              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_sumvnx32qivnx4qi              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_maxuvnx32qivnx4qi             (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_maxvnx32qivnx4qi              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_minuvnx32qivnx4qi             (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_minvnx32qivnx4qi              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_andvnx32qivnx4qi              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_orvnx32qivnx4qi               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_xorvnx32qivnx4qi              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_sumvnx1hivnx2hi               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_maxuvnx1hivnx2hi              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_maxvnx1hivnx2hi               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_minuvnx1hivnx2hi              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_minvnx1hivnx2hi               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_andvnx1hivnx2hi               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_orvnx1hivnx2hi                (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_xorvnx1hivnx2hi               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_sumvnx2hivnx2hi               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_maxuvnx2hivnx2hi              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_maxvnx2hivnx2hi               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_minuvnx2hivnx2hi              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_minvnx2hivnx2hi               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_andvnx2hivnx2hi               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_orvnx2hivnx2hi                (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_xorvnx2hivnx2hi               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_sumvnx4hivnx2hi               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_maxuvnx4hivnx2hi              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_maxvnx4hivnx2hi               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_minuvnx4hivnx2hi              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_minvnx4hivnx2hi               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_andvnx4hivnx2hi               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_orvnx4hivnx2hi                (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_xorvnx4hivnx2hi               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_sumvnx8hivnx2hi               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_maxuvnx8hivnx2hi              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_maxvnx8hivnx2hi               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_minuvnx8hivnx2hi              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_minvnx8hivnx2hi               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_andvnx8hivnx2hi               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_orvnx8hivnx2hi                (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_xorvnx8hivnx2hi               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_sumvnx16hivnx2hi              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_maxuvnx16hivnx2hi             (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_maxvnx16hivnx2hi              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_minuvnx16hivnx2hi             (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_minvnx16hivnx2hi              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_andvnx16hivnx2hi              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_orvnx16hivnx2hi               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_xorvnx16hivnx2hi              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_sumvnx1sivnx1si               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_maxuvnx1sivnx1si              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_maxvnx1sivnx1si               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_minuvnx1sivnx1si              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_minvnx1sivnx1si               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_andvnx1sivnx1si               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_orvnx1sivnx1si                (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_xorvnx1sivnx1si               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_sumvnx2sivnx1si               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_maxuvnx2sivnx1si              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_maxvnx2sivnx1si               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_minuvnx2sivnx1si              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_minvnx2sivnx1si               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_andvnx2sivnx1si               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_orvnx2sivnx1si                (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_xorvnx2sivnx1si               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_sumvnx4sivnx1si               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_maxuvnx4sivnx1si              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_maxvnx4sivnx1si               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_minuvnx4sivnx1si              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_minvnx4sivnx1si               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_andvnx4sivnx1si               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_orvnx4sivnx1si                (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_xorvnx4sivnx1si               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_sumvnx8sivnx1si               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_maxuvnx8sivnx1si              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_maxvnx8sivnx1si               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_minuvnx8sivnx1si              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_minvnx8sivnx1si               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_andvnx8sivnx1si               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_orvnx8sivnx1si                (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_xorvnx8sivnx1si               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_reduc_plusvnx1qivnx4hi        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_reduc_plusuvnx1qivnx4hi       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_reduc_plusvnx2qivnx4hi        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_reduc_plusuvnx2qivnx4hi       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_reduc_plusvnx4qivnx4hi        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_reduc_plusuvnx4qivnx4hi       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_reduc_plusvnx8qivnx4hi        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_reduc_plusuvnx8qivnx4hi       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_reduc_plusvnx16qivnx4hi       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_reduc_plusuvnx16qivnx4hi      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_reduc_plusvnx32qivnx4hi       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_reduc_plusuvnx32qivnx4hi      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_reduc_plusvnx64qivnx4hi       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_reduc_plusuvnx64qivnx4hi      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_reduc_plusvnx1hivnx2si        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_reduc_plusuvnx1hivnx2si       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_reduc_plusvnx2hivnx2si        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_reduc_plusuvnx2hivnx2si       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_reduc_plusvnx4hivnx2si        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_reduc_plusuvnx4hivnx2si       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_reduc_plusvnx8hivnx2si        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_reduc_plusuvnx8hivnx2si       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_reduc_plusvnx16hivnx2si       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_reduc_plusuvnx16hivnx2si      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_reduc_plusvnx32hivnx2si       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_reduc_plusuvnx32hivnx2si      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_reduc_plusvnx1sivnx2di        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_reduc_plusuvnx1sivnx2di       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_reduc_plusvnx2sivnx2di        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_reduc_plusuvnx2sivnx2di       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_reduc_plusvnx4sivnx2di        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_reduc_plusuvnx4sivnx2di       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_reduc_plusvnx8sivnx2di        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_reduc_plusuvnx8sivnx2di       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_reduc_plusvnx16sivnx2di       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_reduc_plusuvnx16sivnx2di      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_reduc_plusvnx1qivnx2hi        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_reduc_plusuvnx1qivnx2hi       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_reduc_plusvnx2qivnx2hi        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_reduc_plusuvnx2qivnx2hi       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_reduc_plusvnx4qivnx2hi        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_reduc_plusuvnx4qivnx2hi       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_reduc_plusvnx8qivnx2hi        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_reduc_plusuvnx8qivnx2hi       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_reduc_plusvnx16qivnx2hi       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_reduc_plusuvnx16qivnx2hi      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_reduc_plusvnx32qivnx2hi       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_reduc_plusuvnx32qivnx2hi      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_reduc_plusvnx1hivnx1si        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_reduc_plusuvnx1hivnx1si       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_reduc_plusvnx2hivnx1si        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_reduc_plusuvnx2hivnx1si       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_reduc_plusvnx4hivnx1si        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_reduc_plusuvnx4hivnx1si       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_reduc_plusvnx8hivnx1si        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_reduc_plusuvnx8hivnx1si       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_reduc_plusvnx16hivnx1si       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_reduc_plusuvnx16hivnx1si      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_maxvnx1sfvnx2sf               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_minvnx1sfvnx2sf               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_maxvnx2sfvnx2sf               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_minvnx2sfvnx2sf               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_maxvnx4sfvnx2sf               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_minvnx4sfvnx2sf               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_maxvnx8sfvnx2sf               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_minvnx8sfvnx2sf               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_maxvnx16sfvnx2sf              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_minvnx16sfvnx2sf              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_maxvnx1dfvnx1df               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_minvnx1dfvnx1df               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_maxvnx2dfvnx1df               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_minvnx2dfvnx1df               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_maxvnx4dfvnx1df               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_minvnx4dfvnx1df               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_maxvnx8dfvnx1df               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_minvnx8dfvnx1df               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_maxvnx1sfvnx1sf               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_minvnx1sfvnx1sf               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_maxvnx2sfvnx1sf               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_minvnx2sfvnx1sf               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_maxvnx4sfvnx1sf               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_minvnx4sfvnx1sf               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_maxvnx8sfvnx1sf               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_minvnx8sfvnx1sf               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_plusovnx1sfvnx2sf             (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_plusuvnx1sfvnx2sf             (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_plusovnx2sfvnx2sf             (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_plusuvnx2sfvnx2sf             (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_plusovnx4sfvnx2sf             (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_plusuvnx4sfvnx2sf             (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_plusovnx8sfvnx2sf             (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_plusuvnx8sfvnx2sf             (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_plusovnx16sfvnx2sf            (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_plusuvnx16sfvnx2sf            (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_plusovnx1dfvnx1df             (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_plusuvnx1dfvnx1df             (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_plusovnx2dfvnx1df             (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_plusuvnx2dfvnx1df             (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_plusovnx4dfvnx1df             (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_plusuvnx4dfvnx1df             (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_plusovnx8dfvnx1df             (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_plusuvnx8dfvnx1df             (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_plusovnx1sfvnx1sf             (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_plusuvnx1sfvnx1sf             (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_plusovnx2sfvnx1sf             (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_plusuvnx2sfvnx1sf             (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_plusovnx4sfvnx1sf             (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_plusuvnx4sfvnx1sf             (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_plusovnx8sfvnx1sf             (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_reduc_plusuvnx8sfvnx1sf             (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_reduc_plusovnx1sfvnx1df       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_reduc_plusuvnx1sfvnx1df       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_reduc_plusovnx2sfvnx1df       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_reduc_plusuvnx2sfvnx1df       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_reduc_plusovnx4sfvnx1df       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_reduc_plusuvnx4sfvnx1df       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_reduc_plusovnx8sfvnx1df       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_reduc_plusuvnx8sfvnx1df       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_reduc_plusovnx16sfvnx1df      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_widen_reduc_plusuvnx16sfvnx1df      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_extract_first_truncvnx1di           (rtx, rtx);
extern rtx        gen_pred_extract_first_truncvnx2di           (rtx, rtx);
extern rtx        gen_pred_extract_first_truncvnx4di           (rtx, rtx);
extern rtx        gen_pred_extract_first_truncvnx8di           (rtx, rtx);
extern rtx        gen_pred_slideupvnx1qi                       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_slidedownvnx1qi                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_slideupvnx2qi                       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_slidedownvnx2qi                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_slideupvnx4qi                       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_slidedownvnx4qi                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_slideupvnx8qi                       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_slidedownvnx8qi                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_slideupvnx16qi                      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_slidedownvnx16qi                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_slideupvnx32qi                      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_slidedownvnx32qi                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_slideupvnx64qi                      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_slidedownvnx64qi                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_slideupvnx1hi                       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_slidedownvnx1hi                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_slideupvnx2hi                       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_slidedownvnx2hi                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_slideupvnx4hi                       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_slidedownvnx4hi                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_slideupvnx8hi                       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_slidedownvnx8hi                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_slideupvnx16hi                      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_slidedownvnx16hi                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_slideupvnx32hi                      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_slidedownvnx32hi                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_slideupvnx1si                       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_slidedownvnx1si                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_slideupvnx2si                       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_slidedownvnx2si                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_slideupvnx4si                       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_slidedownvnx4si                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_slideupvnx8si                       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_slidedownvnx8si                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_slideupvnx16si                      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_slidedownvnx16si                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_slideupvnx1di                       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_slidedownvnx1di                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_slideupvnx2di                       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_slidedownvnx2di                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_slideupvnx4di                       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_slidedownvnx4di                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_slideupvnx8di                       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_slidedownvnx8di                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_slideupvnx1sf                       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_slidedownvnx1sf                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_slideupvnx2sf                       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_slidedownvnx2sf                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_slideupvnx4sf                       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_slidedownvnx4sf                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_slideupvnx8sf                       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_slidedownvnx8sf                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_slideupvnx16sf                      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_slidedownvnx16sf                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_slideupvnx1df                       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_slidedownvnx1df                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_slideupvnx2df                       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_slidedownvnx2df                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_slideupvnx4df                       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_slidedownvnx4df                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_slideupvnx8df                       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_slidedownvnx8df                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_slide1upvnx1qi                      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_slide1downvnx1qi                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_slide1upvnx2qi                      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_slide1downvnx2qi                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_slide1upvnx4qi                      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_slide1downvnx4qi                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_slide1upvnx8qi                      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_slide1downvnx8qi                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_slide1upvnx16qi                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_slide1downvnx16qi                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_slide1upvnx32qi                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_slide1downvnx32qi                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_slide1upvnx64qi                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_slide1downvnx64qi                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_slide1upvnx1hi                      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_slide1downvnx1hi                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_slide1upvnx2hi                      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_slide1downvnx2hi                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_slide1upvnx4hi                      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_slide1downvnx4hi                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_slide1upvnx8hi                      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_slide1downvnx8hi                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_slide1upvnx16hi                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_slide1downvnx16hi                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_slide1upvnx32hi                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_slide1downvnx32hi                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_slide1upvnx1si                      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_slide1downvnx1si                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_slide1upvnx2si                      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_slide1downvnx2si                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_slide1upvnx4si                      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_slide1downvnx4si                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_slide1upvnx8si                      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_slide1downvnx8si                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_slide1upvnx16si                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_slide1downvnx16si                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_slide1upvnx1sf                      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_slide1downvnx1sf                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_slide1upvnx2sf                      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_slide1downvnx2sf                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_slide1upvnx4sf                      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_slide1downvnx4sf                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_slide1upvnx8sf                      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_slide1downvnx8sf                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_slide1upvnx16sf                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_slide1downvnx16sf                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_slide1upvnx1df                      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_slide1downvnx1df                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_slide1upvnx2df                      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_slide1downvnx2df                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_slide1upvnx4df                      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_slide1downvnx4df                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_slide1upvnx8df                      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_slide1downvnx8df                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_gathervnx1qi                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_gathervnx2qi                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_gathervnx4qi                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_gathervnx8qi                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_gathervnx16qi                       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_gathervnx32qi                       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_gathervnx64qi                       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_gathervnx1hi                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_gathervnx2hi                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_gathervnx4hi                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_gathervnx8hi                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_gathervnx16hi                       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_gathervnx32hi                       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_gathervnx1si                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_gathervnx2si                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_gathervnx4si                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_gathervnx8si                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_gathervnx16si                       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_gathervnx1di                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_gathervnx2di                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_gathervnx4di                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_gathervnx8di                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_gathervnx1sf                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_gathervnx2sf                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_gathervnx4sf                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_gathervnx8sf                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_gathervnx16sf                       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_gathervnx1df                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_gathervnx2df                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_gathervnx4df                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_gathervnx8df                        (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_gathervnx1qi_scalar                 (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_gathervnx2qi_scalar                 (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_gathervnx4qi_scalar                 (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_gathervnx8qi_scalar                 (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_gathervnx16qi_scalar                (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_gathervnx32qi_scalar                (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_gathervnx64qi_scalar                (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_gathervnx1hi_scalar                 (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_gathervnx2hi_scalar                 (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_gathervnx4hi_scalar                 (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_gathervnx8hi_scalar                 (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_gathervnx16hi_scalar                (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_gathervnx32hi_scalar                (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_gathervnx1si_scalar                 (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_gathervnx2si_scalar                 (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_gathervnx4si_scalar                 (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_gathervnx8si_scalar                 (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_gathervnx16si_scalar                (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_gathervnx1di_scalar                 (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_gathervnx2di_scalar                 (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_gathervnx4di_scalar                 (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_gathervnx8di_scalar                 (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_gathervnx1sf_scalar                 (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_gathervnx2sf_scalar                 (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_gathervnx4sf_scalar                 (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_gathervnx8sf_scalar                 (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_gathervnx16sf_scalar                (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_gathervnx1df_scalar                 (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_gathervnx2df_scalar                 (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_gathervnx4df_scalar                 (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_gathervnx8df_scalar                 (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_gatherei16vnx1qi                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_gatherei16vnx2qi                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_gatherei16vnx4qi                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_gatherei16vnx8qi                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_gatherei16vnx16qi                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_gatherei16vnx32qi                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_gatherei16vnx1hi                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_gatherei16vnx2hi                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_gatherei16vnx4hi                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_gatherei16vnx8hi                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_gatherei16vnx16hi                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_gatherei16vnx32hi                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_gatherei16vnx1si                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_gatherei16vnx2si                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_gatherei16vnx4si                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_gatherei16vnx8si                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_gatherei16vnx16si                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_gatherei16vnx1di                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_gatherei16vnx2di                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_gatherei16vnx4di                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_gatherei16vnx8di                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_gatherei16vnx1sf                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_gatherei16vnx2sf                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_gatherei16vnx4sf                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_gatherei16vnx8sf                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_gatherei16vnx16sf                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_gatherei16vnx1df                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_gatherei16vnx2df                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_gatherei16vnx4df                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_gatherei16vnx8df                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_compressvnx1qi                      (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_compressvnx2qi                      (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_compressvnx4qi                      (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_compressvnx8qi                      (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_compressvnx16qi                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_compressvnx32qi                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_compressvnx64qi                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_compressvnx1hi                      (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_compressvnx2hi                      (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_compressvnx4hi                      (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_compressvnx8hi                      (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_compressvnx16hi                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_compressvnx32hi                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_compressvnx1si                      (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_compressvnx2si                      (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_compressvnx4si                      (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_compressvnx8si                      (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_compressvnx16si                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_compressvnx1di                      (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_compressvnx2di                      (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_compressvnx4di                      (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_compressvnx8di                      (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_compressvnx1sf                      (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_compressvnx2sf                      (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_compressvnx4sf                      (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_compressvnx8sf                      (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_compressvnx16sf                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_compressvnx1df                      (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_compressvnx2df                      (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_compressvnx4df                      (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_compressvnx8df                      (rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_read_vlsi                                (rtx);
extern rtx        gen_read_vldi_zero_extend                    (rtx);
extern rtx        gen_pred_fault_loadvnx1qi                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_fault_loadvnx2qi                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_fault_loadvnx4qi                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_fault_loadvnx8qi                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_fault_loadvnx16qi                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_fault_loadvnx32qi                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_fault_loadvnx64qi                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_fault_loadvnx1hi                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_fault_loadvnx2hi                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_fault_loadvnx4hi                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_fault_loadvnx8hi                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_fault_loadvnx16hi                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_fault_loadvnx32hi                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_fault_loadvnx1si                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_fault_loadvnx2si                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_fault_loadvnx4si                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_fault_loadvnx8si                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_fault_loadvnx16si                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_fault_loadvnx1di                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_fault_loadvnx2di                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_fault_loadvnx4di                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_fault_loadvnx8di                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_fault_loadvnx1sf                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_fault_loadvnx2sf                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_fault_loadvnx4sf                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_fault_loadvnx8sf                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_fault_loadvnx16sf                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_fault_loadvnx1df                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_fault_loadvnx2df                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_fault_loadvnx4df                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_fault_loadvnx8df                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_addvsi4                                  (rtx, rtx, rtx, rtx);
extern rtx        gen_addvdi4                                  (rtx, rtx, rtx, rtx);
extern rtx        gen_uaddvsi4                                 (rtx, rtx, rtx, rtx);
extern rtx        gen_uaddvdi4                                 (rtx, rtx, rtx, rtx);
extern rtx        gen_subvsi4                                  (rtx, rtx, rtx, rtx);
extern rtx        gen_subvdi4                                  (rtx, rtx, rtx, rtx);
extern rtx        gen_usubvsi4                                 (rtx, rtx, rtx, rtx);
extern rtx        gen_usubvdi4                                 (rtx, rtx, rtx, rtx);
extern rtx        gen_mulvsi4                                  (rtx, rtx, rtx, rtx);
extern rtx        gen_mulvdi4                                  (rtx, rtx, rtx, rtx);
extern rtx        gen_umulvsi4                                 (rtx, rtx, rtx, rtx);
extern rtx        gen_umulvdi4                                 (rtx, rtx, rtx, rtx);
extern rtx        gen_mulditi3                                 (rtx, rtx, rtx);
extern rtx        gen_umulditi3                                (rtx, rtx, rtx);
extern rtx        gen_usmulditi3                               (rtx, rtx, rtx);
extern rtx        gen_mulsidi3                                 (rtx, rtx, rtx);
extern rtx        gen_umulsidi3                                (rtx, rtx, rtx);
extern rtx        gen_usmulsidi3                               (rtx, rtx, rtx);
extern rtx        gen_zero_extendsidi2                         (rtx, rtx);
extern rtx        gen_zero_extendhisi2                         (rtx, rtx);
extern rtx        gen_zero_extendhidi2                         (rtx, rtx);
extern rtx        gen_extendqihi2                              (rtx, rtx);
extern rtx        gen_extendqisi2                              (rtx, rtx);
extern rtx        gen_extendqidi2                              (rtx, rtx);
extern rtx        gen_extendhihi2                              (rtx, rtx);
extern rtx        gen_extendhisi2                              (rtx, rtx);
extern rtx        gen_extendhidi2                              (rtx, rtx);
extern rtx        gen_movhf                                    (rtx, rtx);
extern rtx        gen_movdi                                    (rtx, rtx);
extern rtx        gen_movsi                                    (rtx, rtx);
extern rtx        gen_movhi                                    (rtx, rtx);
extern rtx        gen_movqi                                    (rtx, rtx);
extern rtx        gen_movsf                                    (rtx, rtx);
extern rtx        gen_movdf                                    (rtx, rtx);
extern rtx        gen_cpymemsi                                 (rtx, rtx, rtx, rtx);
extern rtx        gen_clear_cache                              (rtx, rtx);
extern rtx        gen_movsicc                                  (rtx, rtx, rtx, rtx);
extern rtx        gen_movdicc                                  (rtx, rtx, rtx, rtx);
extern rtx        gen_condjump                                 (rtx, rtx);
extern rtx        gen_cbranchqi4                               (rtx, rtx, rtx, rtx);
extern rtx        gen_cbranchsi4                               (rtx, rtx, rtx, rtx);
extern rtx        gen_cbranchdi4                               (rtx, rtx, rtx, rtx);
extern rtx        gen_cbranchsf4                               (rtx, rtx, rtx, rtx);
extern rtx        gen_cbranchdf4                               (rtx, rtx, rtx, rtx);
extern rtx        gen_cbranchhf4                               (rtx, rtx, rtx, rtx);
extern rtx        gen_cstoresi4                                (rtx, rtx, rtx, rtx);
extern rtx        gen_cstoredi4                                (rtx, rtx, rtx, rtx);
extern rtx        gen_cstoresf4                                (rtx, rtx, rtx, rtx);
extern rtx        gen_cstoredf4                                (rtx, rtx, rtx, rtx);
extern rtx        gen_cstorehf4                                (rtx, rtx, rtx, rtx);
extern rtx        gen_flt_quietsfsi4                           (rtx, rtx, rtx);
extern rtx        gen_fle_quietsfsi4                           (rtx, rtx, rtx);
extern rtx        gen_flt_quietsfdi4                           (rtx, rtx, rtx);
extern rtx        gen_fle_quietsfdi4                           (rtx, rtx, rtx);
extern rtx        gen_flt_quietdfsi4                           (rtx, rtx, rtx);
extern rtx        gen_fle_quietdfsi4                           (rtx, rtx, rtx);
extern rtx        gen_flt_quietdfdi4                           (rtx, rtx, rtx);
extern rtx        gen_fle_quietdfdi4                           (rtx, rtx, rtx);
extern rtx        gen_flt_quiethfsi4                           (rtx, rtx, rtx);
extern rtx        gen_fle_quiethfsi4                           (rtx, rtx, rtx);
extern rtx        gen_flt_quiethfdi4                           (rtx, rtx, rtx);
extern rtx        gen_fle_quiethfdi4                           (rtx, rtx, rtx);
extern rtx        gen_indirect_jump                            (rtx);
extern rtx        gen_tablejump                                (rtx, rtx);
extern rtx        gen_prologue                                 (void);
extern rtx        gen_epilogue                                 (void);
extern rtx        gen_sibcall_epilogue                         (void);
extern rtx        gen_return                                   (void);
extern rtx        gen_eh_return                                (rtx);
extern rtx        gen_sibcall                                  (rtx, rtx, rtx, rtx);
extern rtx        gen_sibcall_value                            (rtx, rtx, rtx, rtx);
extern rtx        gen_call                                     (rtx, rtx, rtx, rtx);
extern rtx        gen_call_value                               (rtx, rtx, rtx, rtx);
extern rtx        gen_untyped_call                             (rtx, rtx, rtx);
extern rtx        gen_restore_stack_nonlocal                   (rtx, rtx);
extern rtx        gen_get_thread_pointersi                     (rtx);
extern rtx        gen_get_thread_pointerdi                     (rtx);
extern rtx        gen_stack_protect_set                        (rtx, rtx);
extern rtx        gen_stack_protect_test                       (rtx, rtx, rtx);
extern rtx        gen_extvsi                                   (rtx, rtx, rtx, rtx);
extern rtx        gen_extvdi                                   (rtx, rtx, rtx, rtx);
extern rtx        gen_extzvsi                                  (rtx, rtx, rtx, rtx);
extern rtx        gen_extzvdi                                  (rtx, rtx, rtx, rtx);
extern rtx        gen_maddhisi4                                (rtx, rtx, rtx, rtx);
extern rtx        gen_msubhisi4                                (rtx, rtx, rtx, rtx);
extern rtx        gen_clzdi2                                   (rtx, rtx);
extern rtx        gen_clzsi2                                   (rtx, rtx);
extern rtx        gen_ctzsi2                                   (rtx, rtx);
extern rtx        gen_ctzdi2                                   (rtx, rtx);
extern rtx        gen_popcountsi2                              (rtx, rtx);
extern rtx        gen_popcountdi2                              (rtx, rtx);
extern rtx        gen_rotrsi3                                  (rtx, rtx, rtx);
extern rtx        gen_rotrdi3                                  (rtx, rtx, rtx);
extern rtx        gen_bswapdi2                                 (rtx, rtx);
extern rtx        gen_bswapsi2                                 (rtx, rtx);
extern rtx        gen_bswaphi2                                 (rtx, rtx);
extern rtx        gen_mem_thread_fence                         (rtx);
extern rtx        gen_atomic_compare_and_swapsi                (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_atomic_compare_and_swapdi                (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_atomic_test_and_set                      (rtx, rtx, rtx);
extern rtx        gen_vreinterpretvnx1qi                       (rtx, rtx);
extern rtx        gen_vreinterpretvnx2qi                       (rtx, rtx);
extern rtx        gen_vreinterpretvnx4qi                       (rtx, rtx);
extern rtx        gen_vreinterpretvnx8qi                       (rtx, rtx);
extern rtx        gen_vreinterpretvnx16qi                      (rtx, rtx);
extern rtx        gen_vreinterpretvnx32qi                      (rtx, rtx);
extern rtx        gen_vreinterpretvnx64qi                      (rtx, rtx);
extern rtx        gen_vreinterpretvnx1hi                       (rtx, rtx);
extern rtx        gen_vreinterpretvnx2hi                       (rtx, rtx);
extern rtx        gen_vreinterpretvnx4hi                       (rtx, rtx);
extern rtx        gen_vreinterpretvnx8hi                       (rtx, rtx);
extern rtx        gen_vreinterpretvnx16hi                      (rtx, rtx);
extern rtx        gen_vreinterpretvnx32hi                      (rtx, rtx);
extern rtx        gen_vreinterpretvnx1si                       (rtx, rtx);
extern rtx        gen_vreinterpretvnx2si                       (rtx, rtx);
extern rtx        gen_vreinterpretvnx4si                       (rtx, rtx);
extern rtx        gen_vreinterpretvnx8si                       (rtx, rtx);
extern rtx        gen_vreinterpretvnx16si                      (rtx, rtx);
extern rtx        gen_vreinterpretvnx1di                       (rtx, rtx);
extern rtx        gen_vreinterpretvnx2di                       (rtx, rtx);
extern rtx        gen_vreinterpretvnx4di                       (rtx, rtx);
extern rtx        gen_vreinterpretvnx8di                       (rtx, rtx);
extern rtx        gen_vreinterpretvnx1sf                       (rtx, rtx);
extern rtx        gen_vreinterpretvnx2sf                       (rtx, rtx);
extern rtx        gen_vreinterpretvnx4sf                       (rtx, rtx);
extern rtx        gen_vreinterpretvnx8sf                       (rtx, rtx);
extern rtx        gen_vreinterpretvnx16sf                      (rtx, rtx);
extern rtx        gen_vreinterpretvnx1df                       (rtx, rtx);
extern rtx        gen_vreinterpretvnx2df                       (rtx, rtx);
extern rtx        gen_vreinterpretvnx4df                       (rtx, rtx);
extern rtx        gen_vreinterpretvnx8df                       (rtx, rtx);
extern rtx        gen_vlmul_extx2vnx1qi                        (rtx, rtx);
extern rtx        gen_vlmul_extx2vnx2qi                        (rtx, rtx);
extern rtx        gen_vlmul_extx2vnx4qi                        (rtx, rtx);
extern rtx        gen_vlmul_extx2vnx8qi                        (rtx, rtx);
extern rtx        gen_vlmul_extx2vnx16qi                       (rtx, rtx);
extern rtx        gen_vlmul_extx2vnx32qi                       (rtx, rtx);
extern rtx        gen_vlmul_extx2vnx1hi                        (rtx, rtx);
extern rtx        gen_vlmul_extx2vnx2hi                        (rtx, rtx);
extern rtx        gen_vlmul_extx2vnx4hi                        (rtx, rtx);
extern rtx        gen_vlmul_extx2vnx8hi                        (rtx, rtx);
extern rtx        gen_vlmul_extx2vnx16hi                       (rtx, rtx);
extern rtx        gen_vlmul_extx2vnx1si                        (rtx, rtx);
extern rtx        gen_vlmul_extx2vnx2si                        (rtx, rtx);
extern rtx        gen_vlmul_extx2vnx4si                        (rtx, rtx);
extern rtx        gen_vlmul_extx2vnx8si                        (rtx, rtx);
extern rtx        gen_vlmul_extx2vnx1di                        (rtx, rtx);
extern rtx        gen_vlmul_extx2vnx2di                        (rtx, rtx);
extern rtx        gen_vlmul_extx2vnx4di                        (rtx, rtx);
extern rtx        gen_vlmul_extx2vnx1sf                        (rtx, rtx);
extern rtx        gen_vlmul_extx2vnx2sf                        (rtx, rtx);
extern rtx        gen_vlmul_extx2vnx4sf                        (rtx, rtx);
extern rtx        gen_vlmul_extx2vnx8sf                        (rtx, rtx);
extern rtx        gen_vlmul_extx2vnx1df                        (rtx, rtx);
extern rtx        gen_vlmul_extx2vnx2df                        (rtx, rtx);
extern rtx        gen_vlmul_extx2vnx4df                        (rtx, rtx);
extern rtx        gen_vlmul_extx4vnx1qi                        (rtx, rtx);
extern rtx        gen_vlmul_extx4vnx2qi                        (rtx, rtx);
extern rtx        gen_vlmul_extx4vnx4qi                        (rtx, rtx);
extern rtx        gen_vlmul_extx4vnx8qi                        (rtx, rtx);
extern rtx        gen_vlmul_extx4vnx16qi                       (rtx, rtx);
extern rtx        gen_vlmul_extx4vnx1hi                        (rtx, rtx);
extern rtx        gen_vlmul_extx4vnx2hi                        (rtx, rtx);
extern rtx        gen_vlmul_extx4vnx4hi                        (rtx, rtx);
extern rtx        gen_vlmul_extx4vnx8hi                        (rtx, rtx);
extern rtx        gen_vlmul_extx4vnx1si                        (rtx, rtx);
extern rtx        gen_vlmul_extx4vnx2si                        (rtx, rtx);
extern rtx        gen_vlmul_extx4vnx4si                        (rtx, rtx);
extern rtx        gen_vlmul_extx4vnx1di                        (rtx, rtx);
extern rtx        gen_vlmul_extx4vnx2di                        (rtx, rtx);
extern rtx        gen_vlmul_extx4vnx1sf                        (rtx, rtx);
extern rtx        gen_vlmul_extx4vnx2sf                        (rtx, rtx);
extern rtx        gen_vlmul_extx4vnx4sf                        (rtx, rtx);
extern rtx        gen_vlmul_extx4vnx1df                        (rtx, rtx);
extern rtx        gen_vlmul_extx4vnx2df                        (rtx, rtx);
extern rtx        gen_vlmul_extx8vnx1qi                        (rtx, rtx);
extern rtx        gen_vlmul_extx8vnx2qi                        (rtx, rtx);
extern rtx        gen_vlmul_extx8vnx4qi                        (rtx, rtx);
extern rtx        gen_vlmul_extx8vnx8qi                        (rtx, rtx);
extern rtx        gen_vlmul_extx8vnx1hi                        (rtx, rtx);
extern rtx        gen_vlmul_extx8vnx2hi                        (rtx, rtx);
extern rtx        gen_vlmul_extx8vnx4hi                        (rtx, rtx);
extern rtx        gen_vlmul_extx8vnx1si                        (rtx, rtx);
extern rtx        gen_vlmul_extx8vnx2si                        (rtx, rtx);
extern rtx        gen_vlmul_extx8vnx1di                        (rtx, rtx);
extern rtx        gen_vlmul_extx8vnx1sf                        (rtx, rtx);
extern rtx        gen_vlmul_extx8vnx2sf                        (rtx, rtx);
extern rtx        gen_vlmul_extx8vnx1df                        (rtx, rtx);
extern rtx        gen_vlmul_extx16vnx1qi                       (rtx, rtx);
extern rtx        gen_vlmul_extx16vnx2qi                       (rtx, rtx);
extern rtx        gen_vlmul_extx16vnx4qi                       (rtx, rtx);
extern rtx        gen_vlmul_extx16vnx1hi                       (rtx, rtx);
extern rtx        gen_vlmul_extx16vnx2hi                       (rtx, rtx);
extern rtx        gen_vlmul_extx16vnx1si                       (rtx, rtx);
extern rtx        gen_vlmul_extx16vnx1sf                       (rtx, rtx);
extern rtx        gen_vlmul_extx32vnx1qi                       (rtx, rtx);
extern rtx        gen_vlmul_extx32vnx2qi                       (rtx, rtx);
extern rtx        gen_vlmul_extx32vnx1hi                       (rtx, rtx);
extern rtx        gen_vlmul_extx64vnx1qi                       (rtx, rtx);
extern rtx        gen_movvnx1qi                                (rtx, rtx);
extern rtx        gen_movvnx2qi                                (rtx, rtx);
extern rtx        gen_movvnx4qi                                (rtx, rtx);
extern rtx        gen_movvnx8qi                                (rtx, rtx);
extern rtx        gen_movvnx16qi                               (rtx, rtx);
extern rtx        gen_movvnx32qi                               (rtx, rtx);
extern rtx        gen_movvnx64qi                               (rtx, rtx);
extern rtx        gen_movvnx1hi                                (rtx, rtx);
extern rtx        gen_movvnx2hi                                (rtx, rtx);
extern rtx        gen_movvnx4hi                                (rtx, rtx);
extern rtx        gen_movvnx8hi                                (rtx, rtx);
extern rtx        gen_movvnx16hi                               (rtx, rtx);
extern rtx        gen_movvnx32hi                               (rtx, rtx);
extern rtx        gen_movvnx1si                                (rtx, rtx);
extern rtx        gen_movvnx2si                                (rtx, rtx);
extern rtx        gen_movvnx4si                                (rtx, rtx);
extern rtx        gen_movvnx8si                                (rtx, rtx);
extern rtx        gen_movvnx16si                               (rtx, rtx);
extern rtx        gen_movvnx1di                                (rtx, rtx);
extern rtx        gen_movvnx2di                                (rtx, rtx);
extern rtx        gen_movvnx4di                                (rtx, rtx);
extern rtx        gen_movvnx8di                                (rtx, rtx);
extern rtx        gen_movvnx1sf                                (rtx, rtx);
extern rtx        gen_movvnx2sf                                (rtx, rtx);
extern rtx        gen_movvnx4sf                                (rtx, rtx);
extern rtx        gen_movvnx8sf                                (rtx, rtx);
extern rtx        gen_movvnx16sf                               (rtx, rtx);
extern rtx        gen_movvnx1df                                (rtx, rtx);
extern rtx        gen_movvnx2df                                (rtx, rtx);
extern rtx        gen_movvnx4df                                (rtx, rtx);
extern rtx        gen_movvnx8df                                (rtx, rtx);
extern rtx        gen_movvnx1bi                                (rtx, rtx);
extern rtx        gen_movvnx2bi                                (rtx, rtx);
extern rtx        gen_movvnx4bi                                (rtx, rtx);
extern rtx        gen_movvnx8bi                                (rtx, rtx);
extern rtx        gen_movvnx16bi                               (rtx, rtx);
extern rtx        gen_movvnx32bi                               (rtx, rtx);
extern rtx        gen_movvnx64bi                               (rtx, rtx);
extern rtx        gen_movvnx1qisi_lra                          (rtx, rtx);
extern rtx        gen_movvnx1qidi_lra                          (rtx, rtx);
extern rtx        gen_movvnx2qisi_lra                          (rtx, rtx);
extern rtx        gen_movvnx2qidi_lra                          (rtx, rtx);
extern rtx        gen_movvnx4qisi_lra                          (rtx, rtx);
extern rtx        gen_movvnx4qidi_lra                          (rtx, rtx);
extern rtx        gen_movvnx1hisi_lra                          (rtx, rtx);
extern rtx        gen_movvnx1hidi_lra                          (rtx, rtx);
extern rtx        gen_movvnx2hisi_lra                          (rtx, rtx);
extern rtx        gen_movvnx2hidi_lra                          (rtx, rtx);
extern rtx        gen_movvnx1sisi_lra                          (rtx, rtx);
extern rtx        gen_movvnx1sidi_lra                          (rtx, rtx);
extern rtx        gen_movvnx1sfsi_lra                          (rtx, rtx);
extern rtx        gen_movvnx1sfdi_lra                          (rtx, rtx);
extern rtx        gen_movvnx1bisi_lra                          (rtx, rtx);
extern rtx        gen_movvnx2bisi_lra                          (rtx, rtx);
extern rtx        gen_movvnx4bisi_lra                          (rtx, rtx);
extern rtx        gen_movvnx8bisi_lra                          (rtx, rtx);
extern rtx        gen_movvnx16bisi_lra                         (rtx, rtx);
extern rtx        gen_movvnx32bisi_lra                         (rtx, rtx);
extern rtx        gen_movvnx64bisi_lra                         (rtx, rtx);
extern rtx        gen_movvnx1bidi_lra                          (rtx, rtx);
extern rtx        gen_movvnx2bidi_lra                          (rtx, rtx);
extern rtx        gen_movvnx4bidi_lra                          (rtx, rtx);
extern rtx        gen_movvnx8bidi_lra                          (rtx, rtx);
extern rtx        gen_movvnx16bidi_lra                         (rtx, rtx);
extern rtx        gen_movvnx32bidi_lra                         (rtx, rtx);
extern rtx        gen_movvnx64bidi_lra                         (rtx, rtx);
extern rtx        gen_vec_duplicatevnx1qi                      (rtx, rtx);
extern rtx        gen_vec_duplicatevnx2qi                      (rtx, rtx);
extern rtx        gen_vec_duplicatevnx4qi                      (rtx, rtx);
extern rtx        gen_vec_duplicatevnx8qi                      (rtx, rtx);
extern rtx        gen_vec_duplicatevnx16qi                     (rtx, rtx);
extern rtx        gen_vec_duplicatevnx32qi                     (rtx, rtx);
extern rtx        gen_vec_duplicatevnx64qi                     (rtx, rtx);
extern rtx        gen_vec_duplicatevnx1hi                      (rtx, rtx);
extern rtx        gen_vec_duplicatevnx2hi                      (rtx, rtx);
extern rtx        gen_vec_duplicatevnx4hi                      (rtx, rtx);
extern rtx        gen_vec_duplicatevnx8hi                      (rtx, rtx);
extern rtx        gen_vec_duplicatevnx16hi                     (rtx, rtx);
extern rtx        gen_vec_duplicatevnx32hi                     (rtx, rtx);
extern rtx        gen_vec_duplicatevnx1si                      (rtx, rtx);
extern rtx        gen_vec_duplicatevnx2si                      (rtx, rtx);
extern rtx        gen_vec_duplicatevnx4si                      (rtx, rtx);
extern rtx        gen_vec_duplicatevnx8si                      (rtx, rtx);
extern rtx        gen_vec_duplicatevnx16si                     (rtx, rtx);
extern rtx        gen_vec_duplicatevnx1di                      (rtx, rtx);
extern rtx        gen_vec_duplicatevnx2di                      (rtx, rtx);
extern rtx        gen_vec_duplicatevnx4di                      (rtx, rtx);
extern rtx        gen_vec_duplicatevnx8di                      (rtx, rtx);
extern rtx        gen_vec_duplicatevnx1sf                      (rtx, rtx);
extern rtx        gen_vec_duplicatevnx2sf                      (rtx, rtx);
extern rtx        gen_vec_duplicatevnx4sf                      (rtx, rtx);
extern rtx        gen_vec_duplicatevnx8sf                      (rtx, rtx);
extern rtx        gen_vec_duplicatevnx16sf                     (rtx, rtx);
extern rtx        gen_vec_duplicatevnx1df                      (rtx, rtx);
extern rtx        gen_vec_duplicatevnx2df                      (rtx, rtx);
extern rtx        gen_vec_duplicatevnx4df                      (rtx, rtx);
extern rtx        gen_vec_duplicatevnx8df                      (rtx, rtx);
extern rtx        gen_pred_mergevnx1di_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mergevnx2di_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mergevnx4di_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mergevnx8di_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_broadcastvnx1qi                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_broadcastvnx2qi                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_broadcastvnx4qi                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_broadcastvnx8qi                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_broadcastvnx16qi                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_broadcastvnx32qi                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_broadcastvnx64qi                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_broadcastvnx1hi                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_broadcastvnx2hi                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_broadcastvnx4hi                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_broadcastvnx8hi                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_broadcastvnx16hi                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_broadcastvnx32hi                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_broadcastvnx1si                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_broadcastvnx2si                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_broadcastvnx4si                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_broadcastvnx8si                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_broadcastvnx16si                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_broadcastvnx1di                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_broadcastvnx2di                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_broadcastvnx4di                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_broadcastvnx8di                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_broadcastvnx1sf                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_broadcastvnx2sf                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_broadcastvnx4sf                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_broadcastvnx8sf                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_broadcastvnx16sf                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_broadcastvnx1df                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_broadcastvnx2df                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_broadcastvnx4df                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_broadcastvnx8df                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_addvnx1di_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_andvnx1di_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_iorvnx1di_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_xorvnx1di_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_smaxvnx1di_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_umaxvnx1di_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sminvnx1di_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_uminvnx1di_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulvnx1di_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_addvnx2di_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_andvnx2di_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_iorvnx2di_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_xorvnx2di_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_smaxvnx2di_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_umaxvnx2di_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sminvnx2di_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_uminvnx2di_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulvnx2di_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_addvnx4di_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_andvnx4di_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_iorvnx4di_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_xorvnx4di_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_smaxvnx4di_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_umaxvnx4di_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sminvnx4di_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_uminvnx4di_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulvnx4di_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_addvnx8di_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_andvnx8di_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_iorvnx8di_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_xorvnx8di_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_smaxvnx8di_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_umaxvnx8di_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sminvnx8di_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_uminvnx8di_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulvnx8di_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_subvnx1di_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_divvnx1di_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_udivvnx1di_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_modvnx1di_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_umodvnx1di_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_subvnx2di_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_divvnx2di_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_udivvnx2di_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_modvnx2di_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_umodvnx2di_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_subvnx4di_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_divvnx4di_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_udivvnx4di_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_modvnx4di_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_umodvnx4di_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_subvnx8di_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_divvnx8di_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_udivvnx8di_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_modvnx8di_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_umodvnx8di_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_subvnx1di_reverse_scalar            (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_subvnx2di_reverse_scalar            (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_subvnx4di_reverse_scalar            (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_subvnx8di_reverse_scalar            (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhvnx1di_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhuvnx1di_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhsuvnx1di_scalar                 (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhvnx2di_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhuvnx2di_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhsuvnx2di_scalar                 (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhvnx4di_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhuvnx4di_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhsuvnx4di_scalar                 (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhvnx8di_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhuvnx8di_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mulhsuvnx8di_scalar                 (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_adcvnx1di_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_adcvnx2di_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_adcvnx4di_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_adcvnx8di_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sbcvnx1di_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sbcvnx2di_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sbcvnx4di_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sbcvnx8di_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_madcvnx1di_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_madcvnx2di_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_madcvnx4di_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_madcvnx8di_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_msbcvnx1di_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_msbcvnx2di_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_msbcvnx4di_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_msbcvnx8di_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_madcvnx1di_overflow_scalar          (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_madcvnx2di_overflow_scalar          (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_madcvnx4di_overflow_scalar          (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_madcvnx8di_overflow_scalar          (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_msbcvnx1di_overflow_scalar          (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_msbcvnx2di_overflow_scalar          (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_msbcvnx4di_overflow_scalar          (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_msbcvnx8di_overflow_scalar          (rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssaddvnx1di_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_usaddvnx1di_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssaddvnx2di_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_usaddvnx2di_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssaddvnx4di_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_usaddvnx4di_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ssaddvnx8di_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_usaddvnx8di_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sssubvnx1di_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ussubvnx1di_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sssubvnx2di_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ussubvnx2di_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sssubvnx4di_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ussubvnx4di_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_sssubvnx8di_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ussubvnx8di_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_aadduvnx1di_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_aaddvnx1di_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_asubuvnx1di_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_asubvnx1di_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_smulvnx1di_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_aadduvnx2di_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_aaddvnx2di_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_asubuvnx2di_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_asubvnx2di_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_smulvnx2di_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_aadduvnx4di_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_aaddvnx4di_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_asubuvnx4di_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_asubvnx4di_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_smulvnx4di_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_aadduvnx8di_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_aaddvnx8di_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_asubuvnx8di_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_asubvnx8di_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_smulvnx8di_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_cmpvnx1qi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_cmpvnx2qi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_cmpvnx4qi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_cmpvnx8qi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_cmpvnx16qi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_cmpvnx32qi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_cmpvnx64qi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_cmpvnx1hi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_cmpvnx2hi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_cmpvnx4hi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_cmpvnx8hi                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_cmpvnx16hi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_cmpvnx32hi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_cmpvnx1si                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_cmpvnx2si                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_cmpvnx4si                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_cmpvnx8si                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_cmpvnx16si                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_cmpvnx1di                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_cmpvnx2di                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_cmpvnx4di                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_cmpvnx8di                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ltgevnx1qi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ltgevnx2qi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ltgevnx4qi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ltgevnx8qi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ltgevnx16qi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ltgevnx32qi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ltgevnx64qi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ltgevnx1hi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ltgevnx2hi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ltgevnx4hi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ltgevnx8hi                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ltgevnx16hi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ltgevnx32hi                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ltgevnx1si                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ltgevnx2si                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ltgevnx4si                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ltgevnx8si                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ltgevnx16si                         (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ltgevnx1di                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ltgevnx2di                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ltgevnx4di                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_ltgevnx8di                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_cmpvnx1qi_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_cmpvnx2qi_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_cmpvnx4qi_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_cmpvnx8qi_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_cmpvnx16qi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_cmpvnx32qi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_cmpvnx64qi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_cmpvnx1hi_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_cmpvnx2hi_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_cmpvnx4hi_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_cmpvnx8hi_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_cmpvnx16hi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_cmpvnx32hi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_cmpvnx1si_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_cmpvnx2si_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_cmpvnx4si_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_cmpvnx8si_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_cmpvnx16si_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_eqnevnx1qi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_eqnevnx2qi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_eqnevnx4qi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_eqnevnx8qi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_eqnevnx16qi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_eqnevnx32qi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_eqnevnx64qi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_eqnevnx1hi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_eqnevnx2hi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_eqnevnx4hi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_eqnevnx8hi_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_eqnevnx16hi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_eqnevnx32hi_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_eqnevnx1si_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_eqnevnx2si_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_eqnevnx4si_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_eqnevnx8si_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_eqnevnx16si_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_cmpvnx1di_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_cmpvnx2di_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_cmpvnx4di_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_cmpvnx8di_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_eqnevnx1di_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_eqnevnx2di_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_eqnevnx4di_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_eqnevnx8di_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_gevnx1qi_scalar                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_gevnx2qi_scalar                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_gevnx4qi_scalar                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_gevnx8qi_scalar                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_gevnx16qi_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_gevnx32qi_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_gevnx64qi_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_gevnx1hi_scalar                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_gevnx2hi_scalar                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_gevnx4hi_scalar                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_gevnx8hi_scalar                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_gevnx16hi_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_gevnx32hi_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_gevnx1si_scalar                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_gevnx2si_scalar                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_gevnx4si_scalar                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_gevnx8si_scalar                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_gevnx16si_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_gevnx1di_scalar                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_gevnx2di_scalar                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_gevnx4di_scalar                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_gevnx8di_scalar                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mul_plusvnx1qi                      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mul_plusvnx2qi                      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mul_plusvnx4qi                      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mul_plusvnx8qi                      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mul_plusvnx16qi                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mul_plusvnx32qi                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mul_plusvnx64qi                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mul_plusvnx1hi                      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mul_plusvnx2hi                      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mul_plusvnx4hi                      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mul_plusvnx8hi                      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mul_plusvnx16hi                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mul_plusvnx32hi                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mul_plusvnx1si                      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mul_plusvnx2si                      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mul_plusvnx4si                      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mul_plusvnx8si                      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mul_plusvnx16si                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mul_plusvnx1di                      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mul_plusvnx2di                      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mul_plusvnx4di                      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mul_plusvnx8di                      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mul_plusvnx1qi_scalar               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mul_plusvnx2qi_scalar               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mul_plusvnx4qi_scalar               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mul_plusvnx8qi_scalar               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mul_plusvnx16qi_scalar              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mul_plusvnx32qi_scalar              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mul_plusvnx64qi_scalar              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mul_plusvnx1hi_scalar               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mul_plusvnx2hi_scalar               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mul_plusvnx4hi_scalar               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mul_plusvnx8hi_scalar               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mul_plusvnx16hi_scalar              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mul_plusvnx32hi_scalar              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mul_plusvnx1si_scalar               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mul_plusvnx2si_scalar               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mul_plusvnx4si_scalar               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mul_plusvnx8si_scalar               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mul_plusvnx16si_scalar              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mul_plusvnx1di_scalar               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mul_plusvnx2di_scalar               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mul_plusvnx4di_scalar               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mul_plusvnx8di_scalar               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_minus_mulvnx1qi                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_minus_mulvnx2qi                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_minus_mulvnx4qi                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_minus_mulvnx8qi                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_minus_mulvnx16qi                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_minus_mulvnx32qi                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_minus_mulvnx64qi                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_minus_mulvnx1hi                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_minus_mulvnx2hi                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_minus_mulvnx4hi                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_minus_mulvnx8hi                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_minus_mulvnx16hi                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_minus_mulvnx32hi                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_minus_mulvnx1si                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_minus_mulvnx2si                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_minus_mulvnx4si                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_minus_mulvnx8si                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_minus_mulvnx16si                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_minus_mulvnx1di                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_minus_mulvnx2di                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_minus_mulvnx4di                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_minus_mulvnx8di                     (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_minus_mulvnx1qi_scalar              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_minus_mulvnx2qi_scalar              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_minus_mulvnx4qi_scalar              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_minus_mulvnx8qi_scalar              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_minus_mulvnx16qi_scalar             (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_minus_mulvnx32qi_scalar             (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_minus_mulvnx64qi_scalar             (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_minus_mulvnx1hi_scalar              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_minus_mulvnx2hi_scalar              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_minus_mulvnx4hi_scalar              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_minus_mulvnx8hi_scalar              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_minus_mulvnx16hi_scalar             (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_minus_mulvnx32hi_scalar             (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_minus_mulvnx1si_scalar              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_minus_mulvnx2si_scalar              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_minus_mulvnx4si_scalar              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_minus_mulvnx8si_scalar              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_minus_mulvnx16si_scalar             (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_minus_mulvnx1di_scalar              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_minus_mulvnx2di_scalar              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_minus_mulvnx4di_scalar              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_minus_mulvnx8di_scalar              (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mul_addvnx1sf                       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mul_subvnx1sf                       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mul_addvnx2sf                       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mul_subvnx2sf                       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mul_addvnx4sf                       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mul_subvnx4sf                       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mul_addvnx8sf                       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mul_subvnx8sf                       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mul_addvnx16sf                      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mul_subvnx16sf                      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mul_addvnx1df                       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mul_subvnx1df                       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mul_addvnx2df                       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mul_subvnx2df                       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mul_addvnx4df                       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mul_subvnx4df                       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mul_addvnx8df                       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mul_subvnx8df                       (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mul_addvnx1sf_scalar                (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mul_subvnx1sf_scalar                (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mul_addvnx2sf_scalar                (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mul_subvnx2sf_scalar                (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mul_addvnx4sf_scalar                (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mul_subvnx4sf_scalar                (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mul_addvnx8sf_scalar                (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mul_subvnx8sf_scalar                (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mul_addvnx16sf_scalar               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mul_subvnx16sf_scalar               (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mul_addvnx1df_scalar                (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mul_subvnx1df_scalar                (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mul_addvnx2df_scalar                (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mul_subvnx2df_scalar                (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mul_addvnx4df_scalar                (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mul_subvnx4df_scalar                (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mul_addvnx8df_scalar                (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mul_subvnx8df_scalar                (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mul_neg_addvnx1sf                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mul_neg_subvnx1sf                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mul_neg_addvnx2sf                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mul_neg_subvnx2sf                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mul_neg_addvnx4sf                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mul_neg_subvnx4sf                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mul_neg_addvnx8sf                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mul_neg_subvnx8sf                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mul_neg_addvnx16sf                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mul_neg_subvnx16sf                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mul_neg_addvnx1df                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mul_neg_subvnx1df                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mul_neg_addvnx2df                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mul_neg_subvnx2df                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mul_neg_addvnx4df                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mul_neg_subvnx4df                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mul_neg_addvnx8df                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mul_neg_subvnx8df                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mul_neg_addvnx1sf_scalar            (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mul_neg_subvnx1sf_scalar            (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mul_neg_addvnx2sf_scalar            (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mul_neg_subvnx2sf_scalar            (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mul_neg_addvnx4sf_scalar            (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mul_neg_subvnx4sf_scalar            (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mul_neg_addvnx8sf_scalar            (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mul_neg_subvnx8sf_scalar            (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mul_neg_addvnx16sf_scalar           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mul_neg_subvnx16sf_scalar           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mul_neg_addvnx1df_scalar            (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mul_neg_subvnx1df_scalar            (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mul_neg_addvnx2df_scalar            (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mul_neg_subvnx2df_scalar            (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mul_neg_addvnx4df_scalar            (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mul_neg_subvnx4df_scalar            (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mul_neg_addvnx8df_scalar            (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_mul_neg_subvnx8df_scalar            (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_cmpvnx1sf                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_cmpvnx2sf                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_cmpvnx4sf                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_cmpvnx8sf                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_cmpvnx16sf                          (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_cmpvnx1df                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_cmpvnx2df                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_cmpvnx4df                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_cmpvnx8df                           (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_cmpvnx1sf_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_cmpvnx2sf_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_cmpvnx4sf_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_cmpvnx8sf_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_cmpvnx16sf_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_cmpvnx1df_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_cmpvnx2df_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_cmpvnx4df_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_cmpvnx8df_scalar                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_eqnevnx1sf_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_eqnevnx2sf_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_eqnevnx4sf_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_eqnevnx8sf_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_eqnevnx16sf_scalar                  (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_eqnevnx1df_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_eqnevnx2df_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_eqnevnx4df_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_eqnevnx8df_scalar                   (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_extract_firstvnx1qi                 (rtx, rtx);
extern rtx        gen_pred_extract_firstvnx2qi                 (rtx, rtx);
extern rtx        gen_pred_extract_firstvnx4qi                 (rtx, rtx);
extern rtx        gen_pred_extract_firstvnx8qi                 (rtx, rtx);
extern rtx        gen_pred_extract_firstvnx16qi                (rtx, rtx);
extern rtx        gen_pred_extract_firstvnx32qi                (rtx, rtx);
extern rtx        gen_pred_extract_firstvnx64qi                (rtx, rtx);
extern rtx        gen_pred_extract_firstvnx1hi                 (rtx, rtx);
extern rtx        gen_pred_extract_firstvnx2hi                 (rtx, rtx);
extern rtx        gen_pred_extract_firstvnx4hi                 (rtx, rtx);
extern rtx        gen_pred_extract_firstvnx8hi                 (rtx, rtx);
extern rtx        gen_pred_extract_firstvnx16hi                (rtx, rtx);
extern rtx        gen_pred_extract_firstvnx32hi                (rtx, rtx);
extern rtx        gen_pred_extract_firstvnx1si                 (rtx, rtx);
extern rtx        gen_pred_extract_firstvnx2si                 (rtx, rtx);
extern rtx        gen_pred_extract_firstvnx4si                 (rtx, rtx);
extern rtx        gen_pred_extract_firstvnx8si                 (rtx, rtx);
extern rtx        gen_pred_extract_firstvnx16si                (rtx, rtx);
extern rtx        gen_pred_extract_firstvnx1di                 (rtx, rtx);
extern rtx        gen_pred_extract_firstvnx2di                 (rtx, rtx);
extern rtx        gen_pred_extract_firstvnx4di                 (rtx, rtx);
extern rtx        gen_pred_extract_firstvnx8di                 (rtx, rtx);
extern rtx        gen_pred_extract_firstvnx1sf                 (rtx, rtx);
extern rtx        gen_pred_extract_firstvnx2sf                 (rtx, rtx);
extern rtx        gen_pred_extract_firstvnx4sf                 (rtx, rtx);
extern rtx        gen_pred_extract_firstvnx8sf                 (rtx, rtx);
extern rtx        gen_pred_extract_firstvnx16sf                (rtx, rtx);
extern rtx        gen_pred_extract_firstvnx1df                 (rtx, rtx);
extern rtx        gen_pred_extract_firstvnx2df                 (rtx, rtx);
extern rtx        gen_pred_extract_firstvnx4df                 (rtx, rtx);
extern rtx        gen_pred_extract_firstvnx8df                 (rtx, rtx);
extern rtx        gen_pred_slide1upvnx1di                      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_slide1downvnx1di                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_slide1upvnx2di                      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_slide1downvnx2di                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_slide1upvnx4di                      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_slide1downvnx4di                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_slide1upvnx8di                      (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);
extern rtx        gen_pred_slide1downvnx8di                    (rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx, rtx);

#endif /* GCC_INSN_FLAGS_H */
