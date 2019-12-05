// This is free and unencumbered software released into the public domain.
//
// Anyone is free to copy, modify, publish, use, compile, sell, or
// distribute this software, either in source code form or as a compiled
// binary, for any purpose, commercial or non-commercial, and by any
// means.

#define ENABLE_QREGS
#define ENABLE_RVTST
#define ENABLE_SIEVE
#define ENABLE_MULTST
#define ENABLE_STATS

.set timer_irq_mask, 0x15000000
.set timer_irq_val, 0x15000004
.set print_port, 0x10000000
.set test_ret_val, 0x20000000

.section .vectors, "ax"
.option norvc
vector_table:
	j sw_irq_handler /* ecall, illegal insn and data prohibited */
	j __no_irq_handler
	j __no_irq_handler
vector_table_timer:
	j timer_irq_handler
	j __no_irq_handler
	j __no_irq_handler
	j __no_irq_handler
	j __no_irq_handler
	j __no_irq_handler
	j __no_irq_handler
	j __no_irq_handler
	j __no_irq_handler
	j __no_irq_handler
	j __no_irq_handler
	j __no_irq_handler
	j __no_irq_handler
	j __no_irq_handler
	j __no_irq_handler
	j __no_irq_handler
	j __no_irq_handler
	j __no_irq_handler
	j __no_irq_handler
	j __no_irq_handler
	j __no_irq_handler
	j __no_irq_handler
	j __no_irq_handler
	j __no_irq_handler
	j __no_irq_handler
	j __no_irq_handler
	j __no_irq_handler
	j __no_irq_handler
	j __no_irq_handler

/* this is fixed to 0x8000, used for PULP_SECURE=0. We redirect this entry to the
new vector table (which is at mtvec) */
.section .legacy_irq, "ax"
	j vector_table
	j __no_irq_handler
	j __no_irq_handler
	j vector_table_timer


.section .start, "ax"
	j start

.section .text
.global irq
.global sieve
.global multest
.global hard_mul
.global hard_mulh
.global hard_mulhsu
.global hard_mulhu
.global stats
.global init_stats
.global print_dec
.global print_str


/* exception handling */
__no_irq_handler:
	la a0, no_exception_handler_msg
	jal ra, print_str
	j __no_irq_handler


sw_irq_handler:
	csrr t0, mcause
	slli t0, t0, 1  /* shift off the high bit */
	srli t0, t0, 1
	li t1, 2
	beq t0, t1, handle_illegal_insn
	li t1, 11
	beq t0, t1, handle_ecall
	li t1, 3
	beq t0, t1, handle_ebreak
	j handle_unknown

handle_ecall:
	/* la a0, ecall_msg */
	/* jal ra, print_str */ /* this is too verbose for now */
	j fail_test

handle_ebreak:
	la a0, ebreak_msg
	jal ra, print_str
	j fail_test

handle_illegal_insn:
	la a0, illegal_insn_msg
	jal ra, print_str
	j fail_test

handle_unknown:
	la a0, unknown_msg
	jal ra, print_str
	mv a0, t0
	jal ra, print_chr
	j fail_test

fail_test:
	li a0, 1
	sw a0, test_results, t1 /* signal failure */
	csrr a0, mepc
	addi a0, a0, 4
	csrw mepc, a0
	mret
	wfi

/* when we get a timeout we abort the whole testing procedure */
timer_irq_handler:
	la a0, timeout_msg
	jal ra, print_str
	li a0, 1
	sw a0, test_results, t1 /* signal failure */
	j fast_exit


/* Main program
 **********************************/

start:
	/* initialize global pointer */
.option push
.option norelax
1:	auipc gp, %pcrel_hi(__global_pointer$)
	addi  gp, gp, %pcrel_lo(1b)
.option pop

	/* start performance counters */
	jal ra, init_stats

	/* init bss to zero */
	li t0, 0
	la t1, __bss_start
	la t2, __bss_end

1:
	sw t0, 0(t1)
	addi t1, t1, 4
	ble t1, t2, 1b

	/* zero-initialize all registers */
	addi x1, zero, 0
	addi x2, zero, 0
	/* addi x3, zero, 0 */ /* gp already initialized */
	addi x4, zero, 0
	addi x5, zero, 0
	addi x6, zero, 0
	addi x7, zero, 0
	addi x8, zero, 0
	addi x9, zero, 0
	addi x10, zero, 0
	addi x11, zero, 0
	addi x12, zero, 0
	addi x13, zero, 0
	addi x14, zero, 0
	addi x15, zero, 0
	addi x16, zero, 0
	addi x17, zero, 0
	addi x18, zero, 0
	addi x19, zero, 0
	addi x20, zero, 0
	addi x21, zero, 0
	addi x22, zero, 0
	addi x23, zero, 0
	addi x24, zero, 0
	addi x25, zero, 0
	addi x26, zero, 0
	addi x27, zero, 0
	addi x28, zero, 0
	addi x29, zero, 0
	addi x30, zero, 0
	addi x31, zero, 0

	/* enable machine level interrupts */
	li      t0, 8
	csrrs   zero, mstatus, t0

	/* set timer irq mask */
	li a0, timer_irq_mask
	li a1, 0x8
	sw a1,0(a0)


#ifdef ENABLE_RVTST
#  define TEST(n) \
	.global n; \
	/* set timer value */;\
	li a0, timer_irq_val; \
	li a1, 100000; \
	sw a1, 0(a0); \
	/* return from test */;\
	jal zero,n; \
	.global n ## _ret; \
	n ## _ret:
#else
#  define TEST(n) \
	.global n ## _ret; \
	n ## _ret:
#endif
#ifdef RUN_RISCV_TESTS
	/* running riscv-tests */
	la a0, riscv_tests_msg
	call print_str

	TEST(simple)

	TEST(lui)
	TEST(auipc)
	//TEST(j) /* doesn't exist anymore */
	TEST(jal)
	TEST(jalr)

	TEST(beq)
	TEST(bne)
	TEST(blt)
	TEST(bge)
	TEST(bltu)
	TEST(bgeu)

	TEST(lb)
	TEST(lh)
	TEST(lw)
	TEST(lbu)
	TEST(lhu)

	TEST(sb)
	TEST(sh)
	TEST(sw)

	TEST(addi)
	TEST(slti) /* also tests sltiu */
	TEST(xori)
	TEST(ori)
	TEST(andi)
	TEST(slli)
	TEST(srli)
	TEST(srai)

	TEST(add)
	TEST(sub)
	TEST(sll)
	TEST(slt) /* what is with sltu ? */
	TEST(sltu)
	TEST(sltiu)
	TEST(xor)
	TEST(srl)
	TEST(sra)
	TEST(or)
	TEST(and)

	TEST(mulh)
	TEST(mulhsu)
	TEST(mulhu)
	TEST(mul)

	TEST(div)
	TEST(divu)
	TEST(rem)
	TEST(remu)

	/*TEST(rvc)*/

	TEST(fence_i)
#endif /* RUN_RISCV_TESTS */

#ifdef RUN_COMPLIANCE
	/* running riscv-compliance-tests */

	la a0, riscv_compliance_tests_msg
	call print_str

	TEST(I_ADD_01)
	TEST(I_ADDI_01)
	TEST(I_AND_01)
	TEST(I_ANDI_01)
	TEST(I_AUIPC_01)
	TEST(I_BEQ_01)
	TEST(I_BGE_01)
	TEST(I_BGEU_01)
	TEST(I_BLT_01)
	TEST(I_BLTU_01)
	TEST(I_BNE_01)

	TEST(I_CSRRC_01)
	TEST(I_CSRRCI_01)
	TEST(I_CSRRS_01)
	TEST(I_CSRRSI_01)
	TEST(I_CSRRW_01)
	TEST(I_CSRRWI_01)

	TEST(I_DELAY_SLOTS_01)
	TEST(I_EBREAK_01)
	TEST(I_ECALL_01)
	TEST(I_ENDIANESS_01)
	TEST(I_FENCE.I_01)
	TEST(I_IO)

	TEST(I_JAL_01)
	TEST(I_JALR_01)
	TEST(I_LB_01)
	TEST(I_LBU_01)
	TEST(I_LH_01)
	TEST(I_LHU_01)
	TEST(I_LUI_01)
	TEST(I_LW_01)

	/* bad test: RI5CY supports C extension meaning no exception on
	misaligned jumps */
	/* TEST(I_MISALIGN_JMP_01)  */
	/* TEST(I_MISALIGN_LDST_01) /* fails */

	TEST(I_NOP_01)
	TEST(I_OR_01)
	TEST(I_ORI_01)
	TEST(I_RF_size_01)
	TEST(I_RF_width_01)
	TEST(I_RF_x0_01)
	TEST(I_SB_01)

	TEST(I_SH_01)
	TEST(I_SLL_01)
	TEST(I_SLLI_01)
	TEST(I_SLT_01)
	TEST(I_SLTI_01)
	TEST(I_SLTIU_01)
	TEST(I_SLTU_01)
	TEST(I_SRA_01)
	TEST(I_SRAI_01)
	TEST(I_SRL_01)
	TEST(I_SRLI_01)
	TEST(I_SUB_01)
	TEST(I_SW_01)
	TEST(I_XOR_01)
	TEST(I_XORI_01)
#else
	/* NOT running riscv-compliance-tests */
	la a0, skip_riscv_compliance_tests_msg
	call print_str
#endif /* RUN_COMPLIANCE */

	/* set stack pointer */
	lui sp,(1024*1024)>>12

	/* set gp and tp */
	lui gp, %hi(0xdeadbeef)
	addi gp, gp, %lo(0xdeadbeef)
	addi tp, gp, 0

#ifdef RUN_COMPLIANCE
#ifdef ENABLE_SIEVE
	/* call sieve C code */
	jal ra,sieve
#endif

#ifdef ENABLE_MULTST
	/* call multest C code */
	jal ra,multest
#endif
#endif /* RUN_COMPLIANCE */

#ifdef ENABLE_STATS
	/* call stats C code */
	jal ra,stats
#endif

fast_exit:
	/* print "DONE\n" */
	lui a0,print_port>>12
	addi a1,zero,'D'
	addi a2,zero,'O'
	addi a3,zero,'N'
	addi a4,zero,'E'
	addi a5,zero,'\n'
	sw a1,0(a0)
	sw a2,0(a0)
	sw a3,0(a0)
	sw a4,0(a0)
	sw a5,0(a0)


	li a0, test_ret_val
	lw a1, test_results /* report result */
	sw a1,0(a0)

	wfi  /* we are done */

/* Hard mul functions for multest.c
 **********************************/

hard_mul:
	mul a0, a0, a1
	ret

hard_mulh:
	mulh a0, a0, a1
	ret

hard_mulhsu:
	mulhsu a0, a0, a1
	ret

hard_mulhu:
	mulhu a0, a0, a1
	ret


.section .rodata
illegal_insn_msg:
	.string "illegal instruction exception handler entered\n"
ecall_msg:
	.string "ecall exception handler entered\n"
ebreak_msg:
	.string "ebreak exception handler entered\n"
unknown_msg:
	.string "unknown exception handler entered\n"
no_exception_handler_msg:
	.string "no exception handler installed\n"
riscv_tests_msg:
	.string "\n\n!!! Running riscv-tests\n\n\n"
riscv_compliance_tests_msg:
	.string "\n\n!!! Running riscv-compliance-tests\n\n\n"
skip_riscv_compliance_tests_msg:
	.string "\n\n!!!NOT running riscv-compliance-tests\n\n\n"
timeout_msg:
	.string "\n\nTEST TIMEOUT, aborting...\n\n"
liveness_msg:
	.string "!!PING!!\n"

.section .data
.global test_results
test_results:
	.word 123456789
