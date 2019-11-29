#ifndef _ENV_PICORV32_TEST_H
#define _ENV_PICORV32_TEST_H

#ifndef TEST_FUNC_NAME
#  define TEST_FUNC_NAME mytest
#  define TEST_FUNC_TXT "mytest"
#  define TEST_FUNC_RET mytest_ret
#endif

#define RVTEST_RV32M
#define TESTNUM x28

#define RVTEST_CODE_BEGIN		\
	.text;				\
	.global TEST_FUNC_NAME;		\
	.global TEST_FUNC_RET;		\
TEST_FUNC_NAME:				\
	lui	a0,%hi(.test_name);	\
	addi	a0,a0,%lo(.test_name);	\
	lui	a2,0x10000000>>12;	\
.prname_next:				\
	lb	a1,0(a0);		\
	beq	a1,zero,.prname_done;	\
	sw	a1,0(a2);		\
	addi	a0,a0,1;		\
	jal	zero,.prname_next;	\
.test_name:				\
	.ascii TEST_FUNC_TXT;		\
	.byte 0x00;			\
	.balign 4, 0;			\
.prname_done:				\
	addi	a1,zero,'.';		\
	sw	a1,0(a2);		\
	sw	a1,0(a2);

#define RVTEST_PASS			\
	lui	a0,0x10000000>>12;	\
	addi	a1,zero,'O';		\
	addi	a2,zero,'K';		\
	addi	a3,zero,'\n';		\
	sw	a1,0(a0);		\
	sw	a2,0(a0);		\
	sw	a3,0(a0);		\
1:	auipc   t1, %pcrel_hi(TEST_FUNC_RET);	\
	jalr    x0, t1, %pcrel_lo(1b); \
	/* call    TEST_FUNC_RET; \ */
	/* lui     t0,%hi(TEST_FUNC_RET);  \ */
        /* jalr    zero, t0,%lo(TEST_FUNC_RET); */
	/* jal     TEST_FUNC_RET; */
	/* lui     t1,%hi(TEST_FUNC_RET);	\ */
	/* addi    t1,t1,%lo(TEST_FUNC_RET); \ */
        /* jr      t1; */

#define RVTEST_FAIL			\
	lui	a0,0x10000000>>12;	\
	addi	a1,zero,'E';		\
	addi	a2,zero,'R';		\
	addi	a3,zero,'O';		\
	addi	a4,zero,'\n';		\
	sw	a1,0(a0);		\
	sw	a2,0(a0);		\
	sw	a2,0(a0);		\
	sw	a3,0(a0);		\
	sw	a2,0(a0);		\
	sw	a4,0(a0);		\
	ecall;

#define RVTEST_CODE_END
#define RVTEST_DATA_BEGIN .balign 4;
#define RVTEST_DATA_END

#endif
