#define SBI_EXT_BASE 0x10
#define SBI_EXT_BASE_GET_SPEC_VERSION 0x0

.section .trampoline, "aw", @progbits

.globl test_ret
test_ret:
.type test_ret, @function
.size test_ret, .Lend_test_ret - test_ret
ret
.Lend_test_ret:

.globl test_ecall
test_ecall:
.type test_ecall, @function
.size test_ecall, .Lend_test_ecall - test_ecall
li a7, SBI_EXT_BASE
li a6, SBI_EXT_BASE_GET_SPEC_VERSION
ecall
.Lend_test_ecall:

.balign 8
.globl flag
flag:
.type flag, @object
.size flag, 8
.quad 0x0
