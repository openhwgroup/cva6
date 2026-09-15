# Issue #3463
#
# CBO.INVAL/CLEAN/FLUSH require rd=0.
# Encodings with a non-zero rd must raise illegal instruction (mcause = 2).

  .section .text
  .align 2
  .option norvc
  .globl main

main:
  la t0, trap_handler
  csrw mtvec, t0
  csrw medeleg, zero

  # Use an aligned address in case a malformed CBO incorrectly executes.
  la t1, scratch

  # CBO.INVAL: imm=0, rs1=t1, rd=t0 (invalid: rd must be zero).
  la s1, test_clean
  .word 0x0003228f
  li a0, 20
  j finish

test_clean:
  # CBO.CLEAN: imm=1, rs1=t1, rd=t0.
  la s1, test_flush
  .word 0x0013228f
  li a0, 21
  j finish

test_flush:
  # CBO.FLUSH: imm=2, rs1=t1, rd=t0.
  la s1, pass
  .word 0x0023228f
  li a0, 22
  j finish

  .align 2
trap_handler:
  csrr t3, mcause
  li t4, 2
  bne t3, t4, wrong_cause

  csrw mepc, s1
  mret

wrong_cause:
  ori a0, t3, 0x40
  j finish

pass:
  li a0, 0

finish:
  jal exit

  .section .data
  .balign 8
scratch:
  .dword 0x1122334455667788
