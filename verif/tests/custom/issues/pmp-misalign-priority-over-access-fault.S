  .section .text
  .align 2
  .option norvc
  .globl main
main:
  la t0, th
  csrw mtvec, t0
  csrw medeleg, zero
  csrw vsatp, zero
  li s4, 0
  li a2, 0x80100003
  li a3, 0x1122334455667788
  hsv.d a3, (a2)
  li a0, 10
  j fin
phase1:
  li s4, 1
  hlv.d a4, (a2)
  li a0, 0
  j fin
  .align 2
th:
  csrr t0, mcause
  csrr t1, mepc
  addi t1, t1, 4
  csrw mepc, t1
  bnez s4, 1f
  li t2, 6
  bne t0, t2, bad
  la t1, phase1
  csrw mepc, t1
  mret
1:
  li t2, 4
  bne t0, t2, bad
  li a0, 0
  j fin
bad:
  ori a0, t0, 0x40
fin:
  jal exit
