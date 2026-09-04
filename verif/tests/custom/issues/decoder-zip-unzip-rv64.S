# SUCCESS(a0=0) iff BOTH zip (0x08f31293) and unzip (0x08f35293) trap with
# mcause==2 on RV64. FAIL if either retires (bug) or wrong cause.
  .section .text
  .align 2
  .option norvc
  .globl main
main:
  la t0, th
  csrw mtvec, t0
  csrw medeleg, zero
  li s1, 0                  # 0 = expecting zip trap, 1 = expecting unzip trap
  .word 0x08f31293          # zip x5,x6
  li a0, 10                 # retired -> bug
  j fin
phase1:
  li s1, 1
  .word 0x08f35293          # unzip x5,x6
  li a0, 11                 # retired -> bug
  j fin
  .align 2
th:
  csrr t0, mcause
  li t1, 2
  bne t0, t1, wc
  bnez s1, pass_all         # unzip trapped correctly -> done
  la t1, phase1
  csrw mepc, t1
  mret
pass_all:
  li a0, 0
  j fin
wc:
  ori a0, t0, 0x40
fin:
  jal exit
