  .section .text
  .align 2
  .option norvc
  .globl main
main:
  csrw mideleg, zero
  csrr t0, mideleg
  li t1, 0x444
  and t2, t0, t1
  bne t2, t1, fail          # RO-1 bits (2,6,10) survive a zero write
  li t3, 0x200              # SEIP delegation (bit 9) - a real writable mideleg bit
  csrw mideleg, t3
  csrr t0, mideleg
  and t2, t0, t3
  bne t2, t3, fail          # writable bit takes
  li t1, 0x444
  and t2, t0, t1
  bne t2, t1, fail          # RO-1 bits still set alongside
  li a0, 0
  j fin
fail:
  li a0, 1
fin:
  jal exit
