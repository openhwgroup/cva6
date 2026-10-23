# Issue #3463
#
# Reserved HLV/HLVX rs2 encodings and HSV encodings with a non-zero rd
# must raise an illegal-instruction exception (mcause = 2).

  .section .text
  .align 2
  .option norvc
  .globl main

main:
  la t0, trap_handler
  csrw mtvec, t0
  csrw medeleg, zero

  # Use a valid aligned address/source in case a malformed instruction
  # incorrectly reaches execution.
  la t1, scratch

  # HLV.B/BU family: only rs2=0/1 are valid.
  # funct7=0110000, rs2=2, rs1=t1, rd=t0.
  la s1, test_hlv_h
  .word 0x602342f3
  li a0, 10
  j finish

test_hlv_h:
  # HLV.H/HU/HLVX.HU family: only rs2=0/1/3 are valid.
  # Use reserved rs2=2.
  la s1, test_hlv_w
  .word 0x642342f3
  li a0, 11
  j finish

test_hlv_w:
  # HLV.W/WU/HLVX.WU family: only rs2=0/1/3 are valid.
  # Use reserved rs2=2.
  la s1, test_hlv_d
  .word 0x682342f3
  li a0, 12
  j finish

test_hlv_d:
  # HLV.D requires rs2=0. Use reserved rs2=1.
  la s1, test_hsv_b
  .word 0x6c1342f3
  li a0, 13
  j finish

test_hsv_b:
  # HSV.B requires rd=0. Use rd=t0 (x5).
  la s1, test_hsv_h
  .word 0x627342f3
  li a0, 14
  j finish

test_hsv_h:
  # HSV.H requires rd=0. Use rd=t0 (x5).
  la s1, test_hsv_w
  .word 0x667342f3
  li a0, 15
  j finish

test_hsv_w:
  # HSV.W requires rd=0. Use rd=t0 (x5).
  la s1, test_hsv_d
  .word 0x6a7342f3
  li a0, 16
  j finish

test_hsv_d:
  # HSV.D requires rd=0. Use rd=t0 (x5).
  la s1, pass
  .word 0x6e7342f3
  li a0, 17
  j finish

  .align 2
trap_handler:
  csrr t3, mcause
  li t4, 2
  bne t3, t4, wrong_cause

  # Continue with the next malformed encoding.
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
