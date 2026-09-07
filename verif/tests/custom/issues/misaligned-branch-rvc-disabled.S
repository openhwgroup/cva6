  .option norvc
  .globl main

main:
  .balign 4
branch_site:
  beq zero, zero, misaligned_target
  j fail

  .2byte 0
misaligned_target:
  j fail                    # Reaching here means the expected trap did not occur

  .2byte 0
  .globl handle_trap
handle_trap:
  bnez a0, fail             # mcause must be 0: instruction-address-misaligned
  j pass

.balign 4
fail:
  li a0, 1
  call exit

.balign 4
pass:
  li a0, 0
  call exit
