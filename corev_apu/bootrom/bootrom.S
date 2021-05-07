.section .text.start, "ax", @progbits
.globl _start
_start:
# bootrom.sv need to be functional in 64 and 32 bits,
# li s0, DRAM_BASE creates instructions not compatible with both
# versions. That's why we have replaced it by li and slli instructions
# to generates code compatible with both versions.
  li s0, 1
  slli s0, s0, 31
  csrr a0, mhartid
  la a1, _dtb
  jr s0

.section .text.hang, "ax", @progbits
.globl _hang
_hang:
  csrr a0, mhartid
  la a1, _dtb
1:
  wfi
  j 1b

.section .rodata.dtb, "a", @progbits
.globl _dtb
.align 5, 0
_dtb:
.incbin "ariane.dtb"
