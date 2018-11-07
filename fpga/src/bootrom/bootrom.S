#define DRAM_BASE 0x80000000

.section .text.start, "ax", @progbits
.globl _start
_start:
  li t0, (DRAM_BASE + 32 * 1024 * 1024)
  li t1, DRAM_BASE
2:
  sd x0, 0(t1)
  addi t1, t1, 8
  bne t1, t0, 2b
  fence
  fence.i
  li s0, DRAM_BASE
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
