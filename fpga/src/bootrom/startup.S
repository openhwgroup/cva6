# start sequence of the bootloader
# 
# 
#include <smp.h>
#define DRAM_BASE 0x80000000

  .section .text.init
  .option norvc
  .globl _prog_start
_prog_start:
  smp_pause(s1, s2)
  la sp, _sp
  call main
  smp_resume(s1, s2)
  csrr a0, mhartid
  la a1, _dtb
  li s1, DRAM_BASE
  jr s1

  .section .rodata
.section .rodata.dtb, "a", @progbits
.globl _dtb
.align 5, 0
_dtb:
.incbin "ariane.dtb"