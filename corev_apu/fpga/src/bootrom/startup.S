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
  li sp, 0x84000000
  call main
  smp_resume(s1, s2)
  csrr a0, mhartid
  la a1, _dtb
  li s1, DRAM_BASE
  jr s1

  .section .dtb
  .globl _dtb
  .align 4, 0
_dtb:
#if __riscv_xlen == 64
  .incbin "cv64a6.dtb"
#else
  .incbin "cv32a6.dtb"
#endif
