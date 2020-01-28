# start sequence of the bootloader
# 
# 
#include <smp.h>
#define DRAM_BASE 0x80000000
#define DRAM_END  0x87FFFFF8

  .section .text.init
  .option norvc
  .globl _prog_start
_prog_start:
  li sp, DRAM_END
  la a1, _prog_start
  li a2, 0x8000
  add a2, a1, a2
  li a3, DRAM_BASE
_copy:
  ld a4, 0(a1)
  sd a4, 0(a3)
  ld a4, 8(a1)
  sd a4, 8(a3)
  ld a4, 16(a1)
  sd a4, 16(a3)
  ld a4, 24(a1)
  sd a4, 24(a3)
  add a1, a1, 32
  add a3, a3, 32
  blt a1, a2, _copy
  li a2, DRAM_BASE
  la a4, _reloc
  add a2, a2, a4
  la a4, _prog_start
  sub a2, a2, a4
  jalr ra, a2
_reloc:
  li a1, DRAM_BASE
  add ra, a1, zero
_clr:
  sd zero, 0(a3)
  sd zero, 8(a3)
  sd zero, 16(a3)
  sd zero, 24(a3)
  add a3, a3, 32
  blt a3, a2, _clr
        
  la a5, trap_entry
  csrw mtvec, a5  
  call main
trap_entry:
  csrr t0, mcause
  csrr t1, mepc
1:      
  wfi
  j 1b
