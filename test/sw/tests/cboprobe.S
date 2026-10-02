// Measures the Zicbom behaviour an ACT DUT description depends on, on a
// configuration with a write-back data cache: the cache block size, and
// whether cbo.inval discards dirty data or writes it back. Memory is read
// through the testbench's uncached DRAM alias, which bypasses the cache:
// 0x4000_0000 + x maps onto DRAM at 0x8000_0000 + x (hw/cva6tb_soc.sv).

#define CONSOLE         0x10001000
#define UNCACHED_OFFSET 0x40000000

.macro PRINT label, reg
  la    a1, \label
  jal   ra, puts
  mv    a3, \reg
  jal   ra, puthex
  li    t0, '\n'
  li    t1, CONSOLE
  sw    t0, 0(t1)
.endm

// Counts the bytes of the 256-byte buffer that read \val through the alias:
// a2 = count, a4 = first offset, a5 = last offset (-1 when none).
.macro COUNT val
  li    a2, 0
  li    a4, -1
  li    a5, -1
  li    t1, 0
1:
  add   t2, s1, t1
  lbu   t0, 0(t2)
  li    t3, \val
  bne   t0, t3, 2f
  addi  a2, a2, 1
  bgez  a4, 3f
  mv    a4, t1
3:
  mv    a5, t1
2:
  addi  t1, t1, 1
  li    t3, 256
  blt   t1, t3, 1b
.endm

.section .text
.global main
main:
  addi  sp, sp, -16
  sd    ra, 0(sp)
  la    s0, buf
  li    s1, UNCACHED_OFFSET
  sub   s1, s0, s1                // uncached alias of buf

  // Allocate the buffer's lines with loads, then dirty them: a store that
  // misses might go straight to memory and prove nothing.
  li    t1, 0
1:
  add   t2, s0, t1
  ld    t0, 0(t2)
  addi  t1, t1, 8
  li    t3, 256
  blt   t1, t3, 1b
  li    t0, 0xaaaaaaaaaaaaaaaa
  li    t1, 0
1:
  add   t2, s0, t1
  sd    t0, 0(t2)
  addi  t1, t1, 8
  li    t3, 256
  blt   t1, t3, 1b
  fence

  // Nothing has reached memory yet if the lines are really dirty in the cache.
  COUNT 0xaa
  PRINT .Lbefore, a2

  // Clean one block in the middle: the bytes it writes back are the block.
  addi  t2, s0, 64
  cbo.clean (t2)
  fence
  COUNT 0xaa
  PRINT .Lblock, a2
  PRINT .Lfirst, a4
  PRINT .Llast, a5

  // Dirty that block again and invalidate it: a true invalidate discards the
  // new data, so memory and the cache both still hold the cleaned 0xaa.
  li    t0, 0xcccccccccccccccc
  sd    t0, 64(s0)
  addi  t2, s0, 64
  cbo.inval (t2)
  fence
  ld    s2, 64(s0)
  PRINT .Linvc, s2
  ld    s2, 64(s1)
  PRINT .Linvu, s2

  // cbo.flush must write a dirty block back.
  li    t0, 0xeeeeeeeeeeeeeeee
  sd    t0, 128(s0)
  addi  t2, s0, 128
  cbo.flush (t2)
  fence
  ld    s2, 128(s1)
  PRINT .Lflush, s2

  ld    ra, 0(sp)
  addi  sp, sp, 16
  li    a0, 0
  ret

// Prints the NUL-terminated string at a1.
puts:
  li    t1, CONSOLE
1:
  lbu   t0, 0(a1)
  beqz  t0, 2f
  sw    t0, 0(t1)
  addi  a1, a1, 1
  j     1b
2:
  ret

// Prints a3 as 16 hex digits.
puthex:
  li    t1, CONSOLE
  li    t2, 60
1:
  srl   t0, a3, t2
  andi  t0, t0, 0xf
  li    t3, 10
  blt   t0, t3, 2f
  addi  t0, t0, 'a'-10
  j     3f
2:
  addi  t0, t0, '0'
3:
  sw    t0, 0(t1)
  addi  t2, t2, -4
  bgez  t2, 1b
  ret

.section .rodata
.Lbefore: .asciz "dirty bytes in memory before clean: "
.Lblock:  .asciz "bytes written back by one cbo.clean: "
.Lfirst:  .asciz "  first offset: "
.Llast:   .asciz "  last offset:  "
.Linvc:   .asciz "after dirty + cbo.inval, cached read:   "
.Linvu:   .asciz "after dirty + cbo.inval, uncached read: "
.Lflush:  .asciz "after dirty + cbo.flush, uncached read: "

.section .data
.balign 256
buf:
  .fill 256, 1, 0x55
