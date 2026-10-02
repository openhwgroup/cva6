// Measures the LR/SC behaviour an ACT DUT description depends on: the size of
// the reservation set, whether the SC must match the LR address exactly, and
// whether a plain store by the same hart drops the reservation. Each SC prints
// its result: 0 when it succeeds, nonzero when it fails.
//
// The base is 64-byte aligned, so an SC at base + d with d < 2^n hits the same
// naturally aligned 2^n-byte set as the LR: the first offset that fails gives
// the set size.

#define CONSOLE 0x10001000

.macro PRINT label, reg
  la    a1, \label
  jal   ra, puts
  mv    a3, \reg
  jal   ra, puthex
  li    t0, '\n'
  li    t1, CONSOLE
  sw    t0, 0(t1)
.endm

// lr.d at the base, sc.d at base + \off.
.macro LRSC_D off, label
  lr.d  t0, (s0)
  addi  t2, s0, \off
  sc.d  s2, s1, (t2)
  PRINT \label, s2
.endm

.section .text
.global main
main:
  addi  sp, sp, -16
  sd    ra, 0(sp)
  la    s0, buf
  li    s1, 0x1234

  // Without a reservation the SC must fail.
  sc.d  s2, s1, (s0)
  PRINT .Lnone, s2

  LRSC_D 0,  .Ld0
  LRSC_D 8,  .Ld8
  LRSC_D 16, .Ld16
  LRSC_D 32, .Ld32
  LRSC_D 64, .Ld64

  // Inside the same 8 bytes: succeeds unless the address must match exactly.
  lr.w  t0, (s0)
  addi  t2, s0, 4
  sc.w  s2, s1, (t2)
  PRINT .Lw4, s2

  // A plain store by the same hart to the reserved address.
  lr.d  t0, (s0)
  sd    s1, 0(s0)
  sc.d  s2, s1, (s0)
  PRINT .Lst0, s2

  // A plain store by the same hart outside the reservation set.
  lr.d  t0, (s0)
  sd    s1, 128(s0)
  sc.d  s2, s1, (s0)
  PRINT .Lst128, s2

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
.Lnone:   .asciz "sc.d without lr.d:                 "
.Ld0:     .asciz "lr.d base, sc.d base +  0:         "
.Ld8:     .asciz "lr.d base, sc.d base +  8:         "
.Ld16:    .asciz "lr.d base, sc.d base + 16:         "
.Ld32:    .asciz "lr.d base, sc.d base + 32:         "
.Ld64:    .asciz "lr.d base, sc.d base + 64:         "
.Lw4:     .asciz "lr.w base, sc.w base +  4:         "
.Lst0:    .asciz "lr.d, sd to base, sc.d base:       "
.Lst128:  .asciz "lr.d, sd to base + 128, sc.d base: "

.section .data
.balign 256
buf:
  .fill 256, 1, 0x55
