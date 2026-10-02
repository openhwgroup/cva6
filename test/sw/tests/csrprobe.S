// Dumps the WARL behaviour of the CSRs an ACT DUT description depends on:
// each is written with a pattern, read back and restored, and printed as
// "csr <- written -> read". A CSR the core does not implement traps; the
// handler skips the access and the line reads TRAP. Running it on two
// configurations and diffing the output shows where their descriptions must
// differ -- measuring rather than reading the RTL.

#define CONSOLE 0x10001000

// satp/hgatp/vsatp ignore a write with an unsupported mode entirely, so they
// are written with Sv39 (Sv39x4 for hgatp) and every other field set.
#define ATP_SV39_ALL 0x8fffffffffffffff

.macro PROBE csr, val
  .pushsection .rodata
.Lname\@: .asciz "\csr"
  .popsection
  la    a1, .Lname\@
  jal   ra, puts
  la    a1, .Larrow
  jal   ra, puts
  li    a3, \val
  jal   ra, puthex
  la    a1, .Lsep
  jal   ra, puts
  li    s11, 0
  li    t0, \val
  csrr  s5, \csr
  csrw  \csr, t0
  csrr  s0, \csr
  csrw  \csr, s5
  bnez  s11, 1f
  mv    a3, s0
  jal   ra, puthex
  j     2f
1:
  la    a1, .Ltrap
  jal   ra, puts
2:
  li    t0, '\n'
  li    t1, CONSOLE
  sw    t0, 0(t1)
.endm

.section .text
.global main
main:
  addi  sp, sp, -16
  sd    ra, 0(sp)
  la    t0, probe_trap
  csrw  mtvec, t0

  PROBE misa, -1
  PROBE mstatus, -1
  PROBE medeleg, -1
  PROBE mideleg, -1
  PROBE mie, -1
  PROBE mip, -1
  PROBE mtvec, -1             // mode 3 (CLIC on cores that have it)
  PROBE mtvec, -2             // mode 2 (reserved)
  PROBE mtvec, -3             // mode 1 (vectored)
  PROBE mtvec, -4             // mode 0 (direct)
  PROBE mcounteren, -1
  PROBE mcountinhibit, -1
  PROBE menvcfg, -1
  .irp n, 3, 4, 5, 6, 7, 8, 9, 10, 31
  PROBE mhpmcounter\n, -1
  .endr
  .irp n, 3, 8, 9
  PROBE mhpmevent\n, -1
  .endr

  PROBE sstatus, -1
  PROBE sie, -1
  PROBE sip, -1
  PROBE stvec, -1
  PROBE stvec, -2
  PROBE stvec, -3
  PROBE stvec, -4
  PROBE scounteren, -1
  PROBE senvcfg, -1
  PROBE satp, ATP_SV39_ALL

  PROBE hstatus, -1
  PROBE hedeleg, -1
  PROBE hideleg, -1
  PROBE hie, -1
  PROBE hvip, -1
  PROBE hgeie, -1
  PROBE hcounteren, -1
  PROBE henvcfg, -1
  PROBE hgatp, ATP_SV39_ALL
  PROBE vsstatus, -1
  PROBE vsie, -1
  PROBE vstvec, -1
  PROBE vstvec, -2
  PROBE vstvec, -3
  PROBE vstvec, -4
  PROBE vsatp, ATP_SV39_ALL

  ld    ra, 0(sp)
  addi  sp, sp, 16
  li    a0, 0
  ret

// Skips the faulting CSR access and flags it. Every access probed is a
// 32-bit CSR instruction.
.align 8
probe_trap:
  csrr  t6, mepc
  addi  t6, t6, 4
  csrw  mepc, t6
  li    s11, 1
  mret

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
.Larrow: .asciz " <- "
.Lsep:   .asciz " -> "
.Ltrap:  .asciz "TRAP"
