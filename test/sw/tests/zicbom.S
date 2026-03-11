.section .text
.global main
main:
  // Set up local trap handler to skip CBO if not supported
  la    t0, trap_handler
  csrw  mtvec, t0

  // s0 = cached address of tdat, s1 = uncached alias
  la    s0, tdat
  la    t0, __base_dram
  la    t1, __base_uncached
  sub   t0, s0, t0
  add   s1, t0, t1

  // -------------------------------------------------------
  // Test 1: cbo.clean - write-back
  // Store via cache, clean, verify uncached alias sees the value
  // -------------------------------------------------------
  li    t2, 0x1111
  sd    t2, 0(s0)
  cbo.clean 0(s0)
  fence w, r
  ld    t3, 0(s1)
  bne   t3, t2, fail

  // -------------------------------------------------------
  // Test 2: cbo.clean - no eviction
  // Line stays cached after clean; an uncached write is not
  // visible through the cached alias
  // -------------------------------------------------------
  li    t2, 0x2222
  sd    t2, 0(s1)
  fence w, r
  ld    t3, 0(s0)
  li    t2, 0x1111
  bne   t3, t2, fail

  // -------------------------------------------------------
  // Test 3: cbo.flush - write-back
  // Store via cache, flush, verify uncached alias sees the value
  // -------------------------------------------------------
  li    t2, 0x3333
  sd    t2, 0(s0)
  cbo.flush 0(s0)
  fence w, r
  ld    t3, 0(s1)
  bne   t3, t2, fail

  // -------------------------------------------------------
  // Test 4: cbo.flush - eviction
  // Line is evicted after flush; an uncached write is
  // visible through the cached alias (forces re-fetch)
  // -------------------------------------------------------
  li    t2, 0x4444
  sd    t2, 0(s1)
  fence w, r
  ld    t3, 0(s0)
  bne   t3, t2, fail

  // -------------------------------------------------------
  // Test 5: cbo.inval - eviction on clean line
  // Use cbo.clean to produce a known clean line, then
  // invalidate and verify the cached alias re-fetches
  // -------------------------------------------------------
  li    t2, 0x5555
  sd    t2, 0(s0)
  cbo.clean 0(s0)
  cbo.inval 0(s0)
  li    t2, 0x6666
  sd    t2, 0(s1)
  fence w, r
  ld    t3, 0(s0)
  bne   t3, t2, fail

pass:
  li    a0, 0
  ret

fail:
  li    a0, 1
  ret

// Skips the offending instruction on trap for a clean fail
// if CBO instructions are not supported.
.align 8
trap_handler:
  csrr  t4, mepc
  addi  t4, t4, 4
  csrw  mepc, t4
  mret

.section .data
.align 6
tdat:
  .dword 0xdeadbeefdeadbeef
  .dword 0xdeadbeefdeadbeef
