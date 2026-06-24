# See LICENSE for license details.

#*****************************************************************************
# noncanonical.S
#-----------------------------------------------------------------------------
#
# Test that non-canonical SV39 virtual addresses generate page-fault
# exceptions.  In SV39, bits [63:39] of a virtual address must all equal
# bit [38].  When they do not, the hardware must raise:
#
#   - LOAD_PAGE_FAULT   (mcause 13) for loads,
#   - STORE_PAGE_FAULT  (mcause 15) for stores,
#   - FETCH_PAGE_FAULT  (mcause 12) for instruction fetches.
#
# See: https://github.com/openhwgroup/cva6/issues/371
#

#include "riscv_test.h"
#include "test_macros.h"

#if (DRAM_BASE >> 30 << 30) != DRAM_BASE
# error This test requires DRAM_BASE be SV39 superpage-aligned
#endif

RVTEST_RV64M
RVTEST_CODE_BEGIN

  # ------------------------------------------------------------------
  # Set up SV39 with a 1 GiB identity-mapped superpage at DRAM_BASE.
  # The page table entry has full permissions so that only the
  # non-canonical address check can cause a fault.
  # ------------------------------------------------------------------
  li a0, (SATP_MODE & ~(SATP_MODE<<1)) * SATP_MODE_SV39
  la a1, page_table_1
  srl a1, a1, RISCV_PGSHIFT
  or a1, a1, a0
  csrw satp, a1
  sfence.vma

  # Build a non-canonical virtual address: 0x0000_0080_0000_0000.
  # Bit 39 = 1, bit 38 = 0  ->  bits [63:39] != bit [38].
  li s1, 1
  slli s1, s1, 39

  # ==================================================================
  # Test 2 -- Load from non-canonical address  (expect LOAD_PAGE_FAULT)
  # ==================================================================
  li TESTNUM, 2

  # Enable S-mode address translation for loads/stores while staying
  # in M-mode, by setting MPRV=1 and MPP=S.
  li t0, MSTATUS_MPP | MSTATUS_MPRV
  csrc mstatus, t0
  li t0, ((MSTATUS_MPP & ~(MSTATUS_MPP<<1)) * PRV_S) | MSTATUS_MPRV
  csrs mstatus, t0

  lb t0, 0(s1)
  j fail                        # should not be reached

  # ==================================================================
  # Test 3 -- Store to non-canonical address  (expect STORE_PAGE_FAULT)
  # ==================================================================
test_3:
  li TESTNUM, 3

  sb t0, 0(s1)
  j fail                        # should not be reached

  # ==================================================================
  # Test 4 -- Fetch from non-canonical address (expect FETCH_PAGE_FAULT)
  # ==================================================================
test_4:
  li TESTNUM, 4

  # Clear MPRV so subsequent instructions use M-mode for data access.
  li t0, MSTATUS_MPRV
  csrc mstatus, t0

  # Prepare to enter S-mode via mret: set MPP = S.
  li t0, MSTATUS_MPP
  csrc mstatus, t0
  li t0, (MSTATUS_MPP & ~(MSTATUS_MPP<<1)) * PRV_S
  csrs mstatus, t0

  # Set the return address to the non-canonical address and mret.
  # The CPU will attempt an instruction fetch from s1 in S-mode
  # with SV39 translation active, triggering FETCH_PAGE_FAULT.
  csrw mepc, s1
  mret
  # (control never reaches here -- the fetch itself faults)

  TEST_PASSFAIL

  # ------------------------------------------------------------------
  # M-mode trap handler
  # ------------------------------------------------------------------
  .align 2
  .global mtvec_handler
mtvec_handler:
  csrr t0, mcause

  # --- Test 2: expect LOAD_PAGE_FAULT ---
  li t1, 2
  bne TESTNUM, t1, 1f
  li t1, CAUSE_LOAD_PAGE_FAULT
  bne t0, t1, fail

  # Re-establish MPRV + MPP=S for the store test and jump to test_3.
  li t0, MSTATUS_MPP | MSTATUS_MPRV
  csrc mstatus, t0
  li t0, ((MSTATUS_MPP & ~(MSTATUS_MPP<<1)) * PRV_S) | MSTATUS_MPRV
  csrs mstatus, t0
  j test_3

1:
  # --- Test 3: expect STORE_PAGE_FAULT ---
  li t1, 3
  bne TESTNUM, t1, 1f
  li t1, CAUSE_STORE_PAGE_FAULT
  bne t0, t1, fail
  j test_4

1:
  # --- Test 4: expect FETCH_PAGE_FAULT ---
  li t1, 4
  bne TESTNUM, t1, fail
  li t1, CAUSE_FETCH_PAGE_FAULT
  bne t0, t1, fail
  j pass

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

  TEST_DATA

.align 12
page_table_1: .dword (DRAM_BASE/RISCV_PGSIZE << PTE_PPN_SHIFT) | PTE_V | PTE_U | PTE_R | PTE_W | PTE_X | PTE_A | PTE_D

RVTEST_DATA_END
