# See LICENSE for license details.

#*****************************************************************************
# napot.S
#-----------------------------------------------------------------------------
#
# Test Svnapot
#

#include "riscv_test.h"
#include "test_macros.h"

#if (DRAM_BASE >> 30 << 30) != DRAM_BASE
# error This test requires DRAM_BASE be SV39 superpage-aligned
#endif

#if __riscv_xlen != 64
# error This test requires RV64
#endif

RVTEST_RV64M
RVTEST_CODE_BEGIN

  # Construct the page table

#define MY_VA 0x40201010
  # VPN 2 == VPN 1 == VPN 0 == 0x1
  # Page offset == 0x10

  ####

  # Level 0 PTE contents

  # PPN
  la a0, my_data
  srl a0, a0, 12

  # adjust the PPN to be in NAPOT form
  li a1, ~0xF
  and a0, a0, a1
  ori a0, a0, 0x8

  # attributes
  sll a0, a0, PTE_PPN_SHIFT
  li a1, PTE_V | PTE_U | PTE_R | PTE_W | PTE_X | PTE_A | PTE_D | PTE_N
  or a0, a0, a1

  # Level 0 PTE address
  la a1, page_table
  addi a1, a1, ((MY_VA >> 12) & 0x1FF) * 8

  # Level 0 PTE store
  sd a0, (a1)

  ####

  # Level 1 PTE contents
  la a0, page_table
  srl a0, a0, 12
  sll a0, a0, PTE_PPN_SHIFT
  li a1, PTE_V
  or a0, a0, a1

  # Level 1 PTE address
  la a1, page_table
  addi a1, a1, ((MY_VA >> 21) & 0x1FF) * 8
  li a2, 1 << 12
  add a1, a1, a2

  # Level 1 PTE store
  sd a0, (a1)

  ####

  # Level 2 PTE contents
  la a0, page_table
  li a1, 1 << 12
  add a0, a0, a1
  srl a0, a0, 12
  sll a0, a0, PTE_PPN_SHIFT
  li a1, PTE_V
  or a0, a0, a1

  # Level 2 PTE address
  la a1, page_table
  addi a1, a1, ((MY_VA >> 30) & 0x1FF) * 8
  li a2, 2 << 12
  add a1, a1, a2

  # Level 2 PTE store
  sd a0, (a1)

  ####

  # Do a load from the PA that would be written if the PTE were misinterpreted as non-NAPOT
  la a0, my_data
  li a1, ~0xFFFF
  and a0, a0, a1
  li a1, 0x8000 | (MY_VA & 0xFFF)
  or a3, a0, a1
  li a1, 0
  sw a1, (a3)

  ####
  li TESTNUM, 1

  ## Turn on VM
  la a1, page_table
  li a2, 2 << 12
  add a1, a1, a2
  srl a1, a1, 12
  li a0, (SATP_MODE & ~(SATP_MODE<<1)) * SATP_MODE_SV39
  or a0, a0, a1
  csrw satp, a0
  sfence.vma

  # Set up MPRV with MPP=S and SUM=1, so loads and stores use S-mode and S can access U pages
  li a1, ((MSTATUS_MPP & ~(MSTATUS_MPP<<1)) * PRV_S) | MSTATUS_MPRV | MSTATUS_SUM
  csrs mstatus, a1

  # Do a store to MY_VA
  li a0, MY_VA
  li a1, 42
napot_store:
  sw a1, (a0)

  # Clear MPRV
  li a1, MSTATUS_MPRV
  csrc mstatus, a1

  # Do a load from the PA that would be written if the PTE were misinterpreted as non-NAPOT
  lw a1, (a3)

  # Check the result
  li a0, 42
  beq a1, a0, die

  # Do a load from the PA for MY_VA
  la a0, my_data
  li a1, MY_VA & 0xFFFF
  add a0, a0, a1
  lw a1, (a0)
  li a2, 42

  # Check the result
  bne a1, a2, die

  ####

  RVTEST_PASS

  TEST_PASSFAIL

  .align 2
  .global mtvec_handler
mtvec_handler:
  # Skip if Svnapot is not implemented.
  csrr t5, mcause
  li t6, CAUSE_STORE_PAGE_FAULT
  bne t5, t6, die
  csrr t5, mepc
  la t6, napot_store
  bne t5, t6, die
  csrr t5, mtval
  li t6, MY_VA
  beq t5, t6, pass
die:
  RVTEST_FAIL

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

  TEST_DATA

.align 20
page_table: .dword 0

.align 20
my_data: .dword 0

RVTEST_DATA_END