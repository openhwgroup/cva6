# See LICENSE for license details.

#*****************************************************************************
# hlvx_gstage_repro.S
#-----------------------------------------------------------------------------
#
# Reproducer for the HLVX permission rule being applied to the G-stage check
# on a VS-stage page-table read (core/cva6_mmu/cva6_ptw.sv, data-path
# permission test).
#
# During a two-stage walk, when the PTW is at G_INTERMED_STAGE it is
# G-stage-translating the guest physical address of a VS-stage page table.
# That access is an IMPLICIT LOAD, so it requires pte.r and must NOT require
# pte.x.  The data-path permission test applies hlvx_inst_i unconditionally,
# which switches the pte.r term off and makes pte.x mandatory, so an HLVX
# access faults on any G-stage mapping of guest page-table memory that is
# R=1, X=0.  The instruction path just above already carries the stage
# condition.
#
# Mapping under test:
#   G-stage  : identity 4 KiB leaves over [DRAM_BASE, DRAM_BASE + 2 MiB),
#              V R W X U A D everywhere, EXCEPT the three pages holding
#              vs_root / vs_l1 / vs_l0, which are V R W U A D (X=0).
#              That is the normal W^X hypervisor mapping: guest page tables
#              are data, not code.
#   VS-stage : GVA 0x1000 -> GPA target_page, V R W X A D (U=0, SPVP=1).
#
# The target page is executable at BOTH stages, so HLVX is legal here.  The
# only non-executable pages in the whole setup are the guest's own page
# tables, which no correct implementation should require to be executable.
#
#   probe 1 (control) : hlv.d   t1, (0x1000)  -- uses the pte.r term, must pass
#   hfence.vvma / hfence.gvma / sfence.vma    -- force a FRESH walk
#   probe 2           : hlvx.hu t2, (0x1000)  -- same address, same tables
#
# GSTAGE_PT_EXEC variant: identical program with PTE_X added to the G-stage
# leaves that map vs_root / vs_l1 / vs_l0.  It must pass on unmodified RTL,
# which isolates the X bit on the guest page tables as the only variable.
#
# tohost = 21 (TESTNUM 21) is the defect: probe 2 took a LOAD_GUEST_PAGE_FAULT.
# Any other trap reports its own mcause as tohost.
#

#include "riscv_test.h"
#include "test_macros.h"

.option arch, +h

#define CSR_HSTATUS  0x600
#define CSR_VSSTATUS 0x200
#define CSR_VSATP    0x280
#define CSR_HEDELEG  0x602
#define CSR_HGATP    0x680

#define HGATP_MODE_SV39X4 8
#define HSTATUS_SPVP      (1 << 8)
#define CAUSE_LOAD_GUEST_PAGE_FAULT 21

#define GVA_TARGET   0x1000
#define TARGET_VALUE 0x00c0ffee0badf00d

/* Ordinary G-stage leaf: identity, executable. */
#define G_LEAF     (PTE_V | PTE_R | PTE_W | PTE_X | PTE_U | PTE_A | PTE_D)

/* G-stage leaf for the pages that HOLD the VS-stage page tables. */
#ifdef GSTAGE_PT_EXEC
# define G_LEAF_PT (PTE_V | PTE_R | PTE_W | PTE_X | PTE_U | PTE_A | PTE_D)
#else
# define G_LEAF_PT (PTE_V | PTE_R | PTE_W | PTE_U | PTE_A | PTE_D)
#endif

/* VS-stage leaf: readable AND executable, so HLVX is legal at the VS stage. */
#define VS_LEAF    (PTE_V | PTE_R | PTE_W | PTE_X | PTE_A | PTE_D)

/* Map the 4 KiB page holding \sym in g_l0 with G_LEAF_PT (X=0 by default). */
.macro GMAP_PT sym
  la   t0, \sym
  srli t1, t0, 12                    /* PPN of the page holding the table */
  slli t2, t1, 10
  li   t3, G_LEAF_PT
  or   t2, t2, t3                    /* the PTE */
  li   t3, (DRAM_BASE >> 12)
  sub  t1, t1, t3                    /* page index within the mapped 2 MiB */
  slli t1, t1, 3
  la   t3, g_l0
  add  t1, t3, t1
  sd   t2, 0(t1)
.endm

/* tmp0 = PTE pointing at \sym's page, with permission bits \perm. */
.macro PTE_FOR sym, perm
  la   t0, \sym
  srli t0, t0, 12
  slli t0, t0, 10
  li   t1, \perm
  or   t0, t0, t1
.endm

RVTEST_RV64M
RVTEST_CODE_BEGIN

  csrw CSR_HEDELEG, zero
  csrw medeleg, zero

  # ------------------------------------------------------------------
  # G-stage l0: identity 4 KiB leaves over [DRAM_BASE, DRAM_BASE + 2 MiB).
  # Everything the guest touches is inside this window.
  # ------------------------------------------------------------------
  la   a4, g_l0
  li   a5, DRAM_BASE
  li   a6, 0
1:
  slli t0, a6, 12
  add  t0, t0, a5                    /* physical address of this page */
  srli t1, t0, 12
  slli t1, t1, 10
  li   t2, G_LEAF
  or   t1, t1, t2
  slli t2, a6, 3
  add  t2, a4, t2
  sd   t1, 0(t2)
  addi a6, a6, 1
  li   t0, 512
  blt  a6, t0, 1b

  # ------------------------------------------------------------------
  # The three pages holding the VS-stage tables are DATA: X=0.
  # This is the only thing the control variant changes.
  # ------------------------------------------------------------------
  GMAP_PT vs_root
  GMAP_PT vs_l1
  GMAP_PT vs_l0

  # ---- G-stage upper levels: g_root[GPA[40:30]] -> g_l1[GPA[29:21]] -> g_l0
  PTE_FOR g_l0, PTE_V
  la   t2, g_l1
  li   t3, ((DRAM_BASE >> 21) & 0x1ff)
  slli t3, t3, 3
  add  t2, t2, t3
  sd   t0, 0(t2)

  PTE_FOR g_l1, PTE_V
  la   t2, g_root
  li   t3, (DRAM_BASE >> 30)         /* Sv39x4 root index, 2048 entries */
  slli t3, t3, 3
  add  t2, t2, t3
  sd   t0, 0(t2)

  # ---- VS-stage (Sv39): GVA_TARGET -> target_page.  VPN2 = VPN1 = 0.
  PTE_FOR vs_l1, PTE_V
  la   t2, vs_root
  sd   t0, (((GVA_TARGET >> 30) & 0x1ff) * 8)(t2)

  PTE_FOR vs_l0, PTE_V
  la   t2, vs_l1
  sd   t0, (((GVA_TARGET >> 21) & 0x1ff) * 8)(t2)

  /* GPA == PA here, because the G-stage window is an identity map. */
  PTE_FOR target_page, VS_LEAF
  la   t2, vs_l0
  sd   t0, (((GVA_TARGET >> 12) & 0x1ff) * 8)(t2)

  # ---- turn translation on
  la   t0, g_root
  srli t0, t0, 12
  li   t1, HGATP_MODE_SV39X4
  slli t1, t1, 60
  or   t0, t0, t1
  csrw CSR_HGATP, t0

  la   t0, vs_root
  srli t0, t0, 12
  li   t1, SATP_MODE_SV39
  slli t1, t1, 60
  or   t0, t0, t1
  csrw CSR_VSATP, t0

  li   t0, HSTATUS_SPVP              /* HLV/HLVX run at effective privilege S */
  csrw CSR_HSTATUS, t0
  csrw CSR_VSSTATUS, zero            /* vsstatus.MXR = 0 */
  li   t0, SSTATUS_MXR
  csrc sstatus, t0                   /* sstatus.MXR = 0 */
  sfence.vma
  hfence.gvma
  hfence.vvma

  # ==================================================================
  # probe 1 (control): ordinary guest load. Uses the pte.r term at every
  # stage, so it is unaffected by the defect. Any trap here is a setup
  # problem, not a result.
  # ==================================================================
  li   TESTNUM, 1
  li   a0, GVA_TARGET
  hlv.d t1, (a0)
  li   t0, TARGET_VALUE
  bne  t1, t0, fail

  # Force a fresh walk: no DTLB or G-stage entry may survive into probe 2.
  hfence.vvma
  hfence.gvma
  sfence.vma

  # ==================================================================
  # probe 2: same address, same tables, HLVX. The target page is
  # executable at both stages, so this must retire.
  # ==================================================================
  li   TESTNUM, 2
  li   t2, 0
  hlvx.hu t2, (a0)
  li   t0, (TARGET_VALUE & 0xffff)
  bne  t2, t0, fail
  j    pass

  TEST_PASSFAIL

  .align 2
  .global mtvec_handler
mtvec_handler:
  csrr t5, mcause
  li   t6, 2
  bne  TESTNUM, t6, 1f
  li   t6, CAUSE_LOAD_GUEST_PAGE_FAULT
  bne  t5, t6, 1f
  li   TESTNUM, 21                   /* THE DEFECT: HLVX faulted on the */
  j    fail                          /* G-stage read of a VS page table */
1:
  mv   TESTNUM, t5                   /* anything else: report the cause */
  j    fail

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN
  TEST_DATA

.align 12
vs_root: .fill 512, 8, 0
.align 12
vs_l1:   .fill 512, 8, 0
.align 12
vs_l0:   .fill 512, 8, 0
.align 14
g_root:  .fill 2048, 8, 0            /* 16 KiB Sv39x4 root */
.align 12
g_l1:    .fill 512, 8, 0
.align 12
g_l0:    .fill 512, 8, 0
.align 12
target_page:
  .dword TARGET_VALUE
  .fill 511, 8, 0
RVTEST_DATA_END
