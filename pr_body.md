## Why this PR is needed

While developing an interface-level formal scoreboard for the CVA6 MMU,
I encountered an inconsistency between the same-cycle DTLB PPN output and
the PPN contained in the final LSU physical address.

The LSU/MMU interface exposes:

- `lsu_dtlb_ppn_o` together with `lsu_dtlb_hit_o` in cycle N
- `lsu_paddr_o` together with `lsu_valid_o` in cycle N+1

The formal checker captures the PPN reported on the DTLB-hit cycle and
compares it against the PPN extracted from the final physical address:

```systemverilog
lsu_paddr_o[CVA6Cfg.PLEN-1:12]

The checked invariant is:

captured lsu_dtlb_ppn_o ==
lsu_paddr_o[CVA6Cfg.PLEN-1:12]
Formal counterexample

For an Sv39 1 GiB superpage, the pre-fix RTL produced:

lsu_paddr_o     = 0x17EFD555
expected PPN    = 0x17EFD
lsu_dtlb_ppn_o  = 0x17EFD000

The same-cycle PPN was therefore shifted by exactly 12 bits.

A separate capture-sanity property confirmed that the checker sampled
the intended same-cycle value, excluding a scoreboard timing error.

Root cause

For an Sv39 1 GiB superpage:

VA[29:12] -> PA[29:12]

Since the PPN already excludes the 12-bit page offset:

PPN = PA >> 12

the correct PPN mapping is:

VA[29:12] -> PPN[17:0]

Using physical-address-style indices on the PPN output instead places
the substituted value 12 positions too high.

The same coordinate distinction applies to middle-level superpages.

Fix

Construct the same-cycle lsu_dtlb_ppn_o using PPN-aligned destination
indices while keeping lsu_paddr_o in physical-address coordinates.

For the largest Sv39 superpage:

if (dtlb_is_page_n[0]) begin
  lsu_dtlb_ppn_o[PPNWMin-12:0] =
      lsu_vaddr_n[PPNWMin:12];
end

For the middle-level superpage, use the elaboration-safe indexed
part-select:

if (CVA6Cfg.PtLevels == 3 &&
    dtlb_is_page_n[CVA6Cfg.PtLevels-2]) begin
  lsu_dtlb_ppn_o[0+:MegaPageSubstWidth] =
      lsu_vaddr_n[(9+CVA6Cfg.PtLevels)+:MegaPageSubstWidth];
end
Verification

Before correction:

expected PPN    = 0x17EFD
reported PPN    = 0x17EFD000
RESULT          = FAIL

With PPN-aligned construction:

expected PPN    = 0x17EFD
reported PPN    = 0x17EFD
RESULT          = PASS

This was found through formal scoreboard verification of the MMU
interface rather than by reproducing the internal address-construction
logic in the checker.

Scope

The formal counterexample was obtained with an Sv39 configuration.

The property checks consistency between LSU-visible MMU outputs and is
not intended as a complete proof of PTW, PMP, or hypervisor behavior.
