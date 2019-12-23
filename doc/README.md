# DOC: Documentation for CORE-V verification.

Eventually, this is where you will find the Verification Strategy, Verification Environment
specification(s) and Verifiction Plan(s) (aka Test Plans) for the various CORE-V cores verified here.

## CV32E40P Schedule
| Date | Milestone | Description |
|------|-----------|-------------|
| 2019-12-30 | Feature Agreement | Not yet signed off |
| 2020-03-15 | All RTL Features coded | |
| 2020-07-30 | RTL Frozen | Verification Complete, start of final synthesis |
| 2020-xx-xx | Final Netlist | Last gate-level netlist with extracted timing available |
| 2020-xx-xx | Tape-out (PG) | GDSII shipped to Fab |
| 2020-xx-xx | Samples | Initial bring up of first silicon on demo board |

## Proposed Feature List for CV32E40P and CV32E40
The table below is extracted from CV32E40P-v1.0_draft00.pdf, which is in this directory.  You should consult the PDF for additional information and in case of decrepancy between this table and the PDF, the PDF shall be interpreted as being correct.

The `Verification Comment` columnn in the table is a preliminary assessment by Verification regarding the liklihood of completing the verification of a given feature in time for RTL Freeze of the CV32E40P.
- **OK** indicates nominal risk to complete verification of this feature in time for RTL Freeze.
- **OK, high risk** indicates elevated risk of completing verification of this feature in time for RTL Freeze.
- **TBD** indicates that Verification has not yet assessed the risk of this feature.
- An empty cell is "no comment" typically because the feature is indicated as "No" for CV32E40P.
- **No** indicates that Verification probably cannot achieve complete coverage of the feature in time for RTL Freeze, regardless of the Yes/No/Tenative indication in the CV32E40P column.

### Base instruction set plus standard instruction extensions

| Feature | RI5CY | CV32E40P | CV32E40 | Documentation | Verification Comment |
|---------|-------|----------|---------|---------------|----------------------|
| RV32I | Yes | Yes | Yes | v2.1 ([RV_PRIVILEGED_ISA] ) | OK |
| Zifencei extension | Yes | Yes | Yes | v2.0 ([RV_PRIVILEGED_ISA] ) | OK |
| Zicsr extension | Yes | Yes | Yes | v2.0 ([RV_PRIVILEGED_ISA] ) | OK |
| M extension | Yes | Yes | Yes | v2.0 ([RV_PRIVILEGED_ISA] ) | OK |
| F extension | Optional | Tentative | Optional | v2.2 ([RV_PRIVILEGED_ISA] ) | OK, high risk |
| Zfinx extension | Optional | TBD | TBD | Not standardized yet | OK |
| C extension | Yes | Yes | Yes | v2.0 ([RV_PRIVILEGED_ISA] ) | OK |
| B extension | No | No | Yes | TBD ([RV_PRIVILEGED_ISA] ) | |
| P extension | No | No | Yes | TBD ([RV_PRIVILEGED_ISA] ) | |
| N extension | No | No | No | Not standardized yet | |
| Counters extension | No | Yes 9 | Yes 9 | ([RV_PRIVILEGED_ISA] ) | OK |
| Instruction Exceptions | Yes | Yes | Yes | ([RV_ISA] ) | OK |

### Privileged spec
| Feature | RI5CY | CV32E40P | CV32E40 | Documentation | Verification Comment |
|---------|-------|----------|---------|---------------|----------------------|
| User mode | Optional | No | Yes | ([RV_PRIVILEGED_ISA] ) | |
| PMP | Optional 1 4 | No | Yes 5 | | |

### Xpulp instruction extensions
| Feature | RI5CY | CV32E40P | CV32E40 | Documentation | Verification Comment |
|---------|-------|----------|---------|---------------|----------------------|
| Post-increment load/store | Yes | Yes | Yes | [RI5CY_USER_MANUAL] | OK |
| Hardware Loop | Yes | No 6 | No 6 | [RI5CY_USER_MANUAL] |  |
| Bit Manipulation | Yes | Yes | No 7 | [RI5CY_USER_MANUAL] | OK |
| General ALU | Yes | Yes | Yes | [RI5CY_USER_MANUAL] | OK |
| Immediate branching | Yes | Yes | Yes | [RI5CY_USER_MANUAL] | OK |
| SIMD | Yes | TBD 13 | No 8 | [RI5CY_USER_MANUAL] | TBD |
### Custom circuitry
| Feature | RI5CY | CV32E40P | CV32E40 | Documentation | Verification Comment |
|---------|-------|----------|---------|---------------|----------------------|
| RI5CY performance counters | Yes | No 10 | No 10 | [RI5CY_USER_MANUAL] | |
| Advanced Processing Unit itf | Yes | No | Yes | | |
| 128-bit wide Instruction Bus itf | Optional | No | No | | |
| RI5CY interrupt scheme 2 | Yes | No | No | | |
| PULP cluster itf | Yes | No | No | | |
| Sleep interface | No | Yes | Yes | https://github.com/pulp-platform/riscv/issues/131 | TBD |
### Future extensions
| Feature | RI5CY | CV32E40P | CV32E40 | Documentation | Verification Comment |
|---------|-------|----------|---------|---------------|----------------------|
| Stack overflow protection | No | No | Yes | https://github.com/pulp-platform/riscv/issues/183 | |
### Interrupts
| Feature | RI5CY | CV32E40P | CV32E40 | Documentation | Verification Comment |
|---------|-------|----------|---------|---------------|----------------------|
| CLINT | No | Yes | No | | OK |
| CLINT extension (MIP2, MIE2) No | TBD | No | OK |
| CLIC | No | No | Yes | Version TBD ([CLIC]) | |
### Debug & Trace
| Feature | RI5CY | CV32E40P | CV32E40 | Documentation | Verification Comment |
|---------|-------|----------|---------|---------------|----------------------|
| Debug | Yes 14 | Yes 14 | Yes 14 | Version 0.13.2 ([RV_DEBUG] ) | OK, high risk |
| Trigger module 12 | No | Yes | Yes | Version 0.13.2 ([RV_DEBUG] ) | OK, high risk |
| Trace | No | No | Yes | Version TBD () | |
### RVI-compliant interface
| Feature | RI5CY | CV32E40P | CV32E40 | Documentation | Verification Comment |
|---------|-------|----------|---------|---------------|----------------------|
| RVI Instruction Bus interface | No 3 | Yes | Yes | ([RVI]) | OK |
| RVI Data Bus interface | No 3 | Yes | Yes | ([RVI]) | OK |

