# DOC: Documentation for CORE-V verification.

Eventually, this is where you will find the Verification Strategy, Verification Environment
specification(s) and Verifiction Plan(s) (aka Test Plans) for the various CORE-V cores verified here.

## CV32E40P Schedule
| Date | Milestone | Description |
|------|-----------|-------------|
| 2019-12-30 | Feature Agreement | Not yet signed off |
| 2020-03-15 | All RTL Features coded | |
| 2020-07-30 | RTL Frozen | Verification Complete |

## Proposed Feature List for CV32E40P and CV32E40
The table below is extracted from CV32E40P-v1.0_draft00.pdf, which is in this directory.  You should consult the PDF for additional information and in case of decrepancy between this table and the PDF, the PDF shall be interpreted as being correct.

The `Verification Comment` columnn in the table is a preliminary assessment by the Verification team regarding the liklihood of completing the verification of a given feature in time for RTL Freeze (CV32E40P only).
- OK indicates nominal risk - should be able to do it.
- TBD indicates that we've not assessed the risk of this feature
- No indicates that we probably cannot achieve complete coverage of the feature in time for RTL Freeze

### Base instruction set plus standard instruction extensions

| Feature | RI5CY | CV32E40P | CV32E40 | Documentation | Verification Comment |
|---------|-------|----------|---------|---------------|----------------------|
| RV32I | Yes | Yes | Yes | v2.1 ([RV_PRIVILEGED_ISA] ) | OK |
| Zifencei extension | Yes | Yes | Yes | v2.0 ([RV_PRIVILEGED_ISA] ) | OK |
| Zicsr extension | Yes | Yes | Yes | v2.0 ([RV_PRIVILEGED_ISA] ) | OK |
| M extension | Yes | Yes | Yes | v2.0 ([RV_PRIVILEGED_ISA] ) | OK |
| F extension | Optional | Tentative | Optional | v2.2 ([RV_PRIVILEGED_ISA] ) | OK |
| Zfinx extension | Optional | TBD | TBD | Not standardized yet | OK |
| C extension | Yes | Yes | Yes | v2.0 ([RV_PRIVILEGED_ISA] ) | OK |
| B extension | No | No | Yes | TBD ([RV_PRIVILEGED_ISA] ) | OK |
| P extension | No | No | Yes | TBD ([RV_PRIVILEGED_ISA] ) | OK |
| N extension | No | No | No | Not standardized yet | OK |
| Counters extension | No | Yes 9 | Yes 9 | ([RV_PRIVILEGED_ISA] ) | OK |

### Privileged spec
| Feature | RI5CY | CV32E40P | CV32E40 | Documentation | Verification Comment |
|---------|-------|----------|---------|---------------|----------------------|
| User mode | Optional | No | Yes | ([RV_PRIVILEGED_ISA] ) | OK |
| PMP | Optional 1 4 | No | Yes 5 | | OK |

### Xpulp instruction extensions
| Feature | RI5CY | CV32E40P | CV32E40 | Documentation | Verification Comment |
|---------|-------|----------|---------|---------------|----------------------|
| Post-increment load/store | Yes | Yes | Yes | [RI5CY_USER_MANUAL] | OK |
| Hardware Loop | Yes | No 6 | No 6 | [RI5CY_USER_MANUAL] | OK |
| Bit Manipulation | Yes | Yes | No 7 | [RI5CY_USER_MANUAL] | OK |
| General ALU | Yes | Yes | Yes | [RI5CY_USER_MANUAL] | OK |
| Immediate branching | Yes | Yes | Yes | [RI5CY_USER_MANUAL] | OK |
| SIMD | Yes | TBD 13 | No 8 | [RI5CY_USER_MANUAL] | OK |
### Custom circuitry
| Feature | RI5CY | CV32E40P | CV32E40 | Documentation | Verification Comment |
|---------|-------|----------|---------|---------------|----------------------|
| RI5CY performance counters | Yes | No 10 | No 10 | [RI5CY_USER_MANUAL] | TBD |
| Advanced Processing Unit itf | Yes | No | Yes | | OK |
| 128-bit wide Instruction Bus itf | Optional | No | No | | OK |
| RI5CY interrupt scheme 2 | Yes | No | No | | OK |
| PULP cluster itf | Yes | No | No | | OK |
| Sleep interface | No | Yes | Yes | https://github.com/pulp-platform/riscv/issues/131 | TBD |
### Future extensions
| Feature | RI5CY | CV32E40P | CV32E40 | Documentation | Verification Comment |
|---------|-------|----------|---------|---------------|----------------------|
| Stack overflow protection | No | No | Yes | https://github.com/pulp-platform/riscv/issues/183 | OK |
### Interrupts
| Feature | RI5CY | CV32E40P | CV32E40 | Documentation | Verification Comment |
|---------|-------|----------|---------|---------------|----------------------|
| CLINT | No | Yes | No | | OK |
| CLINT extension (MIP2, MIE2) No | TBD | No | OK |
| CLIC | No | No | Yes | Version TBD ([CLIC]) | OK |
### Debug & Trace
| Feature | RI5CY | CV32E40P | CV32E40 | Documentation | Verification Comment |
|---------|-------|----------|---------|---------------|----------------------|
| Debug | Yes 14 | Yes 14 | Yes 14 | Version 0.13.2 ([RV_DEBUG] ) | OK, high risk |
| Trigger module 12 | No | Yes | Yes | Version 0.13.2 ([RV_DEBUG] ) | OK, high risk |
| Trace | No | No | Yes | Version TBD () | OK |
### RVI-compliant interface
| Feature | RI5CY | CV32E40P | CV32E40 | Documentation | Verification Comment |
|---------|-------|----------|---------|---------------|----------------------|
| RVI Instruction Bus interface | No 3 | Yes | Yes | ([RVI]) | OK |
| RVI Data Bus interface | No 3 | Yes | Yes | ([RVI]) | OK |

