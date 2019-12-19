# DOC: Documentation for CORE-V verification.

Eventually, this is where you will find the Verification Strategy, Verification Environment
specification(s) and Verifiction Plan(s) (aka Test Plans) for the various CORE-V cores verified here.

## Proposed Feature List for CV32E40P and CV32E40
The table below is extracted from CV32E40P-v1.0_draft00.pdf, which is in this directory.  You should consult the PDF for additional information and in case of decrepancy between this table and the PDF, the PDF shall be interpreted as being correct.

### Base instruction set plus standard instruction extensions

| Feature | RI5CY | CV32E40P | CV32E40 | Documentation |
|---------|-------|----------|---------|---------------|
| RV32I | Yes | Yes | Yes | v2.1 ([RV_PRIVILEGED_ISA] ) |
| Zifencei extension | Yes | Yes | Yes | v2.0 ([RV_PRIVILEGED_ISA] ) |
| Zicsr extension | Yes | Yes | Yes | v2.0 ([RV_PRIVILEGED_ISA] ) |
| M extension | Yes | Yes | Yes | v2.0 ([RV_PRIVILEGED_ISA] ) |
| F extension | Optional | Tentative | Optional | v2.2 ([RV_PRIVILEGED_ISA] ) |
| Zfinx extension | Optional | TBD | TBD | Not standardized yet |
| C extension | Yes | Yes | Yes | v2.0 ([RV_PRIVILEGED_ISA] ) |
| B extension | No | No | Yes | TBD ([RV_PRIVILEGED_ISA] ) |
| P extension | No | No | Yes | TBD ([RV_PRIVILEGED_ISA] ) |
| N extension | No | No | No | Not standardized yet |
| Counters extension | No | Yes 9 | Yes 9 | ([RV_PRIVILEGED_ISA] ) |

### Privileged spec
| Feature | RI5CY | CV32E40P | CV32E40 | Documentation |
|---------|-------|----------|---------|---------------|
| User mode | Optional | No | Yes | ([RV_PRIVILEGED_ISA] ) |
| PMP | Optional 1 4 | No | Yes 5 | |

### Xpulp instruction extensions
| Feature | RI5CY | CV32E40P | CV32E40 | Documentation |
|---------|-------|----------|---------|---------------|
| Post-increment load/store | Yes | Yes | Yes | [RI5CY_USER_MANUAL] |
| Hardware Loop | Yes | No 6 | No 6 | [RI5CY_USER_MANUAL] |
| Bit Manipulation | Yes | Yes | No 7 | [RI5CY_USER_MANUAL] |
| General ALU | Yes | Yes | Yes | [RI5CY_USER_MANUAL] |
| Immediate branching | Yes | Yes | Yes | [RI5CY_USER_MANUAL] |
| SIMD | Yes | TBD 13 | No 8 | [RI5CY_USER_MANUAL] |
### Custom circuitry
| Feature | RI5CY | CV32E40P | CV32E40 | Documentation |
|---------|-------|----------|---------|---------------|
| RI5CY performance counters | Yes | No 10 | No 10 | [RI5CY_USER_MANUAL] |
| Advanced Processing Unit itf | Yes | No | Yes | |
| 128-bit wide Instruction Bus itf | Optional | No | No | |
| RI5CY interrupt scheme 2 | Yes | No | No | |
| PULP cluster itf | Yes | No | No | |
| Sleep interface | No | Yes | Yes | https://github.com/pulp-platform/riscv/issues/131 |
### Future extensions
| Feature | RI5CY | CV32E40P | CV32E40 | Documentation |
|---------|-------|----------|---------|---------------|
| Stack overflow protection | No | No | Yes | https://github.com/pulp-platform/riscv/issues/183 |
### Interrupts
| Feature | RI5CY | CV32E40P | CV32E40 | Documentation |
|---------|-------|----------|---------|---------------|
| CLINT | No | Yes | No | |
| CLINT extension (MIP2, MIE2) No | TBD | No |
| CLIC | No | No | Yes | Version TBD ([CLIC]) |
### Debug & Trace
| Feature | RI5CY | CV32E40P | CV32E40 | Documentation |
|---------|-------|----------|---------|---------------|
| Debug | Yes 14 | Yes 14 | Yes 14 | Version 0.13.2 ([RV_DEBUG] ) |
| Trigger module 12 | No | Yes | Yes | Version 0.13.2 ([RV_DEBUG] ) |
| Trace | No | No | Yes | Version TBD () |
### RVI-compliant interface
| Feature | RI5CY | CV32E40P | CV32E40 | Documentation |
|---------|-------|----------|---------|---------------|
| RVI Instruction Bus interface | No 3 | Yes | Yes | ([RVI]) |
| RVI Data Bus interface | No 3 | Yes | Yes | ([RVI]) |



## CV32E40P Schedule
| Date | Milestone | Description |
|------|-----------|-------------|
| 2019-12-30 | Feature Agreement | Not yet signed off |
| 2020-03-15 | All RTL Features coded | |
| 2020-07-30 | RTL Frozen | Verification Complete |

