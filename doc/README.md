# DOC: Documentation for CORE-V verification.

Eventually, this is where you will find the Verification Strategy, Verification Environment
specification(s) and Verifiction Plan(s) (aka Test Plans) for the various CORE-V cores verified here.

## CV32E Features
| Feature | CV32E40P | CV32E40 | Description |
|---------|----------|---------|-------------|
| RV32IMFCZfinx| FPU not verified | Yes | Still under discussion |
| Load/Store with auto increment | Xplup | Xplup | Adds read and write port to RF |
| Hardware loop | No | Xpulp | |
| Bit Manipulation | Xpulp | B-ext | Not yet standardized |
| Enhanced signal processing | Xpulp | Xpulp | |
| Packed SIMD | Xpulp | P-ext | Not yet standardized |
| User Mode | No | Yes | Decoupled from PMP |
| Interrupt Scheme | CLINT | CLIC | |
| User Mode Interrupts | No | N-ext | Not yet standardized |
| PMP | No | v2 | Decouple from User Mode |
| AMBA-lite I/F | Yes | Yes | |
| Advanced Processing Unit I/F | No | Proprietary | Standardization needed? |
| Stack Overflow Protection | No | Yes | |
| Performance Counters | Yes | Yes | Follow the Standard |
| 128-bit wide IFETCH I/F | No | No | |


## CV32E40P Schedule
| Date | Milestone | Description |
|------|-----------|-------------|
| 2019-12-30 | Feature Agreement | Not yet signed off |
| 2020-03-15 | All RTL Features coded | |
| 2020-07-30 | RTL Frozen | Verification Complete |

