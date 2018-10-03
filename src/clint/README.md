# CLINT (Core-local Interrupt Controller)

This repository contains a RISC-V privilege spec 1.11 (WIP) compatible CLINT for the Ariane Core.

The CLINT plugs into an existing AXI Bus with an AXI 4 Lite interface. The IP mirrors transaction IDs and is fully pin-compatible with the full AXI 4 interface. It does not support burst transfers (as specified in the AMBA 4 Bus specifcation)

|      Address      | Description |                      Note                      |
|-------------------|-------------|------------------------------------------------|
| `BASE` + `0x0`    | msip        | Machine mode software interrupt (IPI)          |
| `BASE` + `0x4000` | mtimecmp    | Machine mode timer compare register for Hart 0 |
| `BASE` + `0xBFF8` | mtime       | Timer register                                 |
