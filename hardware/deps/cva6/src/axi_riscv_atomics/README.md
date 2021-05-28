# AXI Adapter(s) for RISC-V Atomic Operations

**Disclaimer**: This repository is under active development and not yet stabilized.  Use only if you
know what you are doing and are prepared to adapt to wide-reaching changes as the project evolves.
Limited support is available for the latest v0.x version, but only for the latest, and we give no
backwards compatibility guarantees for versions before v1.0.

The modules in this repository implement atomic operations (AMOs) for RISC-V processors ("A"
extension version 2.0) on the AXI protocol.  The modules adheres to the RISC-V Weak Memory Ordering
(RVWMO) memory consistency model (version 0.1).

## Usage

Place one of the following modules in your memory hierarchy between an AXI master and slave, where
the slave owns a particular memory location (e.g., exclusive access to a memory controller or
adherence to a cache coherency protocol).  Choose depending on your needs:

- `axi_riscv_lrsc` tracks memory reservations for LR/SC, forwards only successful SCs, and responds
  accordingly.  This is sufficient to support LR/SC if the processor encodes them as AXI exclusive
  memory accesses.  Downstream modules do not have to support AXI exclusive memory accesses.

- `axi_riscv_atomics` implements all RISC-V AMOs in addition to LR/SC.  The processor needs to
  encode RISC-V AMOs as AXI atomic transactions (`AtomicSwap` for `AMOSWAP`, `AtomicLoad` with the
  corresponding opcode for all other AMOs).   This is sufficient to support the entire RISC-V "A"
  extension.  Downstream modules do not have to support AXI atomic transactions or exclusive
  memory accesses.

For each of those modules we additionally provide a wrapper (`_wrap` filename suffix) that exposes
SystemVerilog interfaces instead of `logic` ports.
