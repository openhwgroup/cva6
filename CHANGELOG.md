# Changelog
All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](http://keepachangelog.com/en/1.0.0/)
and this project adheres to [Semantic Versioning](http://semver.org/spec/v2.0.0.html).

## [Unreleased]

### Added

### Changed

- Fix non-setable MEIE bit in MIE CSR

### 4.2.0 - 2019-06-04

### Added

- Check execute PMA on instruction frontend
- Add support for non-contiguous cacheable regions to the PMA checks
- Provision exponential backoff for AMO SC in L1 D$ miss handler

### Changed

- Several small fixes to get the code running on VCS
- Fix compressed instruction decoding in tracer
- Fix privilege bug in performance counters. The counters have always been accessible in user mode.
- Fix RISC-V PK simulation bug caused due to insufficient time to init the `a0` and `a1` registers via the bootrom
- Fix bug in `wt_axi_adapter` (only appeared when dcache lines were wider than icache lines)
- Fix potentially long timing path in `axi_lite_interface`
- Fix VCS elab warning in `load_store_unit`
- Replace PLIC with implementation from lowRISC
- Re-work interrupt and debug subsystem to associate requests during decode. This improves stability on for non-idempotent loads.
- Bump `fpnew` to `v0.5.5`
- Bump `axi` to `v0.7.0`
- Bump `common_cells` to `v1.13.1`
- Bump `riscv-dbg` to `v0.1`
- Improve FPU pipelining and timing around scoreboard
- Reworked the `axilite` to PLIC shim for OpenPiton+Ariane
- Remove `in` and `out` aliases for AXI interfaces
- Fix small issues with DC synthesis
- Fix wrong dirtying of `sd` flag in `mstatus`
- Synthesis fix for `Vivado 2018.3`
- Clean-up instruction front-end, small IPC improvement
- Move to Verilator `4.014`

### 4.1.2

- Update FPU headers (license)

### 4.1.1

### Changed

- Hotfix: add missing defines for OpenPiton cache system.

### 4.1.0

### Added

- Official support for floating point unit
- Added AXI-64bit adapter for write-through cache system
- Added AXI atomic ops and exclusive access support to write-through cache system
- Provision `riscv-isa-sim` tandem simulation
- Support for preloading

### Changed

- Rerouted the JTAG from PMOD to second channel of FTDI 2232 chip on Genesys 2 board
- Increase available RAM size on Genesys II board to 1 GiB
- Fixed problem which decoded compressed hints as illegal instructions
- Reduce clock frequency of FPGA to 30 MHz to accomodate FPU
- Bugfixes in write-through cache system
- ID width fix in random delayer

### 4.0.0

### Added

- Preliminary support for A-Extension
- Preliminary FP support
- Preliminary support for OpenPiton cache system
- Commit log feature
- Provisioned `aw_top` signal for close to memory atomics
- FPGA Support
- Misc bug-fixes
- Platform Level Interrupt Controller (PLIC)
- FPGA Bootrom with capability to boot from SD Card

### Changed

- core_id / cluster_id inputs have been merged to hard_id input (interface changes)
- The three AXI ports have been merged into one (interface changes)
- [Bugfix] Wrong flagging of memory in machine mode if high bits (63-38) are not equal #136

### 3.0.0

### Added

- Added RISC-V compliant debug (interface changes)
- Implemented basic re-naming

### Changed

- [Bugfix] Cache-refill AXI logic (AXI protocol violation)
- [Bugfix] `MSTATUS` write-able through `SSTATUS` #65
- [Bugfix] PTW has protocol violation #61
- [Bugfix] Race-condition #54
- Removed timer input. Access to mtime will trap and must be handled by M-mode SW.

### 2.0.2 - 2018-04-08

### Changed

- Bugfix in flush behaviour of cache #34
- Pumped submodules

### 2.0.1 - 2018-01-26

### Added

- Improved instruction fetch fronten-end
- Add RAS
- Add support for Bender hardware management

### Changed

- Bugfix in non-detected illegal instruction #12
- Bugfix in non-detected illegal instruction JALR (funct3 != 0)
- Bugfix in non-detected illegal instruction FENCE (some bit-checks missing)

### 2.0.0 - 2018-01-26

### Added

- Instruction cache added
- Support for Verilator

### Changed

- CI support for verilator
- Update documentation

### 1.0.0 - 2018-01-17

### Added

- Non-blocking data cache
- Two AXI interfaces on top level, one for bypassing and one for actual cache-able regions
- Performance Counters
- Hardware multiplication (full M-Extension)
- Support for inter processor interrupts (IPI)

### Changed

- Testbench: EOC component now listening on store interface only
- Store interfaces has been simplified by removing the `valid` signal, a transaction is now considered finished as soon as the dcache gives the grant signal.
- EOC and dcache checker has been reworked to get rid of absolute path in UVM testbench
- Fix problem when bypassing the data cache

### 0.4.0 - 2017-10-13

Linux booting on FPGA.

### Added
- Support for M Extension (mul, div and reminder) in simulation
- Preliminary debug support
- Added support for cache management instructions

### Changed
- Various bug fixes (branch-prediction, PTW and TLB problems, interrupt handling)
- Fixed synthesis issues

## [0.3.0] - 2017-07-15

### Added
- Added support for device tree in Ariane's testbench

### Changed
- Bugfixes in compressed decoder (legal shifts where throwing an illegal instruction although they where legal)
- Increase memory size to 16 MB in-order to simulate a full Linux boot
- Re-worked timer facilities in the CSR section, moved to a platform RTC
- Core completed its first full Linux boot
- Changelog design, adhering to a common [standard](http://keepachangelog.com/en/1.0.0/)

## [0.2.0] - 2017-06-28

### Added
- Virtual memory support according to RISC-V privilege specification 1.11 (WIP)
- Add support for Torture test framework

### Changed
- IPC improvements
- Timing improvements
- New fetch interface, smaller and ready for macro-op fusion and dual-issue

## [0.1.0] - 2017-06-21

### Added
- Initial development, getting to a stable point
