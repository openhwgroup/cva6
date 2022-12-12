# Changelog
All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](http://keepachangelog.com/en/1.0.0/)
and this project adheres to [Semantic Versioning](http://semver.org/spec/v2.0.0.html).

## Unreleased

## 0.2.9 - 2022-03-17
### Changed
- Added optional `IS_FUNCTIONAL` flag to `tc_clk_gating` cell to optionally mark them as *not required for functionality*.

## 0.2.8
*Skipped*

## 0.2.7
*Skipped*

## 0.2.6 - 2021-10-04
### Added
- Add `pad_functional_xilinx

### Fixed
- Bender targets

### Removed
- Deprecated xilinx `clk_cell`s replaced by wrappers

## 0.2.5
*Skipped*

## 0.2.4 - 2021-02-04
- Add `deprecated/pulp_clk_cells_xilinx.sv` to `Bender.yml`

## 0.2.3 - 2021-01-28
### Fixed
- `tc_sram_xilinx`: Remove unsupported `string` type from `SimInit` parameter.
- `IPApproX:` Add `tc_sram` to `src_files.yml` for proper compilation with IPApproX

## 0.2.2 - 2020-11-11
### Fixed
- `Bender:` Add deprecated `pulp_clock_gating_async` for compatibility to `udma_core`.

## 0.2.1 - 2020-06-23
### Added
- `Bender:` Add `rtl/tc_sram` to target `rtl`, to prevent overwriting of target specific implementations.

### Fixed
- `tc_sram`: Drop string literal from parameter `SimInit` definition as synopsys throws an elaboration error.
- `tc_clk:tc_clk_delay`: Add Verilator and synthesis guards.

## 0.2.0 - 2020-03-18
### Added
- Add `tc_sram` and `tc_sram_xilinx`, with testbench for verifying technology specific implementations.

## 0.1.6 - 2019-11-18
### Added
- Add Readme
- Add Contribution Guide

### Changed
- Move modules of similar topic to a single file. This makes it easier to add new modules.
- Move separation between `cluster` and `pulp` to `deprecated` folder. There should be a single solution to a tech-cell.

## 0.1.1 - 2018-09-12
### Changed
- Polish release
- Keep Changelog
- Move to sources subfolder

## 0.1.0 - 2018-09-12
### Added
- Initial commit.
