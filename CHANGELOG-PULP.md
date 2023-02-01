# Changelog
All notable changes to the `pulp` branch of this project will be documented in this file.

The format is based on [Keep a Changelog](http://keepachangelog.com/en/1.0.0/)
and this project adheres to [Semantic Versioning](http://semver.org/spec/v2.0.0.html).

## pulp-v2.0.0 - 2025-07-17
### Added
- vCLIC support

### Changed
- Rebase onto openhwgroup:cva6:master#2d411b2d (2025-02-20)
- Apply upstream patches adding superscalar configuration options
- Add HPDCache wrappers
- FPU: Upgrade to pulp-v0.2.3
- fence.t: Support 32-bit XLEN

### Fixed
- Apply upstream bugfixes mostly regarding H extension
- CLIC WFI resume condition and trap vector base

## pulp-v1.0.0 - 2024-02-25
### Changed
- Rebase onto openhwgroup:cva6:master#68f952b4 (2024-02-23)

## pulp-v0.4.3 - 2023-08-12
### Changed
- `tech_cells_generic`: Bump v0.2.12

## pulp-v0.4.2 - 2023-08-11
### Changed
- frontend: Do not speculate beyond xret to avoid spurious icache refills
- coherence: Pack Valid/Dirty SRAM

## pulp-v0.4.1 - 2023-08-03
### Fixed
- CLIC controller: Fix inferred latch

## pulp-v0.4.0 - 2023-07-25
### Added
- Self-invalidation coherence

### Changed
- Upgrade CLIC to v2.0.0
- Upgrade AXI RISC-V AMO adapter to v0.8.0

### Fixed
- Fix CLIC interrupt behaviour

## pulp-v0.3.1 - 2023-05-10
### Changed
- Upgrade FPU to pulp-v0.1.1

### Fixed
- Bender.yml: Fix file list for target cv64a6_imafdcsclic_sv39
- cva6_icache_axi_wrapper: Fix negative repetition multiplier for paddr width > AxiAddrWidth
- cva6_clic_controller: Resolve inferred latch by adding default case
- Bender.lock: Update

## pulp-v0.3.0 - 2023-05-03
### Added
- Initial Hypervisor extension (incl. regression tests)

### Changed
- Upgrade AXI to v0.39.0-beta.2

## pulp-v0.2.2 - 2023-04-27
### Fixed
- `Bender.yml`: Specify version for tech_cells_generic
- `Makefile`: Fix vopt for recent questasim versions

## pulp-v0.2.1 - 2023-04-17
### Fixed
- `Bender.yml`: Add cv64a6_imafdcsclic_sv39 target

## pulp-v0.2.0 - 2023-04-08
### Added
- CLIC support

### Fixed
- Verilator 5 compatibility
- `Bender.yml`: Update paths
- Minor tool compatibility issues

## pulp-v0.1.1 - 2023-03-25
### Fixed
- Typo in `Bender.yml`

## pulp-v0.1.0 - 2023-03-24
### Added
- `fence.t` instruction to support timing channel prevention

### Changed
- Bumped `master`
- Updated `Bender.yml`

### Fixed
- Questasim flow
- `icache_axi_wrapper`: Signal widths
