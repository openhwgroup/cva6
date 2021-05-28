# Change Log

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](http://keepachangelog.com/), and this project adheres to
[Semantic Versioning](http://semver.org).

## [Unreleased]

- Switch default implementation from ALTERA to XILINX
- Add simulation init options to inferable rams (none, 0, random, deadbeef)

### Added

### Fixed

## [v0.3.2] - 2018-07-24

### Updated

- This package has been moved from the internal GitLab to GitHub.  The Changelog and the affected
  Read-Mes and scripts have been updated accordingly.

## [v0.3.1] - 2018-07-03

### Fixed

- `AxiToAxiLitePc`:
  - Fixed bug with multiple parallel transactions.  The AXI interface now only accepts a new request
    after the response from the previous transaction has been acknowledged.
  - Return `SLVERR` on burst requests.  This module does not support bursts and now consistently
    responds with a Slave Error on a burst request.

## [v0.3.0] - 2017-07-11

### Added

- Set of five inferable, synchronous BRAM-based memories:
  - `SyncDpRam` (dual-port)
  - `SyncSpRam` (single-port)
  - `SyncSpRamBeNx32` (single-port N x 32bit with byte-wise enable)
  - `SyncSpRamBeNx64` (single-port N x 64bit with byte-wise enable)
  - `SyncTpRam` (two-port)

## [v0.2.3] - 2017-07-11

### Fixed

- `src_files.yml`: added missing comma at the end of the `AxiToAxiLitePc` entry.

## [v0.2.2] - 2017-07-11

### Fixed

- URLs to the GitLab repository of this project now correctly point to
  `pulp-restricted/fpga-support` instead of the outdated `pulp-project/fpga-support`.

## [v0.2.1] - 2017-07-11

### Fixed

- `src_files.yml`: added the missing entry for `AxiToAxiLitePc`.

## [v0.2.0] - 2017-02-10

### Added

- `AxiToAxiLitePc`: a simple AXI to AXI Lite Protocol Converter.

### Fixed

- `BramDwc`: address registering.  The address can now be changed between clock edges and the output
  will still correspond to the address applied at the former clock edge.

- `BramDwc`: compatibility of interface port declarations with synthesis tools.  Interface ports are
  now explicitly declared either as `Master` or as `Slave`, so that synthesis tools will not infer
  `inout` connections.

## [v0.1.1] - 2017-02-10

### Fixed

- `BramDwc`: address registering.  The address can now be changed between clock edges and the output
  will still correspond to the address applied at the former clock edge.

- `BramDwc`: compatibility of interface port declarations with synthesis tools.  Interface ports are
  now explicitly declared either as `Master` or as `Slave`, so that synthesis tools will not infer
  `inout` connections.

## v0.1.0 - 2016-11-14

### Added

- Three Block RAM (BRAM)-related modules:
  - `BramPort`: the standard interface for Xilinx BRAMs,
  - `TdpBramArray`: an array of Xilinx True Dual-Port BRAM cells with a standard BRAM interface, and
  - `BramDwc`: a Data Width Converter from a narrow master BRAM controller to a wide slave BRAM
    (array).

- `BramLogger`: a logger that writes events to a `TdpBramArray`.

- `AxiBramLogger`: a logger to keep track of events on an AXI bus.  This module is build on
  `BramLogger`.

[Unreleased]: https://github.com/pulp-platform/fpga-support/compare/v0.3.2...HEAD
[v0.3.2]: https://github.com/pulp-platform/fpga-support/compare/v0.3.1...v0.3.2
[v0.3.1]: https://github.com/pulp-platform/fpga-support/compare/v0.3.0...v0.3.1
[v0.3.0]: https://github.com/pulp-platform/fpga-support/compare/v0.2.3...v0.3.0
[v0.2.3]: https://github.com/pulp-platform/fpga-support/compare/v0.2.2...v0.2.3
[v0.2.2]: https://github.com/pulp-platform/fpga-support/compare/v0.2.1...v0.2.2
[v0.2.1]: https://github.com/pulp-platform/fpga-support/compare/v0.2.0...v0.2.1
[v0.2.0]: https://github.com/pulp-platform/fpga-support/compare/v0.1.0...v0.2.0
[v0.1.1]: https://github.com/pulp-platform/fpga-support/compare/v0.1.0...v0.1.1
