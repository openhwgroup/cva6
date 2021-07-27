# Changelog
All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](http://keepachangelog.com/en/1.0.0/)
and this project adheres to [Semantic Versioning](http://semver.org/spec/v2.0.0.html).

## Unreleased

## 1.1.1 - 2018-09-07
- Point dependencies to open-source repos

## 1.1.0 - 2018-09-07
### Added
- Add `axi` dependency.

### Changed
- Make `axi_DW_allocator` and `axi_address_decoder_DW` compliant with new FIFO interface in common_cells.
- Remove defines and switch to `axi_pkg`.
- Switch to common interface for wrappers, slices from `axi` repository.

## 1.0.4 - 2018-09-06
### Changed
- Change common cells source URL and minimum version requirement to 1.7.3.

### Fixed
- Prevent reading from empty FIFO in `axi_address_decoder_DW.sv`.

## 1.0.3 - 2018-03-06
### Changed
- Adopt to real generic FIFO.
- Replace non-ASCII characters in headers.
- Rename `axi_node_wrap.sv` to `axi_node_intf_wrap.sv` in accordance with module name.

## 1.0.2 - 2018-03-06
### Added
- Benderize (add Bender.yml file).

## 1.0.1 - 2018-03-06
### Changed
- Bugfixes for 64-bit support on address line.

## 1.0.0 - 2018-03-06
### Changed
- Open source release.

### Added
- Initial commit.
