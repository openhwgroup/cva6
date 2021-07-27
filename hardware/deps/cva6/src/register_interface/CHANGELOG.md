# Changelog
All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](http://keepachangelog.com/en/1.0.0/)
and this project adheres to [Semantic Versioning](http://semver.org/spec/v2.0.0.html).

## Unreleased

### Added
- AXI to reg interface
- Opensource release

## 0.1.3 - 2018-06-02
### Fixed
- Add `axi_lite_to_reg.sv` to list of source files.

## 0.1.2 - 2018-03-23
### Fixed
- Remove time unit from test package. Fixes delay annotation issues.

## 0.1.1 - 2018-03-23
### Fixed
- Add a clock port to the `REG_BUS` interface. This fixes the test driver.

## 0.1.0 - 2018-03-23
### Added
- Add register bus interfaces.
- Add uniform register.
- Add AXI-Lite to register bus adapter.
- Add test package with testbench utilities.
