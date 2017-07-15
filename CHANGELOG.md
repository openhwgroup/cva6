# Changelog
All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](http://keepachangelog.com/en/1.0.0/)
and this project adheres to [Semantic Versioning](http://semver.org/spec/v2.0.0.html).

## [Unreleased]

## 0.3.0
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

[Unreleased]: https://iis-git.ee.ethz.ch/floce/ariane/compare/v0.3.0...HEAD
[0.2.0]: https://iis-git.ee.ethz.ch/floce/ariane/compare/v0.2.0...v0.3.0
[0.1.0]: https://iis-git.ee.ethz.ch/floce/ariane/compare/v0.1.0...v0.2.0
