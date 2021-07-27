# Changelog
All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](http://keepachangelog.com/en/1.0.0/)
and this project adheres to [Semantic Versioning](http://semver.org/spec/v2.0.0.html).

## Unreleased

## v0.2.0 - 2019-08-20

### Added
- Add module to timeout simulations.

### Changed
- Remove `timeunit` and `timeprecision` declarations from all modules.  Multiple simulators do not
  properly implement precedence of these declarations (IEEE 1800-2012, 3.14.2.3), so we now avoid
  the declarations in favor of a simulation-wide precision declaration.
- Rename parameters to comply with style guidelines.

## v0.1.2 - 2019-08-20

### Fixed
- rand_synch_driver: Fix instantiation of `rand_synch_holdable_driver`.
- rand_stream_slv: Fix instantiation of `rand_sync_driver`.

## v0.1.1 - 2019-02-26

### Fixed
- Move all files into the `simulation` target. This precludes synthesis of files in this package
  when this package is included as dependency.

## v0.1.0 - 2019-02-25

### Added
- Add standalone clock and reset generator.
- Add randomizing synchronous driver and holdable driver.
- Add randomizing stream master and slave.
- Add ID queue with randomizing output.
- Add `rand_verif_pkg` with task to wait for a random number (within interval) of clock cycles.
