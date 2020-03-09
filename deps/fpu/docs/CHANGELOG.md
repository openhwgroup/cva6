# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](http://keepachangelog.com/en/1.0.0/) and this project adheres to [Semantic Versioning](http://semver.org/spec/v2.0.0.html).

In this sense, we interpret the "Public API" of a hardware module as its port/parameter list.
Versions of the IP in the same major relase are "pin-compatible" with each other. Minor relases are permitted to add new parameters as long as their default bindings ensure backwards compatibility.


## [Unreleased]

### Added
### Changed
### Fixed


## [0.6.1] - 2019-07-10

### Fixed
- A bug where the div/sqrt unit could lose operations in flight

## [0.6.0] - 2019-07-04

### Changed
- Pipelines are generated in the datapath modules instead of separate instances

### Fixed
- Don't care assignments to structs have been expanded for better tool support [(#14)](https://github.com/pulp-platform/fpnew/pull/14)
- Undriven busy signal in output pipeline bypass
- Typo in the documentation about the multiply operation
- Generation of merged slices when the first package format is disabled
- Potential simulation/synthesis mismatch of the UF flag
- Various linter warnings
- Documentation to reflect on updated pipeline distribution order
- [fpu_div_sqrt_mvp] Bumped to fix linter warnings
- [Bender] Fixed dependencies for Bender [(#14)](https://github.com/pulp-platform/fpnew/pull/15)

### Removed
- Currently unused modules: `fpnew_pipe*`, `fpnew_{f2i,f2f,i2f}_cast`


## [0.5.6] - 2019-06-12

### Changed
- Don't care logic value can be changed from the package now
- Default pipeline config in the package is now `BEFORE`

### Fixed
- Don't care values are assigned `'1` instead of `'X` by default


## [0.5.5] - 2019-06-02

### Fixed
- UF flag handling according to IEEE754-2008 [(#11)](https://github.com/pulp-platform/fpnew/issues/11)


## [0.5.4] - 2019-06-02

### Added
- Documentation about multi-format operations
- Extended pipelining description slightly
- Extended semantic versioning declaration in changelog

### Changed
- Updated diagrams in architecture documentation

### Fixed
- [common_cells] Bumped to fix src_files.yml bugs
- [fpu_div_sqrt_mvp] Bumped to fix linter warnings


## [0.5.3] - 2019-05-31

### Fixed
- ips_list.yml entry for updated common_cells


## [0.5.2] - 2019-05-31

### Fixed
- Internal pipeline bypass in cast unit


## [0.5.1] - 2019-05-27

### Fixed
- Include path for `common_cells` in `src_files.yml`


## [0.5.0] - 2019-05-27

### Added
- The FPU :)
- Initial Documentation

### Changed
- "Restarted" the changelog as the old one was stale

### Fixed
- Handling of exception flags for infinity operands
