# Changelog
All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](http://keepachangelog.com/en/1.0.0/)
and this project adheres to [Semantic Versioning](http://semver.org/spec/v2.0.0.html).

## [Unreleased]

### Added

### Removed

### Changed

### Fixed

## [5.0.0] 2024-10-10

The major modification in this release is the support of the write-back (WB) policy (in
addition to the write-through (WT) policy). The cache can either implement one of these
policies or both in a per-cacheline basis.

### Added

- Support of the WB policy.
- Configuration parameters to choose between WT or WB, or both, at synthesis time.
- Validation testbench compatible to Verilator.
- Add a write-policy hint field in the request to select between WT and WB, dinamically.

### Removed

- WbufSendFeedThrough parameter removed

### Changed

- Arbitration between cacheable and uncacheable memory requests is done inside the
  HPDcache. The memory interface implements 5 channels, instead of 10.
- The CMO type is into the operation field of the request (instead of the size field).
- Select the victim cacheline at cache miss time (before was done on refill time). The
  slot is pre-allocated and written by the miss handler when the refill response arrives.

### Fixed

## [4.0.0] 2024-08-20

The major modification in this release is the new scheme to set parameters of the HPDcache

### Added

- Add utility macros to define the types in the interface of the HPDcache.
- Add scripts for code static check (lint)
- Add new User Guide document in reStructuredText format

### Removed

### Changed

- Pass configuration parameters through the top module of the HPDcache instead of
  defining them in a package. This allows different instances of the HPDcache to have
  different parameters.
- Add round-robin priority arbiter in the write-buffer to select an entry to send.
- Add fix-priority arbiter in the write-buffer to select a free entry.
- Make AXI transactions modifiable by default

### Fixed

- Fix some synthesis warnings

## [3.1.0] 2024-04-20

### Added

- Add support for pseudo-random (using a LFSR) algorithm for the victim selection
- Add support for the OpenPiton Cache-Coherent Network-on-Chip
- Add support for full-associative, direct-mapped or single-entry MSHR

### Removed

### Changed

- Cache directory valid bits are relocated in the Tag RAM
- Modify the arbitration between the different sources of requests (refill is now prioritary)
- Add feedthrough (optional) fifo in both wbuf and refill handler
- Disable assertions during reset
- Modify write buffer microarchitecture to improve both area and performance

### Fixed

- Fix support for AMOs when using a 32-bit request interface

## [3.0.0] 2023-10-08

### Added

- Add support for virtually-indexed addressing

### Fixed

- Fix forwarding logic of uncacheable Icache response in the cva6 cache subsystem.
- Fix wrong mask signal when implementing the MSHR in registers

## [2.1.0] - 2023-09-25

### Added

- Add additional configuration to implement MSHR in registers (when the number
  of entries is low)

### Fixed

- Fix cache data SRAM chip-select generation when word width is different than
  64 bits (e.g. 32 bits)

## [2.0.0] - 2023-09-18

### Added

- Add parameters in the HPDcache module to define the types of interfaces to
  the memory
- Add helper verilog header file with macros to ease the type definition of
  interfaces to the memory
- Add new event signals in the HPDCache top module
- Add generic single-port RAM macros with byte-enable signals
- Add parameters in the package to choose between RAM macros implementing
  byte-enable or bitmask for the different RAMs instances
- Add additional assertions to verify parameters
- Add additional configuration signal to inhibit write coalescing in the write
  buffer

### Removed

- Remove base_id ports in the HPDCache top module
- Remove nettype (wire,var) in ports as it looks like is badly supported in
  some cases by some simulation tools

### Changed

- Split the hpdcache_pkg into: (1) the hpdcache_pkg contains internally defined
  parameters; (2) a new hpdcache_params_pkg that defines user parameters
- New selection policy of ready requests in the replay table. It gives priority
  to requests in the same linked list.
- The write buffer now accepts writes from requesters in a pending slot when it
  is waiting for the internal arbiter to forward the data to the NoC.

### Fixed

- Correctly support HPDCACHE_ACCESS_WORDS=1
- Correctly support HPDCACHE_ACCESS_WORDS=HPDCACHE_CL_WORDS
- Fix width of the nlines count register in the HW memory prefetcher.

## [1.0.0] - 2023-02-22

### Added
- Initial release to the OpenHW Group
