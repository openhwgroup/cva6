# Changelog

This project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [3.18.1] - 2024-04-10
  - mprv should not be implemented when U mode is absent.

## [3.18.0] - 2024-04-02
  - mabi generation to account for E extension

## [3.17.1] - 2024-02-25
  - add unratified Ssdbltrp, Smdbltrp, and Sddbltrp extensions

## [3.17.0] - 2024-01-09
  - support march generation without custom extensions

## [3.16.0] - 2024-01-03
  - use the "hartX" naming for the merged dict
  - improve logging statements
  - update the "fields" node of each csr in the normalized custom yaml

## [3.15.0] - 2024-01-01
  - Added function that returns the march and mabi for gcc from a given ISA
  
## [3.14.3] - 2023-12-01
  - Add support for Zimop extension

## [3.14.2] - 2023-12-01
  - Add Zcmop extension.

## [3.14.1] - 2023-12-01
  - Add support for Zicfilp and Zicfiss extensions

## [3.14.0] - 2023-11-30
  - Include Sdext in the list of S extensions

## [3.13.4] - 2023-10-30
  - Add support for Zabha extension

## [3.13.3] - 2023-09-23
  - do not assign subfield to None

## [3.13.2] - 2023-09-20
  - Perform satp checks only when the CSR is accessible.

## [3.13.1] - 2023-08-21
  - Add support for Code Size Reduction (Zce) extension

## [3.13.0] - 2023-08-14
  - Fixed issue #110
  - Fixed issue #108
  - Fixed issue #114
  - Fixed issue #127
  - Fixed issue #82
  - Fixed issue #103
  - updated contribution guidelines on versioning
  - added docs for indexed CSRs

## [3.12.0] - 2023-08-12
  - Add support for Svadu extension

## [3.11.0] - 2023-08-12
  - Add support for Zacas extension

## [3.10.0] - 2023-08-12
  - Add support for Zfa extension

## [3.9.2] - 2023-07-21
  - Fix Checks for FCSR, FFLAGS and FRM to depend on F instead of U.

## [3.9.1] - 2023-06-21
  - Check if YAMLs are None before they're merged for performing CSR checks.
  - Perform XLEN specific satp checks based on XLEN value.
  - Check triggers only when debug CSRs are available.

## [3.9.0] - 2023-05-06
  - Add support to include hidden uarch dependencies in YAML definitions of CSRs.
  - Perform checks on all CSRs together instead of handling each spec seperately.
  - Add a schema for custom CSR specification. Add a node for listing uarch signals.

## [3.8.1] - 2023-04-25
  - fix the address for mnstatus

## [3.8.0] - 2023-04-18
  - Add support for Srnmi extension
  - All extension existence checks to be performed on extension\_list from isa validator.

## [3.7.2] - 2023-04-06
  - Add support for Zicond extension

## [3.7.1] - 2023-03-14
  - change all hpmcounters to be read-only shadows of the corresponding machine mode mhpmcounters.

## [3.7.0] - 2023-03-13
  - adding Zicntr and Zihpm extensions

## [3.6.0] - 2023-03-07
  - add V extensions ISA string constraints check

## [3.5.2] - 2022-12-26
  - special checks for vxsat csr added which apply only the max-xlen subsections of the csr

## [3.5.1] - 2022-12-12
  - Added Zbpbo, Zpn, Zpsfoperand into constants.py
  - Added ISA string legality checker for Zp* extension into isa_validator.py
  - Added vxsat CSR into schema_isa.yaml (Credits: chuanhua)

## [3.5.0] - 2022-10-28
  - Add support for indexed registers
  - Add schemas for triggers
  - Fix bugs in WARL class
  - Add function to get a legal value from WARL fields.

## [3.4.0] - 2022-10-13
  - support x-extension parsing in ISA string
  - added check to capture duplicates in the extensions present in the isa string

## [3.3.1] - 2022-09-26
  - documentation cleanup for adding new extensions in riscv-config
  - disabled pdf asset generation for each release.

## [3.3.0] - 2022-09-24
  - rewrote regular expression for determining legal ISA/extension strings to fix bugs and simplify maintenance. (#104)
  - updated example and regex in new-extensions.rst to match

## [3.2.0] - 2022-09-07
  - adding new function to get a legal value from a warl node

## [3.1.2] - 2022-08-23
  - if the value being tested is out of bounds, then skip with error immediately

## [3.1.1] - 2022-08-18
  - fix pypi dependencies for docs

## [3.1.0] - 2022-08-17
  
  - scounteren can be a ro\_constant now
  - the maxval checks for mask/fixedval should be based on the length of the part
  - adding support for mtval\_update field
  - adding support for pte\_ad\_hw\_update field
  - cleaned up documentation

## [3.0.0] - 2022-08-16

  - created new warl class for warl node handling

    - better comments
    - more functions to keep things simple
    - fixed a lot of bugs in checking legal values
    - bitmask and range values can now co-exist in a legal string
    - added new and improved checks for syntax validity of warl strings

  - fixed validationError function to correctly print all errors (dict and/or list)
  - removed wr\_illegal checks from the schema since they are now done as part of the new warl class
    checks
  - updates to the new warl checks and reset-value checks
  - satp.mode should have one of sv\* translation schemes as a legal value. (#89)
  - default setters for pmps fixed
  - pmp checks have been improved (#88)
  - improve WARL documentation

## [2.17.0] - 2022-08-08

  - Support for Zfinx, Zdinx, Zfh, Zhinx, Zhinxmin in ISA string added.

## [2.16.1] - 2022-07-21

  - fixed bug in regex where Zk and Zknh were missing an underscore

## [2.16.0] - 2022-07-20

  - fixed overlap checks for crypto extensions
  - removing K and P extension strings from regex

## [2.15.1] - 2022-06-18

  - added missing Z extensions from Kcrypto
  - fixed ordering of the Z extensions as per isa spec.

## [2.15.0] - 2022-06-16
  
  - moved ISA validation as a separate api function to enable import in other python tools

## [2.14.1] - 2022-06-02

  - add support for Zicbo* extensions
  - add new node in platform_schema: zicbo_cache_block_sz

## [2.14.0] - 2022-05-13

  - fix for index-based dependency checks in warl string.

## [2.13.1] - 2022-03-23

  - Added setup.cfg to automate bumpversion
  - Fix wording for legal strings in dependency warl fields.

## [2.13.0] - 2022-03-09
  - add support for detection of svnapot in ISA string
  - genralize conversion of hex, oct, bin values to int in warl functions
  - machine flat schema to include wlrl types as well

## [2.12.1] - 2021-12-18
### Fixed

  - added mbe and sbe fields in mstatush
  - fixed default setter for vsstatus in RV32 mode

## [2.12.0] - 2021-12-10

### Added
  
  - support for hypervisor csrs
  - change default for dcsr.v and fix the `check_with` function for the same
  - ensures proper checks for csrs defined as 32-bit only registers

## [2.11.2] - 2021-11-29

### Fixed

  - Fixed the relationship between fflags, frm and fcsr
  - Enable subfield to be shadow field of whole csr, and vice versa

## [2.11.1] - 2021-11-19

### Added

- adding the missing shadow_type field for hpmcounter17

## [2.11.0] - 2021-10-15
### Fixed
  - canonical ordering requirement of `_Z` extensions fixed
### Added
  - adding support for Zmmul extension in ISA regex

## [2.10.2] - 2021-10-06
### Fixed
  - islegal function under the warl_interpreter class fixed. The based and bound values are not
     extracted correctly as either hex or decimal values. Also removed the logic to truncate values

## [2.10.1] - 2021-08-26
### Fixed
   - Changed the default value of 'accessible' to false so input yamls need not declare unsupported xlen


## [2.10.0] - 2021-07-30
### Added
   - added default-setters for misa's reset value to match the ISA extensions, to modify warl function of extensions under misa
   - added default setter for reset value of mstatus
### Fixed
   - changed default values of types for subfields in mstatus 
   - changed default values of types for mhpmevent*, mcountinhibit, mcounteren and mhpmcounter* to read only constant 0
   - changed default values of types for fflags, frm and fcsr to warl if F is present, else read-only constant 0
   - changed default values of types for mcycle[h], minstret[h] to  warl
   - changed default values of types and added checks for subfields of scause, satp, stvec, sie, sip and sstatus

## [2.9.1] - 2021-06-02
### Fixed
- removed an unadded feature in rv32i_platform.yaml
- removed debug_interrupts under mip in rv64i_isa.yaml

## [2.9.0] - 2021-05-24
### Fixed
- fixed issue #58 by adding extra checks for bitmask
- fixed issue #59 by removing custom cause from platform yaml
- resolved inconsistencies in the use of "xlen" and "supported_xlen" in schemaValidator
### Added
- added extra "shadow_type" fields in the csr schemas. These indicate the nature of shadow
  (read-only, read-write, etc).
- added parking_loop node in debug_schema to indicate the address of debug rom. Can be empty in
  implementations which do not have this feature

## [2.8.0] - 2021-03-02
### Added
- Added checks for K (sub)extension(s) 
- Updated docs with information on adding new extension, csrs or specs.
- Added github actions based CI

## [2.7.0] - 2021-02-25
### Added
- added new debug schema for debug based csrs and spec
- cli now takes debug spec as input as well along with isa-spec
- added support for defining custom exceptions and interrupts

## [2.6.3] - 2021-01-19
### Fixed
- added priv_mode field to sedeleg and sideleg csrs

## [2.6.2] - 2021-01-18
### Fixed
- Allow B extension in ISA schema

## [2.6.1] - 2021-01-13
### Fixed
- msb,lsb values of "SD" field in mstatus must be 63 in rv64 mode
- added checks for reset value of misa to adhere to the extensions enabled in the input yaml
- fixed dead-link in the docs.

## [2.6.0] - 2021-01-5
### Added
- Added support for custom csr yaml
- Added new nodes in isa_schema: pmp_granularity and physical_addr_sz
- Checks for pmp, counters and custom csrs
- medeleg, mideleg check for S or N extension
- updated the warl syntax slightly for easier parsing.

### Changed
- fixed warl parsing and islegal function to check reset values 

## [2.5.1] - 2020-11-6
### Changed
- modified sn_check and su_check
- scounteren checks to make it depend only on u
- medeleg, mideleg check for S or N extension


## [2.5.0] - 2020-11-6
### Added
- added all n extension csrs
- added missing supervisor csrs
- added default setters for subfields in sip, sie , uip and uie to make it depend as shadows on machine csrs

## [2.4.1] - 2020-10-22
### Changed
- default mpp value to 0
- adding defaults to sub-fields of mtvec

## [2.4.0] - 2020-10-19
### Added
- Added support for pmp csrs in the schema
- Added support for mcycleh and minstreth
- Added special checks for ensuring the shadows are implemented correctly.
- Added support for the following supervisor csrs in the schema: sstatus, sie, sip, stvec, sepc, stval, scause and satp
- Added support for user performance counters, frm, fcsr, time[h], cycle[h] and instret[h] csrs in
  the schema.
### Changed
- all fields are now subsumed under a hartid. This allows specifying multiple harts in the same
  yaml
- logging mechanism improved.
- isa spec is now validated independently of the platform spec
- privilege and unprivilege version checks are no longer required. This satisfied via the
  "allowed" field now.
- improved the 'implemented/accessible' checks for s, u and n extensions
- the "fields" node is now populated by subfields in the increasing order of the placement in the
  csr.
- using aliases to reduce the code size

## [2.3.1] - 2020-10-6
### Changed
- Added Zihintpause to ISA string (for PAUSE Hint instruction extension)..

## [2.3.0] - 2020-07-27
### Changed
- Size of the isa schema has been reduced significantly.
- Using anchors in the schema.
- Provided a command line argument to disable anchors in the checked yaml dump.
- adding mycycle, minstret, pmpcfgs and pmpaddrs
- added support for defining multiple harts

## [2.2.2] - 2020-06-09
### Changed
- Changed quickstart 'riscv_config' to 'riscv-config'
- Changed checker.py to add check_reset_fill_fields() description

## [2.2.1] - 2020-05-18
### Changed
- Changed minimum python version requirement to 3.6.0 which is typically easy to install on all
  major distributions
- Updated readme with better installation instructions

## [2.2.0] - 2020-04-07
### Changed
- Renamed the 'implemented' field  in rv32 and rv64 nodes to 'accessible'.
- Modified appropriate definitions for fields dependent on specific extensions like NSU.

## [2.1.1] - 2020-03-29
## [Fixed
- doc issue for mtimecmp
- mimpid is now part of the default setters list

## [2.1.0] - 2020-03-29
## [Fixed
- Moved machine timer nodes to platform yaml.
## [Added
- `--version` option to arguments to print version and exit when specified.
- Print help and exit when no options/arguments are specified.

## [2.0.2] - 2020-03-28
### Fixed
- Redundant reset-val check for mtvec and misa registers.

## [2.0.1] - 2020-03-25
### Fixed
- typos in quickstart doc
- disabled deployment to repository until authentication issue is fixed.

## [2.0.0] - 2020-03-25
### Added
- adding support for warl fields and support
- documentation for the warl fields added
- reset-value checks added
### Changed
- using a new common template for defining all csrs
- updated docs with new template
- using special function within conf.py to extract comments from yaml file as docs.
### Fixed
- closed issues #10, #11, #12, #13

## [1.0.2] - 2019-08-09
### Changed
- Log is generated only if specified(for API calls to checker.check_specs).
### Fixed
- link in readme now points to github instead of gitlab.

## [1.0.0] - 2019-07-30
### Changed
- Work directory isnt deleted if the directory exists, although the files of the same name will be overwritten.
### Fixed
- Checked yaml passes validation too.

## [0.1.0] - 2019-07-29
### Added
- Added work_dir as arg and always outputs to that dir.
- Added reset vector and nmi vector to platform.yaml
- Vendor description fields in schema.
- An xlen field added for internal use.
### Fixed
- In ISA field in isa_specs subsequent 'Z' extensions should be prefixed by an underscore '_'
- Fixed `cerberus.validator.DocumentError: document is missing` error when platform specs is empty. 
- mtvec:mode max value is set to 1.
- privilege-spec and user-spec are taken as strings instead of float.
### Changed
- The representation of the int fields is preserved in the checked-yaml.
- mepc is a required field.
- check_specs function now returns the paths to the dumped normalized files.
- No other entries in node where implemented is False.
- Readonly fields are purged by default.
- Multiple values/entries for the same node is not allowed.
### Removed
- remove *_checked.yaml files from Examples.
- changed templates_platform.yaml to template_platform.yaml in docs.

## [0.0.3] - 2019-07-19
### Fixed
- doc update

## [0.0.2] - 2019-07-19
### Fixed
- pdf documentation
- ci-cd to host pdf as well

## [0.0.1] - 2019-07-18
### Added
- Documentation to install and use pyenv 

## [0.0.0] - 2019-07-18
### Added
- Initial schemas for M mode and S mode csrs with constraints as specified in the spec.
