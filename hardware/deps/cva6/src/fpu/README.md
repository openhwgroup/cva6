# FPnew - New Floating-Point Unit with Transprecision Capabilities

Parametric floating-point unit with support for standard RISC-V formats and operations as well as transprecision formats, written in SystemVerilog.

Maintainer: Stefan Mach <smach@iis.ee.ethz.ch>

## Features

The FPU is a parametric design that allows generating FP hardware units for various use cases.
Even though mainly designed for use in RISC-V processors, the FPU or its sub-blocks can easily be utilized in other environments.
Our design aims to be compliant with IEEE 754-2008 and provides the following features:

### Formats
Any IEEE 754-2008 style binary floating-point format can be supported, including single-, double-, quad- and half-precision (`binary32`, `binary64`, `binary128`, `binary16`).
Formats can be defined with arbitrary number of exponent and mantissa bits through parameters and are always symmetrically biased.
Multiple FP formats can be supported concurrently, and the number of formats supported is not limited.

Multiple integer formats with arbitrary number of bits (as source or destionation of conversions) can also be defined.

### Operations
- Addition/Subtraction
- Multiplication
- Fused multiply-add in four flavours (`fmadd`, `fmsub`, `fnmadd`, `fnmsub`)
- Division<sup>1</sup>
- Square root<sup>1</sup>
- Minimum/Maximum<sup>2</sup>
- Comparisons
- Sign-Injections (`copy`, `abs`, `negate`, `copySign` etc.)
- Conversions among all supported FP formats
- Conversions between FP formats and integers (signed & unsigned) and vice versa
- Classification

Multi-format FMA operations (i.e. multiplication in one format, accumulation in another) are optionally supported.

Optionally, *packed-SIMD* versions of all the above operations can be generated for formats narrower than the FPU datapath width.
E.g.: Support for double-precision (64bit) operations and two simultaneous single-precision (32bit) operations.

It is also possible to generate only a subset of operations if e.g. divisions are not needed.

<sup>1</sup>Some compliance issues with IEEE 754-2008 are currently known to exist<br>
<sup>2</sup>Implementing IEEE 754-201x `minimumNumber` and `maximumNumber`, respectively

### Rounding modes
All IEEE 754-2008 rounding modes are supported, namely
- `roundTiesToEven`
- `roundTiesToAway`
- `roundTowardPositive`
- `roundTowardNegative`
- `roundTowardZero`

### Status Flags
All IEEE 754-2008 status flags are supported, namely
- Invalid operation (`NV`)
- Division by zero (`DZ`)
- Overflow (`OF`)
- Underflow (`UF`)
- Inexact (`NX`)

## Getting Started

### Dependencies

FPnew currently depends on the following:
- `lzc` and `rr_arb_tree` from the `common_cells` repository (https://github.com/pulp-platform/common_cells.git)
- optional: Divider and square-root unit from the `fpu-div-sqrt-mvp` repository (https://github.com/pulp-platform/fpu_div_sqrt_mvp.git)

These two repositories are included in the source code directory as git submodules, use
```bash
git submodule update --init --recursive
```
if you want to load these dependencies there.

Consider using [Bender](https://github.com/fabianschuiki/bender.git) for managing dependencies in your projects. FPnew comes with Bender support!

### Usage

The top-level module of the FPU is called `fpnew_top` and can be directly instantiated in your design.
Make sure you compile the package `fpnew_pkg` ahead of any files making references to types, parameters or functions defined there.

It is discouraged to `import` all of `fpnew_pkg` into your source files. Instead, explicitly scope references into the package like so: `fpnew_pkg::foo`.

#### Example Instantiation

```SystemVerilog
// FPU instance
fpnew_top #(
  .Features       ( fpnew_pkg::RV64D          ),
  .Implementation ( fpnew_pkg::DEFAULT_NOREGS ),
  .TagType        ( logic                     )
) i_fpnew_top (
  .clk_i,
  .rst_ni,
  .operands_i,
  .rnd_mode_i,
  .op_i,
  .op_mod_i,
  .src_fmt_i,
  .dst_fmt_i,
  .int_fmt_i,
  .vectorial_op_i,
  .tag_i,
  .in_valid_i,
  .in_ready_o,
  .flush_i,
  .result_o,
  .status_o,
  .tag_o,
  .out_valid_o,
  .out_ready_i,
  .busy_o
);
```

### Documentation

More in-depth documentation on the FPnew configuration, interfaces and architecture is provided in [`docs/README.md`](docs/README.md).

### Issues and Contributing

In case you find any issues with FPnew that have not been reported yet, don't hesitate to open a new [issue](https://github.com/pulp-platform/fpnew/issues) here on Github.
Please, don't use the issue tracker for support questions.
Instead, consider contacting the maintainers or consulting the [PULP forums](https://pulp-platform.org/community/index.php).

In case you would like to contribute to the project, please refer to the contributing guidelines in [`docs/CONTRIBUTING.md`](docs/CONTRIBUTING.md) before opening a pull request.


### Repository Structure

HDL source code can be found in the `src` directory while documentation is located in `docs`.
A changelog is kept at [`docs/CHANGELOG.md`](docs/CHANGELOG.md).

This repository loosely follows the [GitFlow](https://nvie.com/posts/a-successful-git-branching-model/) branching model.
This means that the `master` branch is considered stable and used to publish releases of the FPU while the `develop` branch contains features and bugfixes that have not yet been properly released.

Furthermore, this repository tries to adhere to [SemVer](https://semver.org/), as outlined in the [changelog](docs/CHANGELOG.md).

## Licensing

FPnew is released under the *SolderPad Hardware License*, which is a permissive license based on Apache 2.0. Please refer to the [license file](LICENSE) for further information.

## Acknowledgement

This project has received funding from the European Union's Horizon 2020 research and innovation programme under grant agreement No 732631.

For further information, visit [oprecomp.eu](http://oprecomp.eu).

![OPRECOMP](docs/fig/oprecomp_logo_inline1.png)
