# Contribution Guidelines

## Coding Style

All SystemVerilog code in this repository _must_ adhere to the [SystemVerilog Coding Style Guide by
lowRISC](https://github.com/lowRISC/style-guides/blob/master/VerilogCodingStyle.md) and the
following rules:

- All module names _must_ start with `axi_`.

- User-facing modules _must_ have SystemVerilog `struct`s as AXI ports.  The concrete `struct` type
  _must_ be defined as `parameter` to the module.  The fields of the `struct` _must_ correspond to
  those defined by our [`typedef`
  macros](https://github.com/pulp-platform/axi/blob/master/include/axi/typedef.svh).

- User-facing modules _may_ come with a variant that has SystemVerilog interfaces as AXI ports.
  - Such an interface variant module _must not_ implement any functionality except wiring its
    interfaces to the `struct` ports of the original module.
  - The name of an interface variant _must_ be the name of the original module suffixed by `_intf`.
  - The parameters of an interface variant must be formatted `ALL_CAPS`.


## Collaboration Guidelines

We follow [`pulp-platform`'s Collaboration
Guidelines](https://github.com/pulp-platform/style-guidelines/blob/master/CONTRIBUTING.md).
