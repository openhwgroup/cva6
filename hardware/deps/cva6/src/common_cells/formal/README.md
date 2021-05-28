# Formal Verification Properties
These formal properties (`*_properties.sv`) and scripts (`*.sby`) are used for
formal verification of `common_cells` IPs and are meant to be used with
`SymbiYosys`.

## Note on Tools
Make sure you have the commercial `Yosys` and `SymbiYosys`version installed and
in your path or point the `YOSYS` and `SBY` variable to it. We have tested it
with the Symbiotic EDA Edition [20190105A]. Note that the FOSS version won't
work because its SystemVerilog parser does not support all the required
features.

## Usage
Call `make all` to run all tests.

