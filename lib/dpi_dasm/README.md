`dpi_dasm` is a library for disassembling/decoding instruction binaries.

It uses some of the source files from [spike](https://github.com/riscv/riscv-isa-sim)
in order to obtain instruction fields and instruction name.
Via a DPI interface, these C/C++ functions are exposed as SystemVerilog functions.
This library is compiled into an `.so` file before being included in simulation.

In order to use `dpi_dasm` (as needed by e.g. uvma_isacov coverage agent),
one must run `make dpi_dasm` before any `make comp` or `make test`.
TODO description should be in mk/uvmt/README.md when isacov is complete.
