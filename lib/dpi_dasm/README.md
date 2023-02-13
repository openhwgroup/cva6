`dpi_dasm` is a library for disassembling/decoding instruction binaries.

It uses some of the source files from
[spike](https://github.com/riscv/riscv-isa-sim) in order to obtain instruction
fields and instruction name
(see [decode.h](https://github.com/riscv-software-src/riscv-isa-sim/blob/master/riscv/decode.h) ).
Via a DPI interface, these C/C++ functions are exposed as SystemVerilog
functions.
This library is compiled into an `.so` file before being included in simulation.
A 64-bit Linux shared library is included in
`core-v-verif/lib/dpi_dsam/lib/Linux64/libdpi.dasm.so` that should
link with all SystemVerilog simulators.

If the shared library needs to be rebuilt, a make target `dpi_dasm` is provided
in the common Makefiles.
It will overwrite the shared library location above.
Note that a simulator should be provided to locate DPI header files (any
simulator should suffice).

`% make dpi_dasm SIMULATOR=xrun`
