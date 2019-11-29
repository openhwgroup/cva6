RI5CY Verilator Model
=====================

The Verilator model of RI5CY instantiates the RI5CY core along with a RAM. A
testbench accompanies the model, to demonstrate the use of the Verilated model.

If you are interested in running `riscv-tests` and `riscv-compliance` consider
using the `core` testbench which also supports verilator.

Building the model
------------------

In order to build the model, you will require a recent version of Verilator
(3.906 or above), and that version of verilator must be known to pkg-config.

Run `make` in the `verilator-model` directory to build the model.

The Testbench
-------------

The testbench demonstrates:

- Instantiating the model
- Writing data to memory a short program (write 0xFFF_FFFF in all 31 GPR): Execution begins at 0x80
- Writing debug data to memory: Base address = 0x0a0000;
- Resetting the CPU
- Running the CPU
- Using the debug unit to:
  - Resume
  - Going (TODO)
  - Breakpoint (TODO)
  - Single-Step (TODO)

The testbench can be executed as `./testbench`. The expected output of the
testbench is:

```
```
