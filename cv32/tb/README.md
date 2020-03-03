## CV32/TB: testbenches for the CV32E40\* CORE-V family of RISC-V cores.
Derived from the
[tb](https://github.com/pulp-platform/riscv/tree/master/tb)
directory of the PULP-Platform RI5CY project.

### core
Modified to remove a few RTL files (placed these in the rtl directory). This
testbench supports Verilator and we will do what we can to maintain Verilator
support here.

### dm
Unmodified.  Future plans for this are to integrate it into the uvmt_cv32
environment, and perhaps the core testbench.

### scripts
Unmodified.  The future of this directory is unknown.

### serDiv
Unmodified.  The future of this directory is unknown.

### tb_MPU
Unmodified.  The future of this directory is unknown.

### tb_riscv
Support models and functions for the `core` testbench.  While the future of
this directory is unknown, at least some of this will find its way into the
`uvmt_cv32` UVM environment (perhaps in a different form).   A good example
of this is `tb_riscv/riscv_perturbation.sv`.

### uvmt_cv32
**_New_**.  The testbench and testharness for the CV32E40\* UVM verification
environments.  This tb/th maintains support for all features of the `core`
testbench. Cannot be run with Verilator.

### verilator-model
DO NOT USE.  The Makefile has been renamed to make it obvious that this
directory is no longer maintained and should not be used.  There is no reason
to remove this, but it does not provide anything that you cannot find in `core`.
