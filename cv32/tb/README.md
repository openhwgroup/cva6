## CV32/TB: testbenches for the CV32E40\* CORE-V family of OpenHW RSIC-V cores.
Each sub-directory has a specific purpose.  Note that some are expected to be
depricated in the near future.  Derived from the
[tb](https://github.com/pulp-platform/riscv/tree/master/tb)
directory of the PULP-Platform RI5CY project.

### core
Modified to remove a few RTL files (placed these in the rtl directory.  Makefile
has been substantially updated.

### dm
Unmodified.  The future of this directory is unknown.

### scripts
Unmodified.  The future of this directory is unknown.

### serDiv
Unmodified.  The future of this directory is unknown.

### tb_MPU
Unmodified.  The future of this directory is unknown.

### tb_riscv
Support models and functions for the `core` testbench.  While the future of this
directory is unknown, at least some of this will find its way into the UVM
environment (perhaps in a different form).   A good example of this is
`tb_riscv/riscv_perturbation.sv`.

### uvmt_cv32
**_New_**.  The testbench and testharness for the CV32E40\* UVM verification environments.
This tb/th maintains support for all features of the `core` testbench.

### verilator-model
Unmodified.  There is no reason to remove this, but keep in mind that some of
the capabilties of the testbench in the `core` directory are not supported by
Verilator and are `\`ifdef'ed` out.  Verilator does not support the UVM
environment at all.  Given that, maintenance of Verilator is a low priority for
this project and Issues submitted for Verilator support will be a low priorty.

