# Verilab SVLIB Vendor Library

The Verilab SVLIB http://www.verilab.com/resources/svlib/ is a SystemVerilog package that provides a host of convenient utilities for
testbench functionality that is not provided by UVM nor SystemVerilog itself conveniently.  These utilities include:

- Advanced string handling
- Regular expression parsing
- File pathname manipulation
- Environment variable queries
- Time functions

## Documentation

For more details on using the SVLIB, please refer to their documentation PDF.  This PDF can be found either on the Verilab website
or by cloning the Bitbucket SVLIB repository into vendor_lib (`make clone_svlib`) and finding the documenation under `svlib/doc`

## CORE-V_VERIF Compilation

The SVLIB will now be cloned and compiled into every core-v-verif simulation.  The source code is cloned from a checked-in hash
in Common.mk for the CV_CORE being simulated.  The Makefiles will compile this package into the simulation database automatically.
From any class or module simply address or import the svlib_pkg to access the SVLIB itself.

## Shared Library

SVLIB is partially implemented in C accessed via the DPI in SystemVerilog.  A checked-in shared object (compile to Linux 64-bit) will enable
out-of-the-box operation for most users.  However if one needs to recompile the SVLIB DPI this can be accomplished via the `svlib` make target.
Note that each CV_CORE has a separate SVLIB directory.  Refer to `mk/Common.mk` for more details on the actual compilation and creation of the
shared library and the variables provided to customize.


```
% make svlib CV_CORE=cv32e40x
```
