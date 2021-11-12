## Toolchain Installation Instructions

### CORE-V Toolchain
The recommended toolchain for all CORE-V cores is available
[here](https://www.embecosm.com/resources/tool-chain-downloads/#corev).
It is recommended that you install this at /opt/corev, add it to your path and
create a shell variable COREV to YES:
```
$ export COREV_SW_TOOLCHAIN=/opt/corev
$ export COREV=1
```
Search for "Toolchain" in `../../mk/Common.mk` for guidance on how to get a custom
installation to work with the Makefiles.

### PULP Toolchain
The PULP toolchain is not supported on the CV32E40S as the PULP extensions are not supported.

### LLVM Toolchain
The core-v-verif testbench also supports usage of an LLVM/Clang toolchain.  An LLVM toolchain with RISCV32 support
built for various Linux binary platforms is available [here](https://www.embecosm.com/resources/tool-chain-downloads/#riscv-stable)

All tests and regressions should be buildable and runnable with LLVM/Clang.

To use LLVM set the following environment variables:
```
% export LLVM_SW_TOOLCHAIN=/opt/llvm
% export LLVM=1
```

Individual tests may add additional arguments to the clang invocation using the *llvm_cflags* argument in the test configuration YAML.
The default architecture for LLVM tests is *rv32imc*.  Tests may enable additional extensions by setting the *llvm_march* argument in
the test configuration YAML.

#### Known caveats with LLVM

* When using a non-standard extension, the test should set the cflag `-menable-experimental-extensions`
* The clang integrated assembler cannot properly convert conditional branches to jump sequences when the branch distance is too large
(i.e. beyond +-2KB).  Set the cflag `-fno-integrated-as` to use a GNU system assembler with this ability.
