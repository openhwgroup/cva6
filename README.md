# CVA6 RISC-V CPU [![Build Status](https://github.com/openhwgroup/cva6/actions/workflows/ci.yml/badge.svg?branch=master)](https://github.com/openhwgroup/cva6/actions/workflows/ci.yml) [![CVA6 dashboard](https://riscv-ci.pages.thales-invia.fr/dashboard/badge.svg)](https://riscv-ci.pages.thales-invia.fr/dashboard/) [![Documentation Status](https://readthedocs.com/projects/openhw-group-cva6-user-manual/badge/?version=latest)](https://docs.openhwgroup.org/projects/cva6-user-manual/?badge=latest) [![GitHub release](https://img.shields.io/github/release/openhwgroup/cva6?include_prereleases=&sort=semver&color=blue)](https://github.com/openhwgroup/cva6/releases/)

CVA6 is a 6-stage, single-issue, in-order CPU which implements the 64-bit RISC-V instruction set. It fully implements I, M, A and C extensions as specified in Volume I: User-Level ISA V 2.3 as well as the draft privilege extension 1.10. It implements three privilege levels M, S, U to fully support a Unix-like operating system. Furthermore, it is compliant to the draft external debug spec 0.13.

It has a configurable size, separate TLBs, a hardware PTW and branch-prediction (branch target buffer and branch history table). The primary design goal was on reducing critical path length.


# Resources and Ecosystem

The CVA6 core is part of a vivid ecosystem. In [this document](RESOURCES.md), we gather pointers to this ecosystem (building blocks, designs, partners...)
This guide provides step-by-step instructions to prepare and run a simulation using the CVA6 core.
First, clone the core from the Git repository and initialize its submodules:
```bash
git clone https://github.com/X-Crpt/cva6.git
cd cva6
git submodule update --init --recursive
```
It is strongly recommended to use the toolchain built with the provided scripts:
```bash
export ROOT_PROJECT=$PWD
export RISCV="$ROOT_PROJECT/util/riscv_toolchain"
export INSTALL_DIR=$RISCV
cd util/toolchain-builder/
bash get-toolchain.sh
bash build-toolchain.sh $INSTALL_DIR
cd ../..
```
To set up the necessary simulators, run the following scripts:
```bash
source verif/regress/install-verilator.sh
source verif/regress/install-spike.sh
```
`setup-env.sh` file located at `verif/sim/setup-env.sh` and `verif/sim/cva6.py` file have been modified for our application. 
To run a test using the core and the Spike simulator, execute:
```bash
source verif/regress/initial_test.sh
```

# Branches and Organization
### 1. Basic CV-X-IF Coprocessor Test  
- Implemented a simple coprocessor using CV-X-IF with custom instructions for **XOR, AND, and OR** operations.  
- Validated functionality through initial hardware/software testing.  
- More details can be found in the respective branch. [branch-name](https://github.com/your-repo-name/tree/branch-name)


### 2️. Crypto Coprocessor Using CVA6 Register File  
- Implemented a **64-bit RISC-V Cryptographic Extensions** coprocessor based on [riscv-crypto](https://github.com/riscv/riscv-crypto).  
- Integrated the coprocessor following the **CV-X-IF** protocol, using the **CVA6 core's internal register file (RF)** for data processing.
- More details can be found in the respective branch. [branch-name](https://github.com/your-repo-name/tree/branch-name)

### 3. Crypto Coprocessor with Dedicated Register File  
- Extended the implementation to a cryptographic coprocessor that operates **exclusively with an external register file**, independent of CVA6's RF.  
- Added custom instructions to correctly manage data within the dedicated register file.
- More details can be found in the respective branch. [branch-name](https://github.com/your-repo-name/tree/branch-name)

# Acknowledgements

Check out the [acknowledgements](ACKNOWLEDGEMENTS.md).
