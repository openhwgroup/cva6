# CVA6 Post-Quantum Cryptography Port by GSTL-ITU

This port aims to enhance the working environment experience for scaled teams while adding several sources and scripts for post-quantum cryptography (PQC) applications.

## Table of Contents
- [ CVA6 Post-Quantum Cryptography Port by GSTL-ITU](#cva6-post-quantum-cryptography-port-by-gstl-itu)
   - [Easy Docker Setup for CVA6](#easy-docker-setup-for-cva6)
     - [Added Configuration Files](#added-configuration-files)
     - [How to Build and Run](#how-to-build-and-run)
   - [PQC Source Codes](#pqc-source-codes)
   - [Simulation Scripts](#simulation-scripts)
   - [FPGA Tests](#fpga-tests)
- [Original CVA6 README](#cva6-risc-v-cpu-build-status-cva6-dashboard-documentation-status-github-release)
---

## Easy Docker Setup for CVA6

This repository offers a common ground for small and medium-scale teams. The original CVA6 repository requires specific, version-limited software and tools, including GCC, RISC-V GCC, Spike, Verilator, and various Python libraries. 

This fork introduces a Docker solution that automatically builds the exact version of every required tool, ensuring consistency across your team. It is designed to be easily built within Visual Studio Code using the official "Dev Containers" extension and Docker Engine (see the [Docker Engine installation guide](https://docs.docker.com/engine/install/) for details). 

### Added Configuration Files
This repository comes with four additional files to achieve this stable environment:
* **`.devcontainer/Dockerfile`**: Sets up the Docker environment using an Ubuntu 22.04 base image. It installs required dependencies like GCC 11, downloads the RISC-V GCC 13.2.0 toolchain (installs a compiled binary rather than compiling), configures necessary environment variables (including paths for Verilator v5.008 and Spike), and creates a dedicated `cva6user` with sudo privileges.
* **`.devcontainer/devcontainer.json`**: Configures the VS Code Dev Container extension. It sets the remote user to `cva6user`, automatically installs the required C/C++ and Verilog HDL extensions, and triggers the `python_requirements.sh` script once the container is created.
* **`python_requirements.sh`**: Iterates through the repository to find and install all Python dependencies via `pip3`, utilizing specific flags to prevent C-API build errors for packages like `ruamel.yaml`.
* **`cva6-pqc.code-workspace`**: An optional, out-of-the-box VS Code workspace configuration for this repository. 

> **Note on Standalone Docker Usage:** If you want to run the Docker environment outside of VS Code, the `devcontainer.json` configuration is not required, and the `.code-workspace` file is unused. Ensure your host machine's Docker permissions are configured properly. On Linux, you may need to add your host user to the `docker` group to run commands without `sudo` (refer to the [Docker Linux post-installation steps](https://docs.docker.com/engine/install/linux-postinstall/)).

### How to Build and Run

1. **Open the repository in VS Code.** Ensure you have the official "Dev Containers" extension installed.
```sh
git clone https://github.com/GSTL-ITU/cva6-pqc
cd cva6-pqc
git submodule update --init --recursive
```
2. **Build the container:** Press `Ctrl+Shift+P` (or `Cmd+Shift+P` on Mac) and select **`Dev Containers: Rebuild and Reopen in Container`**. 
3. VS Code will automatically start building the Docker container. The initial build will take some time as it prepares the Ubuntu 22.04 system, installs GCC 11, and sets up the RISC-V toolchain. 
4. **Build the simulation tools:** Once the environment is up and running, you still need to build Spike and Verilator. These tools will be installed to `/tools` subdirectory and won't be compiled into any image in the future. Open a new terminal inside VS Code and run the following command:

```bash
# This will build the simulation tools (Spike & Verilator) and run the given test. Replace TESTNAME with a valid smoke test.
bash ./verif/regress/smoke-tests<TESTNAME>.sh
```

To run simulations and tests, you can either follow the scripts provided in `/verif/regress/` for smoke tests or refer to `/tutorials/running_sim.md`.

---

## PQC Source Codes

* **Location:** `verif/tests/custom/`

This directory houses the source code and verification workloads for Post-Quantum Cryptography algorithms:
* `verif/tests/custom/falcon/` — Falcon signature scheme sources and test suites.
* `verif/tests/custom/kyber/` — ML-KEM (Kyber) key encapsulation sources and benchmarks.
* `verif/tests/custom/dilithium/` — ML-DSA (Dilithium) digital signature algorithm implementations.

> Refer to the dedicated `README.md` file located inside each individual algorithm folder for specific compilation flags, test targets, and usage instructions.

---

## Simulation Scripts

* **Location:** `pqc_tests/`

This section provides shell scripts (`.sh`) designed to easily configure parameters, streamline automated test execution, and run simulations for the added PQC suites across supported targets (Spike, Verilator, etc.).

> For detailed script options, configuration flags, and example execution workflows, see [`pqc_tests/README.md`](./pqc_tests/README.md).

---

## FPGA Tests

* **Location:** `pqc_tests_fpga/`

Provides a streamlined environment for evaluating PQC code directly on hardware targets in real time. This folder includes:
* **Makefiles & Linker Scripts:** Pre-configured for building hardware-compatible binaries.
* **C Test Applications:** Minimal test cases, including UART communication and transaction routines for real-time monitoring.

> Refer to [`pqc_tests_fpga/README.md`](./pqc_tests_fpga/README.md) for toolchain configuration, flashing instructions, and UART terminal connection guides.

---

You can find the original READMEs and details below and additional READMEs inside the according subdirectories. 

---

# CVA6 RISC-V CPU [![Build Status](https://github.com/openhwgroup/cva6/actions/workflows/ci.yml/badge.svg?branch=master)](https://github.com/openhwgroup/cva6/actions/workflows/ci.yml) [![CVA6 dashboard](https://riscv-ci.pages.thales-invia.fr/dashboard/badge_master.svg)](https://riscv-ci.pages.thales-invia.fr/dashboard/dashboard_cva6.html) [![Documentation Status](https://readthedocs.com/projects/openhw-group-cva6-user-manual/badge/?version=latest)](https://docs.openhwgroup.org/projects/cva6-user-manual/?badge=latest) [![GitHub release](https://img.shields.io/github/release/openhwgroup/cva6?include_prereleases=&sort=semver&color=blue)](https://github.com/openhwgroup/cva6/releases/)

CVA6 is a 6-stage, single-issue, in-order CPU which implements the 64-bit RISC-V instruction set. It fully implements I, M, A and C extensions as specified in Volume I: User-Level ISA V 2.3 as well as the draft privilege extension 1.10. It implements three privilege levels M, S, U to fully support a Unix-like operating system. Furthermore, it is compliant to the draft external debug spec 0.13.

It has a configurable size, separate TLBs, a hardware PTW and branch-prediction (branch target buffer and branch history table). The primary design goal was on reducing critical path length.

The CVA6 core is part of a vivid ecosystem. In [this document](RESOURCES.md), we gather pointers to this ecosystem (building blocks, designs, partners...).

A performance model of CVA6 is available in the `perf-model/` folder of this repository.
It can be used to investigate performance-related micro-architecture changes.

<img src="docs/03_cva6_design/_static/ariane_overview.drawio.png"/>


# Quick setup

The following instructions will allow you to compile and run a Verilator model of the CVA6 APU (which instantiates the CVA6 core) within the CVA6 APU testbench (corev_apu/tb).

Throughout all build and simulations scripts executions, you can use the environment variable `NUM_JOBS` to set the number of concurrent jobs launched by `make`:
- if left undefined, `NUM_JOBS` will default to 1, resulting in a sequential execution
of `make` jobs;
- when setting `NUM_JOBS` to an explicit value, it is recommended not to exceed 2/3 of
the total number of virtual cores available on your system.    

1. Checkout the repository and initialize all submodules.
```sh
git clone https://github.com/openhwgroup/cva6.git
cd cva6
git submodule update --init --recursive
```

2. Install the GCC Toolchain [build prerequisites](util/toolchain-builder/README.md#Prerequisites) then [the toolchain itself](util/toolchain-builder/README.md#Getting-started).

:warning: It is **strongly recommended** to use the toolchain built with the provided scripts.

3. Install `cmake`, version 3.14 or higher.

4. Set the RISCV environment variable.
```sh
export RISCV=/path/to/toolchain/installation/directory
```

5. Install `help2man` and `device-tree-compiler` packages.

For Debian-based Linux distributions, run :

```sh
sudo apt-get install help2man device-tree-compiler
```

6. Install the riscv-dv requirements:

```sh
pip3 install -r verif/sim/dv/requirements.txt
```

7. Run these commands to install a custom Spike and Verilator (i.e. these versions must be used to simulate the CVA6) and [these](#running-regression-tests-simulations) tests suites.
```sh
# DV_SIMULATORS is detailed in the next section
export DV_SIMULATORS=veri-testharness,spike
bash verif/regress/smoke-tests.sh
```


# Tutorials

* **[Running Simulations](tutorials/running_sim.md)**
* **[ASIC Implementation](tutorials/asic.md)**
* **[FPGA Implementation and running an OS](tutorials/fpga.md)**
* **[Instruction Tracing](corev_apu/instr_tracing/README.md)**

# Directory Structure

The directory structure separates the [CVA6 RISC-V CPU](#cva6-risc-v-cpu) core from the [CORE-V-APU FPGA Emulation Platform](#corev-apu-fpga-emulation).
Files, directories and submodules under `cva6` are for the core _only_ and should not have any dependencies on the APU.
Files, directories and submodules under `corev_apu` are for the FPGA Emulation platform.
The CVA6 core can be compiled stand-alone, and obviously the APU is dependent on the core.

The top-level directories of this repo:
* **ci**: Scriptware for CI.
* **common**: Source code used by both the CVA6 Core and the COREV APU. Subdirectories from here are `local` for common files that are hosted in this repo and `submodules` that are hosted in other repos.
* **core**: Source code for the CVA6 Core only. There should be no sources in this directory used to build anything other than the CVA6 core.
* **corev_apu**: Source code for the CVA6 APU, exclusive of the CVA6 core. There should be no sources in this directory used to build the CVA6 core.
* **docs**: Documentation.
* **pd**: Example and CI scripts to synthesis CVA6.
* **util**: General utility scriptware.
* **vendor**: Third-party IP maintained outside the repository.
* **verif**: Verification environment for the CVA6. The verification files shared with other cores are in the [core-v-verif](https://github.com/openhwgroup/core-v-verif) repository on GitHub. core-v-verif is defined as a cva6 submodule.


## verif Directories

- **bsp**:     board support package for test-programs compiled/assembled/linked for the CVA6.
This BSP is used by both `core` testbench and `uvmt_cva6` UVM verification environment.
- **regress**: scripts to install tools, test suites, CVA6 code and to execute tests
- **sim**:     simulation environment (e.g. riscv-dv)
- **tb**:      testbench module instancing the core
- **tests**:   source of test cases and test lists


# Contributing

We highly appreciate community contributions.
To ease the work of reviewing contributions, please review [CONTRIBUTING](CONTRIBUTING.md).

Contributions to the documentation (`docs/` and `tutorials/` directories) are very welcome as well.

If you find any problems or issues with CVA6 or the documentation, please check out the [issue tracker](https://github.com/openhwgroup/cva6/issues)
and create a new issue if your problem is not yet tracked. \
[The CVA6 Kanban Board](https://github.com/orgs/openhwgroup/project/3/view/7) loosely tracks planned improvements.


# Publication

If you use CVA6 in your academic work you can cite us:

<details>
<summary>CVA6 Publication</summary>

```
@article{zaruba2019cost,
   author={F. {Zaruba} and L. {Benini}},
   journal={IEEE Transactions on Very Large Scale Integration (VLSI) Systems},
   title={The Cost of Application-Class Processing: Energy and Performance Analysis of a Linux-Ready 1.7-GHz 64-Bit RISC-V Core in 22-nm FDSOI Technology},
   year={2019},
   volume={27},
   number={11},
   pages={2629-2640},
   doi={10.1109/TVLSI.2019.2926114},
   ISSN={1557-9999},
   month={Nov},
}
```

</details>

# Acknowledgements

Check out the [acknowledgements](ACKNOWLEDGEMENTS.md).


