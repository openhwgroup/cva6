# `toolchain-builder`: Basic scripts for building a RISC-V GCC or LLVM compiler toolchain

## Overview

This directory contains basic scripts for building local instances of CORE-V GCC or LLVM toolchains.
The scripts provide the means of fetching the source code and building the executables
and libraries for well-defined toolchain configurations.  The intention is to
simplify the processs of building such toolchains and make it as "push-button"
(and as accessible to CORE-V users) as reasonably possible.

Currently, the scripts support only 'bare metal' toolchain configurations
intended for hardware verification of 32- and 64-bit RISC-V targets.
These configurations are deliberately lightweight and consist of:

* `binutils-gdb`: assembler, linker, GDB debugger, and object file utilities
* `GCC`: the GNU GCC compiler configured for C only
* `LLVM`: the LLVM compiler infrastructure
* `newlib`: an open-source C library suitable for embedded applications.

## Prerequisites

**Disk space:** Approximately 3.5 GB of disk space are needed to build and install a bare-metal toolchain
from source code:

 * 1.9 GB is occupied by source code (including Git history);
 * 1.1 GB is needed for the build space;
 * 0.5 GB is needed for the installed toolchain.

Several **standard packages** are needed to build the compiler
toolchains.  On Debian/Ubuntu, executing the following command should suffice:

    $ sudo apt-get install autoconf automake autotools-dev curl git libmpc-dev libmpfr-dev libgmp-dev gawk build-essential bison flex texinfo gperf libtool bc zlib1g-dev

On Fedora/CentOS/RHEL OS, executing the following command should suffice:

    $ sudo yum install autoconf automake git libmpc-devel mpfr-devel gmp-devel gawk  bison flex texinfo gcc gcc-c++ zlib-devel

On macOS, you can use [Homebrew](http://brew.sh) to install the dependencies:

    $ brew install gawk gnu-sed gmp mpfr libmpc isl zlib

## Getting started

Once the prerequisites (see [above](#prerequisites)) are satisfied, you can fetch and build the
upstream toolchain (default: GCC 13.1.0) for bare-metal 32-bit and 64-bit applications in just three steps.

    # 1. Select an installation location for the toolchain (here: the default RISC-V tooling directory $RISCV).
    INSTALL_DIR=$RISCV

    # 2. Fetch the source code of the toolchain (assumes Internet access.)
    sh get-toolchain.sh

    # 3. Build and install the toolchain (requires write+create permissions for $INSTALL_DIR.)
    sh build-toolchain.sh $INSTALL_DIR

## File and directory structure

The base infrastructure for building compilation toolchains consists of two scripts
and a directory holding configuration files:

 * `get-toolchain.sh`: script in charge of obtaining the source code and
extracting the correct code baselines.
 * `build-toolchain.sh`: script in charge of building and installing the
different toolchain components in suitable order.
 * `config/`: directory containing the configuration files for the various configurations.

In the process of building the toolchain, two new directory trees are created
under the current working directory:

 * `SRC_DIR`: Source code is fetched and checked out into subdirectories of `$SRC_DIR`, which
 defaults to `src/` in the current working directory when it is not set.

 * `BUILD_DIR`: The building of the various components of the toolchain occurs in subdirectories
 of `$BUILD_DIR`, which defaults to `build/` in the current working directory when it is not set.

This directory structure was chosen to keep the source and build directories
local to the user's workspace while supporting systematic out-of-source-tree
building of toolchain components.

## Building a bare-metal toolchain (Newlib-based)

In order to build a toolchain you need to select a _toolchain configuration_ and
an _installation location_ (an "install prefix"):

 * the toolchain configuration name must match one of the predefined `config/CONFIG_NAME.sh`
files under `config` directory.

 * the installation location can be an arbitrary path.  It needs not to exist
yet: any missing directories will be created during the building process. _The user running the
`build-toolchain.sh` script must have sufficient permissions to create the
missing directories of the installation location._

Once a configuration name `CONFIG_NAME` and an installation
location `INSTALL_DIR` are chosen, use

    sh get-toolchain.sh CONFIG_NAME
    # E.g.,
    # sh get-toolchain.sh gcc-13.1.0-baremetal

to fetch/update the source code and to check out the matching baseline of code.

If the name of the toolchain configuration is omitted, a default configuration
will be selected implicitly.  _The default configuration is currently named
`gcc-13.1.0-baremetal`_ and builds a toolchain containing

 * binutils v2.40 (official release baseline)
 * gcc v.13.1.0 (official release baseline)
 * newlib v4.3 (official release baseline).

To build the toolchain from the retrieved source baseline, use

    sh build-toolchain.sh CONFIG_NAME INSTALL_DIR
    # E.g.,
    # sh build-toolchain.sh gcc-13.1.0-baremetal $RISCV

To speedup the building it is recommended to set the number of threads to use

    # Use all available threads
    export NUM_JOBS=$(nproc)
    # Use 8 threads
    export NUM_JOBS=8

The `build-toolchain.sh` script incorporates fallbacks for several commonly encountered configuration and
build issues. However, it is not meant to auto-detect major reconfigurations of source
code such as a change of baseline configuration.  _Whenever the source
configuration is changed, please use the `-f` (or `--force`)
option to forcibly rebuild the entire toolchain_:

    sh build-toolchain.sh -f CONFIG_NAME INSTALL_DIR
    # E.g.,
    # sh build-toolchain.sh -f gcc-13.1.0-baremetal $RISCV

## Defining new configurations

Users involved with toolchain validation and development may be interested in
creating new configurations that cater for specific needs:

 * use of local Git mirrors to enable toolchain development and to shorten
   Git query times
 * building of experimental toolchains combining specific versions of individual
   components.

New configurations can be easily introduced by copying existing
configuration files in subdirectory `config/` under a different name and
adjusting the values of per-component variables.  Taking `GCC` as an example:

 * `GCC_DIR` defines the location of GCC source code.
 * `GCC_REPO` selects the Git repository to fetch GCC code from.
 * `GCC_COMMIT` identifies the revision of source code to use: a specific commit,
   tag, or branch. \
   _**NOTE:** If you set `GCC_COMMIT` to the name of a branch, the
   `get-toolchain.sh` will update the local repository to the tip of the remote
   branch at every invocation._

 * `GCC_CONFIGURE_OPTS` is the list of options to pass to the configure script. 
   It is located in `config/global.sh`.

## Potential additions

Several extensions are envisioned:

* Explicit selection of GDB version
* Support for Linux-based target environments
* Addition of full-featured C library implementations
