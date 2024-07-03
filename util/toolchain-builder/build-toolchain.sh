#!/bin/bash

#############################################################################
#
# Copyright 2024 Thales DIS France SAS
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
#
#############################################################################
#
# Original Author: Zbigniew CHAMSKI, Thales Silicon Security
#
# Adapted by Mathieu Gouttenoire, Thales DIS France SAS
#
#############################################################################

# Assumptions:
# - the required binutils source is in src/binutils-gdb
# - the required GCC source is in src/gcc
# - the required LLVM source is in src/llvm-project
# - the required newlib is in src/newlib
# - the user invoking this script has sufficient permissions
#   to create/populate the installation directory.
# - there are no restrictions on the parallelism of the build process
#   ("make -j" without an explicit job limit causes no significant harm)


# Helper function to print usage information.
print_usage() {
    echo Usage:
    echo "  $SHELL $0 [-h|--help]"
    echo "  $SHELL $0 [-f|--force] [CONFIG_NAME] INSTALL_DIR"
    echo ""
    echo "  -h, --help       Print this help message and exit."
    echo "  -f, --force      Rebuild toolchain from scratch (remove build dirs,"
    echo "                     configure and build again.)"
    echo "  CONFIG_NAME      Use configuration from file config/CONFIG_NAME.sh"
    echo "                     (default: '$CONFIG_NAME')"
    echo "  INSTALL_DIR      Path where the toolchain should be installed"
    echo "                     (relative paths will be converted to absolute ones,"
    echo "                     missing parent directories will be created as needed.)"
}

# Helper function to parse the cmdline args.
# Takes the complete list of cmdline args, drops them as they get parsed.
parse_cmdline() {

    POSITIONAL_ARGS=()

    while [ $# -gt 0 ]; do
        case $1 in
            -h|--help)
                print_usage
                exit 0
                ;;
            -f|--force)
                FORCE_REBUILD=yes
	            shift
                ;;
            -*|--*)
                echo "*** Unknown option $1"
                print_usage
                exit 1
                ;;
            *)
                POSITIONAL_ARGS+=("$1")
                shift
                ;;
        esac
    done

    case ${#POSITIONAL_ARGS[@]} in
        0)
            echo "*** Argument INSTALL_DIR is missing!"
            print_usage
            exit 1
            ;;
        1)
            export INSTALL_DIR="${POSITIONAL_ARGS[0]}"
            ;;
        2)
            CONFIG_NAME="${POSITIONAL_ARGS[0]}"
            export INSTALL_DIR="${POSITIONAL_ARGS[1]}"
            ;;
        *)
            echo "*** Too may arguments were given!"
            print_usage
            exit 1
            ;;
    esac
}



build_binutils() {
    # Create build directory
    mkdir -p "$BUILD_DIR/binutils-$1"
    cd "$BUILD_DIR/binutils-$1"
    [ -d gas/doc ] || mkdir -p gas/doc # Binutils 2.40 has a bug caused by a missing 'gas/doc'

    [ -f Makefile ] || CFLAGS="-O2" CXXFLAGS="-O2" \
    $SRC_DIR/$BINUTILS_DIR/configure $(BINUTILS_CONFIGURE_OPTS $1)
    make -j$NUM_JOBS
    make install

    # Add symlinks for riscv64 triple
    shopt -s nullglob
    cd "$INSTALL_DIR/bin"
    for TOOL in riscv32-unknown-elf-*; do
        ln -sv ${TOOL} riscv64-unknown-elf-${TOOL#riscv32-unknown-elf-}
    done
}


build_gcc() {
    # Create build directory
    mkdir -p "$BUILD_DIR/gcc"
    cd "$BUILD_DIR/gcc"

    [ -f Makefile ] || CFLAGS="-O2" CXXFLAGS="-O2" \
    $SRC_DIR/$GCC_DIR/configure $(GCC_CONFIGURE_OPTS)
    make -j$NUM_JOBS
    make install
}


build_llvm() {
    # Create build directory
    mkdir -p "$BUILD_DIR/llvm"
    cd "$BUILD_DIR/llvm"

    [ -f Makefile ] || cmake $SRC_DIR/$LLVM_DIR/llvm $(LLVM_CONFIGURE_OPTS)
    make -j$NUM_JOBS
    make install-distribution

    # Add symlinks to LLVM tools
    cd "$INSTALL_DIR/bin"
    for TOOL in clang clang++ cc c++; do
        ln -sv clang riscv32-unknown-elf-$TOOL
        ln -sv clang riscv64-unknown-elf-$TOOL
    done
}


build_newlib() {
    # Create build directory
    PATH=${INSTALL_DIR}/bin:${PATH}
    mkdir -p "$BUILD_DIR/newlib-$1"
    cd "$BUILD_DIR/newlib-$1"

    [ -f Makefile ] || CFLAGS_FOR_TARGET="-O2 -mcmodel=medany -Wno-unused-command-line-argument -Wno-implicit-function-declaration -Wno-int-conversion" \
    $SRC_DIR/$NEWLIB_DIR/configure $(NEWLIB_CONFIGURE_OPTS $1)
    make -j$NUM_JOBS
    make install
}


build_compiler_rt() {
    # Create build directory
    mkdir -p "$BUILD_DIR/compiler-rt-$1"
    cd "$BUILD_DIR/compiler-rt-$1"

    COMPILER_RT_CONFIGURE_OPTS $1
    [ -f Makefile ] || cmake $SRC_DIR/$LLVM_DIR/compiler-rt $(COMPILER_RT_CONFIGURE_OPTS $1)
    make -j$NUM_JOBS
    make install
}


build_gcc_toolchain() {
    [ $FORCE_REBUILD = "yes" ] && rm -rf $BUILD_DIR/{gcc,*-none-elf}

    echo "### Building Binutils ..."
    build_binutils riscv-none-elf

    echo "### Building GCC ..."
    build_gcc

    echo "### Building Newlib ..."
    build_newlib riscv-none-elf
}


build_llvm_toolchain() {
    [ $FORCE_REBUILD = "yes" ] && rm -rf $BUILD_DIR/{llvm,*-unknown-elf}

    echo "### Building Binutils ..."
    build_binutils riscv32-unknown-elf

    echo "### Building LLVM ..."
    build_llvm

    echo "### Building Newlib 32 bits ..."
    build_newlib riscv32-unknown-elf

    echo "### Building Newlib 64 bits ..."
    build_newlib riscv64-unknown-elf

    echo "### Building Compiler-RT 32 bits ..."
    build_compiler_rt riscv32-unknown-elf

    echo "### Building Compiler-RT 64 bits ..."
    build_compiler_rt riscv64-unknown-elf
}



# Absolute path of the toolchain-builder directory
export ROOT_DIR=$(dirname $(readlink -f $0))

# ======== Default settings: GCC 13.1.0 baremetal, no forced rebuild ========
# - toolchain configuration.
#   NOTE: config/$CONFIG_NAME.sh can be a symbolic link.
CONFIG_NAME="gcc-13.1.0-baremetal"

# - rebuild mode
FORCE_REBUILD=no


echo "### Parsing the cmdline..."
parse_cmdline "$@"

# Load global config
. $ROOT_DIR/config/global.sh

# Make sure the install directory exists and is empty
if [ -n "$(ls -A $INSTALL_DIR 2>/dev/null)" ]; then
    echo "Install directory $INSTALL_DIR is not empty!"
    exit 1
else
    mkdir -p "$INSTALL_DIR"
fi

if [[ $CONFIG_NAME == "gcc"* ]]; then
    build_gcc_toolchain
else
    build_llvm_toolchain
fi


# Exit happily.
exit 0

