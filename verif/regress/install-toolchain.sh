#!/bin/bash
# Copyright 2026 OpenHW Group
# SPDX-License-Identifier: Apache-2.0
#
# Install a prebuilt RISC-V GCC toolchain into <cva6>/tools/riscv.
# Wraps ci/install-toolchain.sh with a local default install path.

ROOT_PROJECT=$(readlink -f "$(dirname "${BASH_SOURCE[0]}")/../..")

if [ -z "$RISCV" ] || [ "$RISCV" = "__local__" ]; then
  export RISCV="$ROOT_PROJECT/tools/riscv"
  echo "Setting RISCV to '$RISCV'..."
fi

if [ -f "$RISCV/bin/riscv64-unknown-elf-gcc" ] || \
   [ -f "$RISCV/bin/riscv32-unknown-elf-gcc" ] || \
   ls "$RISCV/bin"/riscv*-unknown-elf-gcc >/dev/null 2>&1; then
  echo "RISC-V toolchain already installed in '$RISCV'."
  exit 0
fi

mkdir -p "$RISCV"
bash "$ROOT_PROJECT/ci/install-toolchain.sh"
