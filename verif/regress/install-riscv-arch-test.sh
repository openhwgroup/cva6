# Copyright 2021 Thales DIS design services SAS
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
# You may obtain a copy of the License at https://solderpad.org/licenses/
#
# Original Author: Jean-Roch COULON - Thales

# riscv-arch-tests uses definition of RVMODEL_HALT provided by Spike.
. verif/regress/install-spike.sh
if [ ! -d $SPIKE_SRC_DIR/arch_test_target ]; then
  echo "*** Variable SPIKE_SRC_DIR must point to a source-based installation of Spike."
  return 1
fi

if ! [ -n "$ARCH_TEST_REPO" ]; then
  ARCH_TEST_REPO=https://github.com/riscv-non-isa/riscv-arch-test
  ARCH_TEST_BRANCH=main
  ARCH_TEST_HASH="a5a49fc9f244192649e57fe61b4513d9bc39b1e3"
fi
echo "Repo:  " $ARCH_TEST_REPO
echo "Branch:" $ARCH_TEST_BRANCH
echo "Hash:  " $ARCH_TEST_HASH


mkdir -p verif/tests
if ! [ -d verif/tests/riscv-arch-test ]; then
  git clone $ARCH_TEST_REPO -b $ARCH_TEST_BRANCH verif/tests/riscv-arch-test
  cd verif/tests/riscv-arch-test; git checkout $ARCH_TEST_HASH;
  # Copy Spike definitions to the corresponding riscv-target subdirectory.
  cp -rpa $SPIKE_SRC_DIR/arch_test_target riscv-target
  cd -
fi

