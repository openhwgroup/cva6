# Copyright 2021 Thales DIS design services SAS
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
# You may obtain a copy of the License at https://solderpad.org/licenses/
#
# Original Author: Jean-Roch COULON (jean-roch.coulon@thalesgroup.fr)

if ! [ -n "$ARCH_TEST_REPO" ]; then
  ARCH_TEST_REPO=https://github.com/riscv-non-isa/riscv-arch-test
  ARCH_TEST_BRANCH=main
  ARCH_TEST_HASH=ad04e119a5d846a1c11159786ad3382cf5ad3649
fi
echo $ARCH_TEST_REPO
echo $ARCH_TEST_BRANCH
echo $ARCH_TEST_HASH

mkdir -p cva6/tests
if ! [ -d cva6/tests/riscv-arch-test ]; then
  git clone $ARCH_TEST_REPO -b $ARCH_TEST_BRANCH cva6/tests/riscv-arch-test
  cd cva6/tests/riscv-arch-test; git checkout $ARCH_TEST_HASH;
  cd -
fi

