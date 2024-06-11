# Copyright 2021 Thales DIS design services SAS
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
# You may obtain a copy of the License at https://solderpad.org/licenses/
#
# Original Author: Jean-Roch COULON - Thales

if ! [ -n "$TESTS_REPO" ]; then
  TESTS_REPO="https://github.com/riscv/riscv-tests.git"
  TESTS_BRANCH="master"
  TESTS_HASH="f92842f91644092960ac7946a61ec2895e543cec"
fi
echo "Repo:  " $TESTS_REPO
echo "Branch:" $TESTS_BRANCH
echo "Hash:  " $TESTS_HASH

mkdir -p verif/tests
if ! [ -d verif/tests/riscv-tests ]; then
  git clone $TESTS_REPO -b $TESTS_BRANCH verif/tests/riscv-tests
  cd verif/tests/riscv-tests; git checkout $TESTS_HASH;
  git apply ../../../verif/regress/riscv-tests.patch
  git submodule update --init --recursive
  git apply --directory=env ../../../verif/regress/riscv-tests-env.patch
  cd -
fi
