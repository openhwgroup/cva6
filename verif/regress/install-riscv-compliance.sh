# Copyright 2021 Thales DIS design services SAS
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
# You may obtain a copy of the License at https://solderpad.org/licenses/
#
# Original Author: Jean-Roch COULON - Thales

if ! [ -n "$COMPLIANCE_REPO" ]; then
  COMPLIANCE_REPO="https://github.com/riscv-non-isa/riscv-arch-test.git"
  COMPLIANCE_BRANCH="main"
  COMPLIANCE_HASH="220e78542da4510e40eac31e31fdd4e77cdae437"
  COMPLIANCE_PATCH="../../../verif/regress/riscv-compliance.patch"
fi
echo "Repo:  " $COMPLIANCE_REPO
echo "Branch:" $COMPLIANCE_BRANCH
echo "Hash:  " $COMPLIANCE_HASH
echo "Patch: " $COMPLIANCE_PATCH

mkdir -p verif/tests
if ! [ -d verif/tests/riscv-compliance ]; then
  git clone $COMPLIANCE_REPO -b $COMPLIANCE_BRANCH verif/tests/riscv-compliance
  cd verif/tests/riscv-compliance; git checkout $COMPLIANCE_HASH;
  if [[ -n "$COMPLIANCE_PATCH" && -f "$COMPLIANCE_PATCH" ]]; then
    echo "Applying patch $COMPLIANCE_PATCH in $PWD..."
    git apply "$COMPLIANCE_PATCH"
  fi
  cd -
fi
