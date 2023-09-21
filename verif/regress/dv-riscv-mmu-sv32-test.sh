# Copyright 2021 Thales DIS design services SAS
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
# You may obtain a copy of the License at https://solderpad.org/licenses/
#
# Original Author: Jean-Roch COULON - Thales

# where are the tools
if ! [ -n "$RISCV" ]; then
  echo "Error: RISCV variable undefined"
  return
fi

# install the required tools
source verif/regress/install-cva6.sh
source verif/regress/install-riscv-dv.sh
source verif/regress/install-riscv-arch-test.sh

if ! [ -n "$DV_TARGET" ]; then
  DV_TARGET=cv32a60x
fi

if ! [ -n "$DV_SIMULATORS" ]; then
  DV_SIMULATORS=veri-testharness,spike
fi

cd verif/sim
python3 cva6.py --testlist=../tests/testlist_riscv-mmu-sv32-arch-test-$DV_TARGET.yaml --target $DV_TARGET --iss_yaml=cva6.yaml --iss=$DV_SIMULATORS $DV_OPTS --linker=../tests/riscv-arch-test/riscv-target/spike/link.ld
cd -
