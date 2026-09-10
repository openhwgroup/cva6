# Copyright 2022 Thales DIS France
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
# You may obtain a copy of the License at https://solderpad.org/licenses/
#
# Original Author: Zbigniew CHAMSKI (zbigniew.chamski@thalesgroup.fr)

# where are the tools
if ! [ -n "$RISCV" ]; then
  echo "Error: RISCV variable undefined"
  return
fi

# install the required tools
source ./verif/regress/install-verilator.sh
source ./verif/regress/install-spike.sh
source verif/regress/install-riscv-compliance.sh
source verif/regress/install-riscv-tests.sh

source ./verif/sim/setup-env.sh

if ! [ -n "$DV_SIMULATORS" ]; then
  DV_SIMULATORS=veri-testharness,spike
fi

cd verif/sim/
python3 cva6.py --testlist=../tests/testlist_issues.yaml --test compressed-fpreg-commits-rv64 --iss_yaml cva6.yaml --target cv64a6_imafdc_sv39 --iss=$DV_SIMULATORS $DV_OPTS
make clean
make -C verif/sim clean_all
python3 cva6.py --testlist=../tests/testlist_issues.yaml --test compressed-fpreg-commits-rv32 --iss_yaml cva6.yaml --target cv32a6_imafc_sv32 --iss=$DV_SIMULATORS $DV_OPTS
make clean
make -C verif/sim clean_all


# Check the complete eight-bit Zcmt JVT index with a directed assembly test.
python3 cva6.py \
  --testlist=../tests/testlist_issues.yaml \
  --test zcmt-jvt-index-rv32 \
  --iss_yaml cva6.yaml \
  --target hwconfig \
  --hwconfig_opts="cv32a60x *RVZCMT=1" \
  --iss=veri-testharness \
  --linker="../../config/gen_from_riscv_config/cv32a60x/linker/link.ld"

zcmt_status=$?
if [ "$zcmt_status" -ne 0 ]; then
  echo "Error: Zcmt JVT index assembly regression failed"
  cd ../..
  return "$zcmt_status" 2>/dev/null || exit "$zcmt_status"
fi


# Check that cm.jt clears bit 0 of the loaded JVT target.
python3 cva6.py \
  --testlist=../tests/testlist_issues.yaml \
  --test zcmt-jt-target-lsb-rv32 \
  --iss_yaml cva6.yaml \
  --target hwconfig \
  --hwconfig_opts="cv32a60x *RVZCMT=1" \
  --iss=veri-testharness \
  --linker="../../config/gen_from_riscv_config/cv32a60x/linker/link.ld"

zcmt_jt_lsb_status=$?
if [ "$zcmt_jt_lsb_status" -ne 0 ]; then
  echo "Error: Zcmt cm.jt target LSB regression failed"
  cd ../..
  return "$zcmt_jt_lsb_status" 2>/dev/null || exit "$zcmt_jt_lsb_status"
fi

# Check that cm.jalt clears bit 0 of the loaded JVT target.
python3 cva6.py \
  --testlist=../tests/testlist_issues.yaml \
  --test zcmt-jalt-target-lsb-rv32 \
  --iss_yaml cva6.yaml \
  --target hwconfig \
  --hwconfig_opts="cv32a60x *RVZCMT=1" \
  --iss=veri-testharness \
  --linker="../../config/gen_from_riscv_config/cv32a60x/linker/link.ld"

zcmt_jalt_lsb_status=$?
if [ "$zcmt_jalt_lsb_status" -ne 0 ]; then
  echo "Error: Zcmt cm.jalt target LSB regression failed"
  cd ../..
  return "$zcmt_jalt_lsb_status" 2>/dev/null || exit "$zcmt_jalt_lsb_status"
fi

cd -
