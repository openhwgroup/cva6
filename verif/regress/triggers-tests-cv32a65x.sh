# Copyright 2021 Thales DIS design services SAS
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
# You may obtain a copy of the License at https://solderpad.org/licenses/
#
# Original Author: Mounsaf YOUSFI - Thales

# where are the tools
if ! [ -n "$RISCV" ]; then
  echo "Error: RISCV variable undefined"
  return
fi

if ! [ -n "$DV_SIMULATORS" ]; then
  DV_SIMULATORS=vcs-testharness,spike
fi

# install the required tools
if [[ "$DV_SIMULATORS" == *"veri-testharness"* ]]; then
  source ./verif/regress/install-verilator.sh
fi
source ./verif/regress/install-spike.sh

# setup sim env
source ./verif/sim/setup-env.sh

echo "$SPIKE_INSTALL_DIR$"

if ! [ -n "$UVM_VERBOSITY" ]; then
    export UVM_VERBOSITY=UVM_NONE
fi

export DV_OPTS="$DV_OPTS --issrun_opts=+enable_interrupt+tb_performance_mode+debug_disable=1+UVM_VERBOSITY=$UVM_VERBOSITY"

CC_OPTS="-static \
         -mcmodel=medany \
         -fvisibility=hidden \
         -nostartfiles \
         -g \
         -O0 \
         ../tests/custom/common/syscalls.c \
         ../tests/custom/common/crt.S \
         -I../tests/custom/env \
         -I../tests/custom/common"

DV_HWCONFIG_OPTS="cv32a65x Sdtrig=1 SdtrigMcontrol6=1 SdtrigMcontrol6ExecAddr=1 SdtrigMcontrol6ExecData=1 SdtrigMcontrol6Store=1 SdtrigMcontrol6LoadAddr=1 SdtrigMcontrol6LoadData=1 SdtrigIcount=1 SdtrigEtrigger=1 SdtrigItrigger=1 SdtrigNrTriggers=4 SdtrigTriggerChaining=1 SdtrigSupportedActions=2'b01 SdtrigSupportedMatch=10'b11_1111_1111 SdtrigSupportTextra=0"

cd verif/sim/

make -C ../.. clean
make clean_all
python3 cva6.py --target hwconfig --hwconfig_opts="$DV_HWCONFIG_OPTS" --asm_tests=../tests/custom/trigger_tests/trigger_main.S --iss_yaml cva6.yaml --iss=$DV_SIMULATORS --linker=../../config/gen_from_riscv_config/cv32a60x/linker/link.ld --gcc_opts="$CC_OPTS" $DV_OPTS --sv_seed 1
make -C ../.. clean
make clean_all

cd -
