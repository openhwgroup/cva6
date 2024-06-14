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
source ./verif/regress/install-verilator.sh
source ./verif/regress/install-spike.sh

# install the required test suites
source ./verif/regress/install-riscv-compliance.sh
source ./verif/regress/install-riscv-tests.sh
source ./verif/regress/install-riscv-arch-test.sh

# setup sim env
source ./verif/sim/setup-env.sh

echo "$SPIKE_INSTALL_DIR$"

if ! [ -n "$DV_SIMULATORS" ]; then
  DV_SIMULATORS=vcs-testharness,spike
fi

if ! [ -n "$UVM_VERBOSITY" ]; then
    export UVM_VERBOSITY=UVM_NONE
fi

export DV_OPTS="$DV_OPTS --issrun_opts=+debug_disable=1+UVM_VERBOSITY=$UVM_VERBOSITY"

CC_OPTS="-static -mcmodel=medany -fvisibility=hidden -nostdlib -nostartfiles -g ../tests/custom/common/syscalls.c ../tests/custom/common/crt.S -I../tests/custom/env -I../tests/custom/common -lgcc"


cd verif/sim/
make -C ../.. clean
make clean_all
python3 cva6.py --testlist=../tests/testlist_riscv-compliance-cv64a6_imafdc_sv39.yaml --test rv32i-I-ADD-01 --iss_yaml cva6.yaml --target cv64a6_imafdc_sv39 --iss=$DV_SIMULATORS $DV_OPTS
python3 cva6.py --testlist=../tests/testlist_riscv-tests-cv64a6_imafdc_sv39-v.yaml --test rv64ui-v-add --iss_yaml cva6.yaml --target cv64a6_imafdc_sv39 --iss=$DV_SIMULATORS $DV_OPTS
python3 cva6.py --testlist=../tests/testlist_riscv-tests-cv64a6_imafdc_sv39-p.yaml --test rv64ui-p-add --iss_yaml cva6.yaml --target cv64a6_imafdc_sv39 --iss=$DV_SIMULATORS $DV_OPTS
python3 cva6.py --testlist=../tests/testlist_riscv-arch-test-cv64a6_imafdc_sv39.yaml --test rv64i_m-add-01 --iss_yaml cva6.yaml --target cv64a6_imafdc_sv39 --iss=$DV_SIMULATORS $DV_OPTS  --linker=../tests/riscv-arch-test/riscv-target/spike/link.ld
python3 cva6.py --testlist=../tests/testlist_custom.yaml --test custom_test_template --iss_yaml cva6.yaml --target cv64a6_imafdc_sv39 --iss=$DV_SIMULATORS $DV_OPTS
python3 cva6.py --c_tests ../tests/custom/hello_world/hello_world.c --iss_yaml cva6.yaml --target cv64a6_imafdc_sv39 --iss=$DV_SIMULATORS --gcc_opts="$CC_OPTS -T ../tests/custom/common/test.ld" $DV_OPTS
make -C ../.. clean
make clean_all
python3 cva6.py --testlist=../tests/testlist_riscv-compliance-cv32a60x.yaml --test rv32i-I-ADD-01 --iss_yaml cva6.yaml --target cv32a6_imac_sv32 --iss=$DV_SIMULATORS $DV_OPTS
python3 cva6.py --testlist=../tests/testlist_riscv-tests-cv32a60x-p.yaml --test rv32ui-p-add --iss_yaml cva6.yaml --target cv32a6_imac_sv32 --iss=$DV_SIMULATORS $DV_OPTS
python3 cva6.py --testlist=../tests/testlist_riscv-arch-test-cv32a60x.yaml --test rv32im-cadd-01 --iss_yaml cva6.yaml --target cv32a6_imac_sv32 --iss=$DV_SIMULATORS $DV_OPTS  --linker=../tests/riscv-arch-test/riscv-target/spike/link.ld
python3 cva6.py --c_tests ../tests/custom/hello_world/hello_world.c --iss_yaml cva6.yaml --target cv32a6_imac_sv32 --iss=$DV_SIMULATORS --linker=../tests/custom/common/test.ld --gcc_opts="$CC_OPTS" $DV_OPTS
make -C ../.. clean
make clean_all
python3 cva6.py --testlist=../tests/testlist_riscv-compliance-cv32a60x.yaml --test rv32i-I-ADD-01 --iss_yaml cva6.yaml --target cv32a65x --iss=$DV_SIMULATORS $DV_OPTS
python3 cva6.py --testlist=../tests/testlist_riscv-tests-cv32a60x-p.yaml --test rv32ui-p-add --iss_yaml cva6.yaml --target cv32a65x --iss=$DV_SIMULATORS $DV_OPTS
python3 cva6.py --testlist=../tests/testlist_riscv-arch-test-cv32a60x.yaml --test rv32im-cadd-01 --iss_yaml cva6.yaml --target cv32a65x --iss=$DV_SIMULATORS $DV_OPTS  --linker=../tests/riscv-arch-test/riscv-target/spike/link.ld
python3 cva6.py --c_tests ../tests/custom/hello_world/hello_world.c --iss_yaml cva6.yaml --target cv32a65x --iss=$DV_SIMULATORS --linker=../tests/custom/common/test.ld --gcc_opts="$CC_OPTS" $DV_OPTS
make -C ../.. clean
make clean_all
python3 cva6.py --testlist=../tests/testlist_riscv-compliance-cv64a6_imafdc_sv39.yaml --test rv32i-I-ADD-01 --iss_yaml cva6.yaml --target cv64a6_mmu --iss=$DV_SIMULATORS $DV_OPTS
python3 cva6.py --testlist=../tests/testlist_riscv-tests-cv64a6_imafdc_sv39-p.yaml --test rv64ui-p-add --iss_yaml cva6.yaml --target cv64a6_mmu --iss=$DV_SIMULATORS $DV_OPTS
python3 cva6.py --testlist=../tests/testlist_riscv-arch-test-cv64a6_imafdc_sv39.yaml --test rv64i_m-add-01 --iss_yaml cva6.yaml --target cv64a6_mmu --iss=$DV_SIMULATORS $DV_OPTS --linker=../tests/riscv-arch-test/riscv-target/spike/link.ld
python3 cva6.py --c_tests ../tests/custom/hello_world/hello_world.c --iss_yaml cva6.yaml --target cv64a6_mmu --iss=$DV_SIMULATORS --linker=../tests/custom/common/test.ld --gcc_opts="$CC_OPTS" $DV_OPTS
make -C ../.. clean
make clean_all

cd -
