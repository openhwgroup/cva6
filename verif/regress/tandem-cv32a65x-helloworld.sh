# Copyright 2021 Thales DIS design services SAS
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
# You may obtain a copy of the License at https://solderpad.org/licenses/
#
# Original Author: Jean-Roch COULON - Thales

# Run hello_world on cv32a65x with Spike embedded tandem (per-instruction
# step-and-compare via DPI) under the questa-uvm flow.

if ! [ -n "$RISCV" ]; then
  echo "Error: RISCV variable undefined"
  return
fi

# Pin the QuestaSim toolchain. Both selectors must agree, else tandem silently
# no-ops: QUESTASIM_HOME (via vsim.mk's `?=`) sets the version the UVM/tandem
# DPI is COMPILED against; PATH (`which vsim`) sets the version that RUNS it.
# If a user's login env points these at different installs (e.g. QUESTASIM_HOME
# 2023.4 but PATH vsim 2022.3), the DPI ABI skew makes tandem never engage.
export QUESTASIM_HOME=/opt/questasim2023.4/questasim
export PATH="$QUESTASIM_HOME/linux_x86_64:$PATH"

echo ">>> vsim in use: $(command -v vsim)"
vsim -version

DV_SIMULATORS=questa-uvm

# Must be exported before the build: drives +define+SPIKE_TANDEM=1 (Spike cosim).
export SPIKE_TANDEM=1

source ./verif/regress/install-spike.sh
source ./verif/sim/setup-env.sh

# vsim loads -sv_lib with LOCAL scope; preload these GLOBAL so libriscv resolves
# YAML::LoadFile and owns the extension registry (else vsim-12005 / "couldn't
# find extension 'cvxif'").
export LD_PRELOAD="$SPIKE_INSTALL_DIR/lib/libyaml-cpp.so:$SPIKE_INSTALL_DIR/lib/libriscv.so${LD_PRELOAD:+:$LD_PRELOAD}"

if ! [ -n "$UVM_VERBOSITY" ]; then
    export UVM_VERBOSITY=UVM_LOW
fi

# questa doesn't auto-inject +tandem_enabled (only VCS/Xcelium do); pass it via
# issrun_opts. Use SPACES not '+': vsim treats "+a=1+b=1" as one plusarg, so
# tandem stays off. Quote it onto the cva6.py call so the spaces survive.
ISSRUN_OPTS="+debug_disable=1 +tandem_enabled=1 +UVM_VERBOSITY=$UVM_VERBOSITY"

CC_OPTS="-static \
         -mcmodel=medany \
         -fvisibility=hidden \
         -nostartfiles \
         -g \
         ../tests/custom/common/syscalls.c \
         ../tests/custom/common/crt.S \
         -I../tests/custom/env \
         -I../tests/custom/common"

cd verif/sim/

# Rebuild so the compile-time +define+SPIKE_TANDEM takes effect.
make -C ../.. clean
make clean_all

python3 cva6.py --c_tests ../tests/custom/hello_world/hello_world.c --iss_yaml cva6.yaml --target cv32a65x --iss=$DV_SIMULATORS --linker=../../config/gen_from_riscv_config/cv32a65x/linker/link.ld --gcc_opts="$CC_OPTS" $DV_OPTS --sv_seed 1 --issrun_opts="$ISSRUN_OPTS"
[[ $? > 0 ]] && ((errors++))

# Tandem result: report must carry instr_count (else tandem did not engage).
REPORT=$(ls -t out_*/questa-uvm_sim/hello_world.cv32a65x.log.yaml 2>/dev/null | head -1)
echo "=== SPIKE TANDEM RESULT ($REPORT) ==="
if grep -q "instr_count" "$REPORT" 2>/dev/null; then
  grep -E "instr_count|mismatches_count|exit_cause" "$REPORT"
  grep -q "mismatches_count: 0" "$REPORT" && echo "[PASS]" || echo "[CHECK] mismatches > 0 (REF=Spike, CORE=RTL)"
else
  echo "[WARN] no instr_count -> tandem did not engage (check +tandem_enabled / SPIKE_TANDEM at compile)"
fi

cd -
