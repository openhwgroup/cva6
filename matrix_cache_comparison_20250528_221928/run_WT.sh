#!/bin/bash
set -x
cd /home/cai/cache_project/sandbox/cva6/verif/sim
source ./setup-env.sh
export PATH=$PATH:/home/cai/cache_project/sandbox/cva6/tools/bin:/usr/bin:/bin
export TRACE_FAST=1
ln -sf ./verilator.vcd hello_world.cv32a60x.vcd
# Copy the signal list to help waveform viewers
cp /home/cai/cache_project/sandbox/cva6/cache_signals.txt matrix_cache_comparison_20250528_221928/wt_results/signals.txt
python3 cva6.py --target cv32a60x --iss=veri-testharness --iss_yaml=cva6.yaml \
--c_tests /home/cai/cache_project/sandbox/cva6/verif/tests/custom/hybrid_cache_test/matrix_cache_test.c \
--linker=../../config/gen_from_riscv_config/linker/link.ld \
--gcc_opts="-static -mcmodel=medany -fvisibility=hidden -nostdlib \
-nostartfiles -g ../tests/custom/common/syscalls.c \
../tests/custom/common/crt.S -lgcc \
-I../tests/custom/env -I../tests/custom/common"

# Copy all simulation artifacts
echo "Copying simulation artifacts..."
newest_dir=$(find ./out_* -type d -name "veri-testharness_sim" -o -name "spike" | sort -r | head -1)
if [ -z "$newest_dir" ]; then
    newest_dir="./veri-testharness_sim"
fi
mkdir -p matrix_cache_comparison_20250528_221928/wt_results/sim_artifacts
cp -R "$newest_dir"/* matrix_cache_comparison_20250528_221928/wt_results/sim_artifacts/ 2>/dev/null || true
cp -R ./out_* matrix_cache_comparison_20250528_221928/wt_results/sim_artifacts/ 2>/dev/null || true
cp ./verilator.vcd matrix_cache_comparison_20250528_221928/wt_results/ 2>/dev/null || true
cp ./trace_* matrix_cache_comparison_20250528_221928/wt_results/ 2>/dev/null || true
cp ./*.log matrix_cache_comparison_20250528_221928/wt_results/ 2>/dev/null || true
if [ -f ./verilator.vcd ]; then
    cp ./verilator.vcd matrix_cache_comparison_20250528_221928/wt_results/hello_world.cv32a60x.vcd
fi
if [ -f ./hello_world.cv32a60x.vcd ]; then
    cp ./hello_world.cv32a60x.vcd matrix_cache_comparison_20250528_221928/wt_results/
fi
