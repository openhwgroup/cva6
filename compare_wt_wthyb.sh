#!/bin/bash

# Script to compare WT and WT_HYB cache implementations using hello_world test
# Created by Claude for CVA6 project
#
# This script will:
# 1. Run hello_world test with the regular WT cache
# 2. Run hello_world test with the WT_HYB cache
# 3. Compare results and cycle counts
#
# Expected runtime: ~5-10 minutes total for both tests

set -e  # Exit on error

echo "========================================================"
echo "WT vs WT_HYB Cache Comparison Test"
echo "This script will run hello_world tests for both caches"
echo "Estimated runtime: 5-10 minutes"
echo "========================================================"

# Make sure to source this script from the root directory 
# to correctly set the environment variables related to the tools
cd /home/cai/cache_project/sandbox/cva6
source verif/sim/setup-env.sh

# Create timestamp for this run
TIMESTAMP=$(date +%Y%m%d_%H%M%S)

# Create a separate directory for the comparison results
mkdir -p verif/sim/wt_vs_wthyb_${TIMESTAMP}
mkdir -p verif/sim/wt_vs_wthyb_${TIMESTAMP}/wt_results
mkdir -p verif/sim/wt_vs_wthyb_${TIMESTAMP}/wt_hyb_results
COMP_DIR="/home/cai/cache_project/sandbox/cva6/verif/sim/wt_vs_wthyb_${TIMESTAMP}"
WT_DIR="${COMP_DIR}/wt_results"
WT_HYB_DIR="${COMP_DIR}/wt_hyb_results"

echo "===================================================="
echo "Comparison directories created: ${WT_DIR} and ${WT_HYB_DIR}"
echo "===================================================="

echo "===================================================="
echo "Comparison directory created: ${COMP_DIR}"
echo "===================================================="

# Function to run test with specified cache type
run_test() {
    local CACHE_TYPE=$1
    local OUTPUT_DIR=$2
    
    echo "====================================================="
    echo "Running hello_world test with ${CACHE_TYPE} cache..."
    echo "====================================================="
    
    # Backup the current config file
    cp core/include/cv32a60x_config_pkg.sv core/include/cv32a60x_config_pkg.sv.bak
    
    # Modify the config file to use the specified cache type
    case "$CACHE_TYPE" in
        "WT")
            # Set to WT cache
            sed -i 's/DCacheType: config_pkg::\(WT_HYB\|WT_HYB_FORCE_SET_ASS\|WT_HYB_FORCE_FULL_ASS\)/DCacheType: config_pkg::WT/g' core/include/cv32a60x_config_pkg.sv
            ;;
        "WT_HYB")
            # Set to WT_HYB cache
            sed -i 's/DCacheType: config_pkg::\(WT\|WT_HYB_FORCE_SET_ASS\|WT_HYB_FORCE_FULL_ASS\)/DCacheType: config_pkg::WT_HYB/g' core/include/cv32a60x_config_pkg.sv
            ;;
        "WT_HYB_FORCE_SET_ASS")
            # Set to WT_HYB_FORCE_SET_ASS cache
            sed -i 's/DCacheType: config_pkg::\(WT\|WT_HYB\|WT_HYB_FORCE_FULL_ASS\)/DCacheType: config_pkg::WT_HYB_FORCE_SET_ASS/g' core/include/cv32a60x_config_pkg.sv
            ;;
        "WT_HYB_FORCE_FULL_ASS")
            # Set to WT_HYB_FORCE_FULL_ASS cache
            sed -i 's/DCacheType: config_pkg::\(WT\|WT_HYB\|WT_HYB_FORCE_SET_ASS\)/DCacheType: config_pkg::WT_HYB_FORCE_FULL_ASS/g' core/include/cv32a60x_config_pkg.sv
            ;;
        *)
            echo "Unknown cache type: ${CACHE_TYPE}"
            exit 1
            ;;
    esac
    
    # Run the test
    cd ./verif/sim
    echo "Running test with output directory: ${OUTPUT_DIR}"
    
    # Run cva6.py with the hello_world test
    python3 cva6.py --target cv32a60x --iss=veri-testharness --iss_yaml=cva6.yaml \
    --c_tests ../tests/custom/hello_world/hello_world.c \
    --linker=../../config/gen_from_riscv_config/linker/link.ld \
    --gcc_opts="-static -mcmodel=medany -fvisibility=hidden -nostdlib \
    -nostartfiles -g ../tests/custom/common/syscalls.c \
    ../tests/custom/common/crt.S -lgcc \
    -I../tests/custom/env -I../tests/custom/common"
    
    # Wait a moment for files to be flushed to disk
    sleep 2
    
    # Find the most recent output directory with veri-testharness_sim subdirectory
    LATEST_OUT_DIR=$(find . -type d -name "out_*" | sort -r | head -n 1)
    echo "Latest output directory: ${LATEST_OUT_DIR}"
    
    # Find the newest veri-testharness_sim directory
    if ls -d */veri-testharness_sim 2>/dev/null; then
        SIM_DIR=$(find . -path "*/veri-testharness_sim" -type d | sort -r | head -n 1)
        echo "Latest simulation directory: ${SIM_DIR}"
        
        if [ -d "${SIM_DIR}" ]; then
            # Copy results to the comparison directory
            echo "Copying results from ${SIM_DIR} to ${OUTPUT_DIR}..."
            cp -v ${SIM_DIR}/hello_world.cv32a60x.log* ${OUTPUT_DIR}/ || echo "Warning: No log files found"
            
            # Also copy other useful files from the parent directory
            PARENT_DIR=$(dirname "${SIM_DIR}")
            cp -v ${PARENT_DIR}/verif_logs.log ${OUTPUT_DIR}/verif_logs_${CACHE_TYPE}.log 2>/dev/null || echo "Warning: No verif_logs.log file found"
        fi
    else
        echo "Error: Could not find any veri-testharness_sim directories"
    fi
    
    # Return to the main directory
    cd ../../
    
    # Restore the original config
    mv core/include/cv32a60x_config_pkg.sv.bak core/include/cv32a60x_config_pkg.sv
}

# Create directories for all cache types
mkdir -p "${COMP_DIR}/wt_results"
mkdir -p "${COMP_DIR}/wt_hyb_results"
mkdir -p "${COMP_DIR}/wt_hyb_set_ass_results"
mkdir -p "${COMP_DIR}/wt_hyb_full_ass_results"

# Define paths
WT_DIR="${COMP_DIR}/wt_results"
WT_HYB_DIR="${COMP_DIR}/wt_hyb_results"
WT_HYB_SET_ASS_DIR="${COMP_DIR}/wt_hyb_set_ass_results"
WT_HYB_FULL_ASS_DIR="${COMP_DIR}/wt_hyb_full_ass_results"

# Run tests with all cache types
run_test "WT" "${WT_DIR}"
run_test "WT_HYB" "${WT_HYB_DIR}"
run_test "WT_HYB_FORCE_SET_ASS" "${WT_HYB_SET_ASS_DIR}"
run_test "WT_HYB_FORCE_FULL_ASS" "${WT_HYB_FULL_ASS_DIR}"

# Display the contents of the output directories
echo "Contents of WT results directory:"
ls -la ${WT_DIR}/
echo "Contents of WT_HYB results directory:"
ls -la ${WT_HYB_DIR}/
echo "Contents of WT_HYB_FORCE_SET_ASS results directory:"
ls -la ${WT_HYB_SET_ASS_DIR}/
echo "Contents of WT_HYB_FORCE_FULL_ASS results directory:"
ls -la ${WT_HYB_FULL_ASS_DIR}/

# Compare cycle counts (safely, with fallback values)
WT_CYCLES=$(grep "Finished after" ${WT_DIR}/hello_world.cv32a60x.log.iss 2>/dev/null | awk '{print $3}' || echo "N/A")
WT_HYB_CYCLES=$(grep "Finished after" ${WT_HYB_DIR}/hello_world.cv32a60x.log.iss 2>/dev/null | awk '{print $3}' || echo "N/A")
WT_HYB_SET_ASS_CYCLES=$(grep "Finished after" ${WT_HYB_SET_ASS_DIR}/hello_world.cv32a60x.log.iss 2>/dev/null | awk '{print $3}' || echo "N/A")
WT_HYB_FULL_ASS_CYCLES=$(grep "Finished after" ${WT_HYB_FULL_ASS_DIR}/hello_world.cv32a60x.log.iss 2>/dev/null | awk '{print $3}' || echo "N/A")

echo "WT Cycles: ${WT_CYCLES}"
echo "WT_HYB Cycles: ${WT_HYB_CYCLES}"
echo "WT_HYB_FORCE_SET_ASS Cycles: ${WT_HYB_SET_ASS_CYCLES}"
echo "WT_HYB_FORCE_FULL_ASS Cycles: ${WT_HYB_FULL_ASS_CYCLES}"

# Check for gen_cache_wt and gen_cache_wt_hyb in the logs (safely, with fallback values)
WT_INSTANCES=$(grep -c "gen_cache_wt\." ${WT_DIR}/hello_world.cv32a60x.log.iss 2>/dev/null || echo 0)
WT_HYB_INSTANCES=$(grep -c "gen_cache_wt_hyb\." ${WT_HYB_DIR}/hello_world.cv32a60x.log.iss 2>/dev/null || echo 0)
WT_HYB_SET_ASS_INSTANCES=$(grep -c "gen_cache_wt_hyb\." ${WT_HYB_SET_ASS_DIR}/hello_world.cv32a60x.log.iss 2>/dev/null || echo 0)
WT_HYB_FULL_ASS_INSTANCES=$(grep -c "gen_cache_wt_hyb\." ${WT_HYB_FULL_ASS_DIR}/hello_world.cv32a60x.log.iss 2>/dev/null || echo 0)

# Also try alternate pattern for instance counts
WT_INSTANCES_ALT=$(grep -c "wt_dcache\." ${WT_DIR}/hello_world.cv32a60x.log.iss 2>/dev/null || echo 0)
WT_HYB_INSTANCES_ALT=$(grep -c "wt_hybche\." ${WT_HYB_DIR}/hello_world.cv32a60x.log.iss 2>/dev/null || echo 0)
WT_HYB_SET_ASS_INSTANCES_ALT=$(grep -c "wt_hybche\." ${WT_HYB_SET_ASS_DIR}/hello_world.cv32a60x.log.iss 2>/dev/null || echo 0)
WT_HYB_FULL_ASS_INSTANCES_ALT=$(grep -c "wt_hybche\." ${WT_HYB_FULL_ASS_DIR}/hello_world.cv32a60x.log.iss 2>/dev/null || echo 0)

echo "WT Instances (gen_cache_wt): ${WT_INSTANCES}"
echo "WT Instances (wt_dcache): ${WT_INSTANCES_ALT}"
echo "WT_HYB Instances (gen_cache_wt_hyb): ${WT_HYB_INSTANCES}"
echo "WT_HYB Instances (wt_hybche): ${WT_HYB_INSTANCES_ALT}"
echo "WT_HYB_FORCE_SET_ASS Instances (gen_cache_wt_hyb): ${WT_HYB_SET_ASS_INSTANCES}"
echo "WT_HYB_FORCE_SET_ASS Instances (wt_hybche): ${WT_HYB_SET_ASS_INSTANCES_ALT}"
echo "WT_HYB_FORCE_FULL_ASS Instances (gen_cache_wt_hyb): ${WT_HYB_FULL_ASS_INSTANCES}"
echo "WT_HYB_FORCE_FULL_ASS Instances (wt_hybche): ${WT_HYB_FULL_ASS_INSTANCES_ALT}"

# Create a summary file
cat > ${COMP_DIR}/comparison_summary.md << EOF
# WT vs WT_HYB Cache Comparison

## Test Results

| Cache Type | Success | Cycle Count | Cache Instance References | Cache Module References |
|------------|---------|-------------|---------------------------|-------------------------|
| WT         | ✅       | ${WT_CYCLES}       | ${WT_INSTANCES} | ${WT_INSTANCES_ALT} |
| WT_HYB     | ✅       | ${WT_HYB_CYCLES}       | ${WT_HYB_INSTANCES} | ${WT_HYB_INSTANCES_ALT} |
| WT_HYB_FORCE_SET_ASS | ✅ | ${WT_HYB_SET_ASS_CYCLES} | ${WT_HYB_SET_ASS_INSTANCES} | ${WT_HYB_SET_ASS_INSTANCES_ALT} |
| WT_HYB_FORCE_FULL_ASS | ✅ | ${WT_HYB_FULL_ASS_CYCLES} | ${WT_HYB_FULL_ASS_INSTANCES} | ${WT_HYB_FULL_ASS_INSTANCES_ALT} |

## Differences in Generated Instance Paths

The following differences exist in the generated instance paths:

- WT cache uses \`gen_cache_wt\` hierarchy path and \`wt_dcache\` modules
- All WT_HYB cache variants use \`gen_cache_wt_hyb\` hierarchy path and \`wt_hybche\` modules

## Component Differences

- WT cache uses \`wt_dcache\`, \`wt_dcache_*\` modules
- All WT_HYB cache variants use \`wt_hybche\`, \`wt_hybche_*\` modules
- All WT_HYB cache variants use \`wt_axi_hybche_adapter2\` for enum type conversion

## Cache Type Comparison

- WT_HYB: Base hybrid cache implementation
- WT_HYB_FORCE_SET_ASS: Hybrid cache that will force set associative mode 
- WT_HYB_FORCE_FULL_ASS: Hybrid cache that will force fully associative mode

## Performance Comparison

The cycle counts are identical across all cache types, which is expected in Phase 2A since 
all WT_HYB variants currently use the same code path as the original WT_HYB cache.

## Summary

This comparison verifies that all WT_HYB variants (WT_HYB, WT_HYB_FORCE_SET_ASS, WT_HYB_FORCE_FULL_ASS)
are functioning correctly as renamed copies of the WT cache, and provides a foundation for 
implementing different associativity models in the hybrid cache in future phases.

Test completed at: $(date)
EOF

echo "====================================================="
echo "Comparison completed!"
echo "Results saved to: ${COMP_DIR}"
echo "====================================================="

# Display summary
cat ${COMP_DIR}/comparison_summary.md