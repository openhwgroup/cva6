#!/bin/bash
# Script to compare four cache configurations:
# 1. WT - Standard Write-Through
# 2. WT_HYB - Hybrid cache with dynamic privilege-based mode switching
# 3. WT_HYB_FORCE_SET_ASS - Hybrid cache forced to set associative mode
# 4. WT_HYB_FORCE_FULL_ASS - Hybrid cache forced to fully associative mode

set -e

# Create a directory for results with timestamp
TIMESTAMP=$(date +%Y%m%d_%H%M%S)
RESULT_DIR="hybrid_cache_comparison_${TIMESTAMP}"
mkdir -p ${RESULT_DIR}
mkdir -p ${RESULT_DIR}/config_backups
mkdir -p ${RESULT_DIR}/simulation_artifacts

# Make backup of original config files
cp core/include/cv32a60x_config_pkg.sv ${RESULT_DIR}/config_backups/cv32a60x_config_pkg.sv.original
cp core/include/wt_hybrid_cache_pkg.sv ${RESULT_DIR}/config_backups/wt_hybrid_cache_pkg.sv.original

# Define test function
run_cache_test() {
    local CONFIG=$1
    local CONFIG_NAME=$2
    local RESULT_SUBDIR="${RESULT_DIR}/${CONFIG_NAME}"
    
    echo "Running tests with configuration: ${CONFIG_NAME}"
    mkdir -p ${RESULT_SUBDIR}
    
    # Modify config file based on cache type
    case ${CONFIG} in
        WT)
            # Standard Write-Through cache
            sed -i 's/DCacheType: config_pkg::[^,]*/DCacheType: config_pkg::WT/' core/include/cv32a60x_config_pkg.sv
            ;;
        WT_HYB)
            # Hybrid cache with dynamic privilege-based mode switching
            sed -i 's/DCacheType: config_pkg::[^,]*/DCacheType: config_pkg::WT_HYB/' core/include/cv32a60x_config_pkg.sv
            ;;
        WT_HYB_FORCE_SET_ASS)
            # Hybrid cache forced to set associative mode
            sed -i 's/DCacheType: config_pkg::[^,]*/DCacheType: config_pkg::WT_HYB_FORCE_SET_ASS/' core/include/cv32a60x_config_pkg.sv
            ;;
        WT_HYB_FORCE_FULL_ASS)
            # Hybrid cache forced to fully associative mode
            sed -i 's/DCacheType: config_pkg::[^,]*/DCacheType: config_pkg::WT_HYB_FORCE_FULL_ASS/' core/include/cv32a60x_config_pkg.sv
            ;;
    esac
    
    # Save the config file variant
    cp core/include/cv32a60x_config_pkg.sv ${RESULT_SUBDIR}/cv32a60x_config_pkg.sv.${CONFIG}
    
    # Run hello world test
    echo "Running hello_world test..."
    cd verif/sim
    make clean
    make veri-testharness-run HWCONFIG=cv32a60x TB=core TEST=hello_world TRACE=1
    
    # Copy simulation artifacts
    mkdir -p ${RESULT_SUBDIR}/simulation_artifacts
    cp -r out_* ${RESULT_SUBDIR}/simulation_artifacts/
    
    # Run cache_test (specialized test with frequent cache operations)
    echo "Running cache_test..."
    make veri-testharness-run HWCONFIG=cv32a60x TB=core TEST=cache_test TRACE=1
    cp -r out_* ${RESULT_SUBDIR}/simulation_artifacts/
    
    # Run cache thrashing test
    echo "Running cache_thrash test..."
    make veri-testharness-run HWCONFIG=cv32a60x TB=core TEST=cache_thrash TRACE=1
    cp -r out_* ${RESULT_SUBDIR}/simulation_artifacts/
    
    # Return to project root
    cd ../../
    
    echo "Tests completed for ${CONFIG_NAME}"
}

# Run all four configurations
echo "Starting cache configuration comparison..."

# Run WT configuration
run_cache_test "WT" "WT"

# Run WT_HYB configuration
run_cache_test "WT_HYB" "WT_HYB"

# Run WT_HYB_FORCE_SET_ASS configuration
run_cache_test "WT_HYB_FORCE_SET_ASS" "WT_HYB_FORCE_SET_ASS"

# Run WT_HYB_FORCE_FULL_ASS configuration
run_cache_test "WT_HYB_FORCE_FULL_ASS" "WT_HYB_FORCE_FULL_ASS"

# Generate comparison report
echo "Generating comparison report..."
cat > ${RESULT_DIR}/cache_comparison_report.md << EOF
# Hybrid Cache Configuration Comparison

This report compares the performance and behavior of four cache configurations:

1. **WT**: Standard Write-Through cache
2. **WT_HYB**: Hybrid cache with dynamic privilege-based mode switching 
   - Uses set associative mode in Machine Mode
   - Uses fully associative mode in Supervisor/User Mode
3. **WT_HYB_FORCE_SET_ASS**: Hybrid cache forced to set associative mode
4. **WT_HYB_FORCE_FULL_ASS**: Hybrid cache forced to fully associative mode

## Test Results

Tests were run with the following benchmarks:
- hello_world: Basic functionality test
- cache_test: Test with frequent cache operations
- cache_thrash: Test designed to create cache thrashing

## Performance Comparison

| Configuration | hello_world (cycles) | cache_test (cycles) | cache_thrash (cycles) | Avg. Cache Hits (%) |
|---------------|----------------------|---------------------|------------------------|---------------------|
| WT            | See test logs        | See test logs       | See test logs          | See test logs       |
| WT_HYB        | See test logs        | See test logs       | See test logs          | See test logs       |
| WT_HYB_FORCE_SET_ASS | See test logs | See test logs       | See test logs          | See test logs       |
| WT_HYB_FORCE_FULL_ASS | See test logs | See test logs      | See test logs          | See test logs       |

## Isolation Analysis

The hybrid cache design aims to improve isolation between privilege levels by using
fully associative mode for Supervisor/User modes. The following aspects were analyzed:

1. **Cache Thrashing Impact**: How cache thrashing in one privilege level affects another
2. **Context Switch Overhead**: Cost of switching cache organization on privilege changes
3. **Security Benefit**: Improved resistance to cache side-channel attacks

## Conclusion

(To be filled in after analyzing test results)

EOF

echo "Cache configuration comparison completed. Results are in: ${RESULT_DIR}"
echo "Running automated analysis..."
python3 analyze_hybrid_cache.py "${RESULT_DIR}" --output "${RESULT_DIR}/analysis"
echo "Analysis completed. Report available in ${RESULT_DIR}/analysis"

# Automatically generate the detailed analysis report
python3 analyze_hybrid_cache.py "${RESULT_DIR}" --output "${RESULT_DIR}/analysis"

echo "Detailed analysis generated under ${RESULT_DIR}/analysis"

# Restore original configuration
cp ${RESULT_DIR}/config_backups/cv32a60x_config_pkg.sv.original core/include/cv32a60x_config_pkg.sv

echo "Original configuration restored"
