#!/bin/bash

# CVA6 Cache Configuration Test Script
# This script demonstrates how to run hello_world test with different cache configurations

echo "========================================="
echo "CVA6 Cache Configuration Test"
echo "========================================="

# Set environment variables
export CVA6_REPO_DIR=/home/cai/cache_project/sandbox/cva6
export RISCV=/opt/riscv
export VERILATOR_INSTALL_DIR=/usr

# Check required environment variables
if [ -z "$RISCV" ]; then
    echo "Error: RISCV environment variable not set"
    exit 1
fi

echo "Environment setup:"
echo "  CVA6_REPO_DIR: $CVA6_REPO_DIR"
echo "  RISCV: $RISCV"
echo "  VERILATOR_INSTALL_DIR: $VERILATOR_INSTALL_DIR"
echo ""

# Function to run test with specific cache configuration
run_cache_test() {
    local cache_type=$1
    local config_name=$2
    local defines=$3
    
    echo "----------------------------------------"
    echo "Running test with $config_name cache"
    echo "Cache type: $cache_type"
    echo "Defines: $defines"
    echo "----------------------------------------"
    
    # Build verilator model with specific cache configuration
    echo "1. Building Verilator model..."
    make verilate target=cv32a60x defines="$defines"
    
    if [ $? -ne 0 ]; then
        echo "ERROR: Failed to build Verilator model for $config_name"
        return 1
    fi
    
    # Compile hello_world test
    echo "2. Compiling hello_world test..."
    cd verif/tests/custom/hello_world
    
    # Use RISCV toolchain to compile the test
    ${RISCV}/bin/riscv32-unknown-elf-gcc \
        -march=rv32imc \
        -mabi=ilp32 \
        -static \
        -mcmodel=medany \
        -fvisibility=hidden \
        -nostdlib \
        -nostartfiles \
        -I../env \
        -I../common \
        -T../common/test.ld \
        hello_world.c \
        ../common/crt.S \
        ../common/syscalls.c \
        -lgcc \
        -o hello_world_${cache_type}.elf
    
    if [ $? -ne 0 ]; then
        echo "ERROR: Failed to compile hello_world for $config_name"
        cd ../../../../
        return 1
    fi
    
    cd ../../../../
    
    # Run the test
    echo "3. Running simulation..."
    ./work-ver/Variane_testharness verif/tests/custom/hello_world/hello_world_${cache_type}.elf
    
    if [ $? -eq 0 ]; then
        echo "SUCCESS: $config_name test completed successfully"
    else
        echo "ERROR: $config_name test failed"
        return 1
    fi
    
    echo ""
}

echo "========================================="
echo "Test 1: WT (Write-Through) Cache"
echo "========================================="

# Create temporary config file for WT cache
cp core/include/cv32a60x_config_pkg.sv core/include/cv32a60x_config_pkg.sv.backup

# Update config to use WT cache (already set by default)
echo "Using default WT cache configuration..."
run_cache_test "wt" "Write-Through (WT)" ""

echo "========================================="
echo "Test 2: WT_NEW Cache"
echo "========================================="

# Update config to use WT_NEW cache
echo "Updating configuration to use WT_NEW cache..."
sed -i 's/DCacheType: config_pkg::WT,/DCacheType: config_pkg::WT_NEW,/' core/include/cv32a60x_config_pkg.sv

run_cache_test "wt_new" "New Write-Through (WT_NEW)" ""

# Restore original config
echo "Restoring original configuration..."
mv core/include/cv32a60x_config_pkg.sv.backup core/include/cv32a60x_config_pkg.sv

echo "========================================="
echo "Test Summary"
echo "========================================="
echo "Both WT and WT_NEW cache configurations have been tested."
echo "Check the output above for any errors."
echo ""
echo "Key findings:"
echo "- WT cache: Traditional write-through cache implementation"
echo "- WT_NEW cache: New write-through cache with enhanced features"
echo ""
echo "To run tests manually:"
echo "1. For WT cache: make sim-verilator target=cv32a60x elf_file=<your_test.elf>"
echo "2. For WT_NEW cache: modify DCacheType in cv32a60x_config_pkg.sv to WT_NEW, then rebuild"