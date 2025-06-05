# CVA6 Cache Configuration Testing - Complete Guide

## Overview

This guide provides the complete information needed to run simple tests like `hello_world` with both WT (Write-Through) and WT_NEW (New Write-Through) cache configurations using the Verilator testharness in the CVA6 RISC-V processor.

## Current Environment Setup

Based on the analysis of your CVA6 repository structure:

- **Repository**: `/home/cai/cache_project/sandbox/cva6`
- **Current branch**: `wt_new`
- **Verilator model**: Already built at `work-ver/Variane_testharness`
- **Modified file**: `core/include/cv32a60x_config_pkg.sv` (shows WT_NEW integration)

## Available Cache Types

The cache types are defined in `core/include/config_pkg.sv` (lines 30-40):

```systemverilog
typedef enum logic [3:0] {
    WB = 0,
    WT = 1,                    // Traditional Write-Through
    HPDCACHE_WT = 2,
    HPDCACHE_WB = 3,
    HPDCACHE_WT_WB = 4,
    WT_HYB = 5,
    WT_HYB_FORCE_SET_ASS = 6,
    WT_HYB_FORCE_FULL_ASS = 7,
    WT_NEW = 8                 // New Write-Through (enhanced)
} cache_type_t;
```

## Configuration File Location

- **Target configuration**: `core/include/cv32a60x_config_pkg.sv`
- **Key parameter**: `DCacheType: config_pkg::WT,` (line 92)

## Method 1: Quick Test Commands

### Test with WT Cache (Traditional)

```bash
# 1. Ensure WT cache configuration (default)
# Check that line 92 in cv32a60x_config_pkg.sv shows:
# DCacheType: config_pkg::WT,

# 2. Clean and build
make clean
make verilate target=cv32a60x

# 3. Run hello_world test (using existing dhrystone as example)
make sim-verilator target=cv32a60x elf_file=tmp/riscv-tests/build/benchmarks/dhrystone.riscv
```

### Test with WT_NEW Cache (Enhanced)

```bash
# 1. Update configuration to WT_NEW
sed -i 's/DCacheType: config_pkg::WT,/DCacheType: config_pkg::WT_NEW,/' core/include/cv32a60x_config_pkg.sv

# 2. Clean and build
make clean
make verilate target=cv32a60x

# 3. Run the same test
make sim-verilator target=cv32a60x elf_file=tmp/riscv-tests/build/benchmarks/dhrystone.riscv

# 4. Restore original configuration
sed -i 's/DCacheType: config_pkg::WT_NEW,/DCacheType: config_pkg::WT,/' core/include/cv32a60x_config_pkg.sv
```

## Method 2: Using Verification Framework

Navigate to the verification simulation directory:

```bash
cd verif/sim
```

### For WT Cache:
```bash
python3 cva6.py \
    --target cv32a60x \
    --iss veri-testharness \
    --iss_yaml cva6.yaml \
    --c_tests ../tests/custom/hello_world/hello_world.c \
    --gcc_opts "-static -mcmodel=medany -fvisibility=hidden -nostdlib -nostartfiles -I../tests/custom/env -I../tests/custom/common -lgcc"
```

### For WT_NEW Cache:
Update the configuration as shown above, then run the same command.

## Method 3: Direct Executable Test

If you have the Verilator model built:

```bash
# Run a pre-built test directly
./work-ver/Variane_testharness tmp/riscv-tests/build/benchmarks/dhrystone.riscv
```

## Key Make Targets Summary

| Target | Description |
|--------|-------------|
| `make clean` | Clean all build artifacts |
| `make verilate target=cv32a60x` | Build Verilator simulation model |
| `make sim-verilator target=cv32a60x elf_file=<path>` | Run simulation with specific ELF |

## Configuration Parameters

In `cv32a60x_config_pkg.sv`, key cache-related parameters:

```systemverilog
DCacheType: config_pkg::WT,           // WT or WT_NEW
DcacheByteSize: unsigned'(2028),      // Cache size: 2KB
DcacheSetAssoc: unsigned'(2),         // 2-way set associative
DcacheLineWidth: unsigned'(128),      // 128-bit cache lines
WtDcacheWbufDepth: int'(8),          // Write buffer depth: 8 entries
```

## Expected Test Flow

1. **Build Phase**: Verilator compiles the RTL with specified cache configuration
2. **Simulation Phase**: Test ELF is loaded and executed
3. **Output**: Console shows test execution progress and results
4. **Completion**: Simulation exits with success/failure status

## Cache Performance Analysis

To compare WT vs WT_NEW performance:

1. **Functional Verification**: Both should produce identical functional results
2. **Performance Metrics**: May differ in cache efficiency, memory bandwidth utilization
3. **Timing**: WT_NEW may show improved timing characteristics

## Available Test ELF Files

Common test files you can use:

- `tmp/riscv-tests/build/benchmarks/dhrystone.riscv` - Performance benchmark
- `verif/tests/custom/hello_world/hello_world.c` - Simple hello world (needs compilation)

## Troubleshooting

### Common Issues:

1. **Environment Variables**: Ensure `RISCV` toolchain path is set
2. **Build Failures**: Check Verilator installation and version compatibility
3. **Configuration Errors**: Verify SystemVerilog syntax after manual edits
4. **Simulation Hangs**: Check test compatibility with target configuration

### Debug Steps:

1. Verify configuration changes: `grep "DCacheType" core/include/cv32a60x_config_pkg.sv`
2. Check build success: Look for `work-ver/Variane_testharness` executable
3. Monitor simulation: Add debug flags if available

## Current Repository Status

Your repository shows evidence of WT_NEW cache integration work:
- Modified `cv32a60x_config_pkg.sv` 
- Various test outputs in `verif/sim/out_*` directories
- Recent commits related to WT_NEW cache integration

This demonstrates that the WT_NEW cache implementation is already integrated and ready for testing with the commands provided above.

## Quick Verification Commands

To quickly verify both cache configurations work:

```bash
# Backup current config
cp core/include/cv32a60x_config_pkg.sv core/include/cv32a60x_config_pkg.sv.backup

# Test WT cache
echo "Testing WT cache..."
make clean && make verilate target=cv32a60x
timeout 300 make sim-verilator target=cv32a60x elf_file=tmp/riscv-tests/build/benchmarks/dhrystone.riscv

# Test WT_NEW cache  
echo "Testing WT_NEW cache..."
sed -i 's/DCacheType: config_pkg::WT,/DCacheType: config_pkg::WT_NEW,/' core/include/cv32a60x_config_pkg.sv
make clean && make verilate target=cv32a60x
timeout 300 make sim-verilator target=cv32a60x elf_file=tmp/riscv-tests/build/benchmarks/dhrystone.riscv

# Restore config
mv core/include/cv32a60x_config_pkg.sv.backup core/include/cv32a60x_config_pkg.sv
```

This provides a complete workflow for testing both WT and WT_NEW cache configurations with the CVA6 Verilator testharness.