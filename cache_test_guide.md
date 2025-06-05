# CVA6 Cache Configuration Testing Guide

This guide shows how to run simple tests like `hello_world` with both WT and WT_NEW cache configurations using the Verilator testharness.

## Prerequisites

Ensure you have the following environment variables set:
```bash
export CVA6_REPO_DIR=/home/cai/cache_project/sandbox/cva6
export RISCV=/opt/riscv  # Path to your RISC-V toolchain
export VERILATOR_INSTALL_DIR=/usr  # Path to Verilator installation
```

## Available Cache Types

The CVA6 supports multiple cache types defined in `core/include/config_pkg.sv`:
- `WT = 1` - Write-Through cache (traditional)
- `WT_NEW = 8` - New Write-Through cache (enhanced implementation)

## Configuration Files

Cache configuration is controlled by the target-specific config package. For cv32a60x:
- Configuration file: `core/include/cv32a60x_config_pkg.sv`
- Key parameter: `DCacheType: config_pkg::WT` (line 92)

## Method 1: Using Direct Make Commands

### Step 1: Test with WT Cache (Default Configuration)

```bash
# Build Verilator model with WT cache (default)
make verilate target=cv32a60x

# Run hello_world test
make sim-verilator target=cv32a60x elf_file=tmp/riscv-tests/build/benchmarks/dhrystone.riscv
```

### Step 2: Test with WT_NEW Cache

```bash
# 1. Backup current config
cp core/include/cv32a60x_config_pkg.sv core/include/cv32a60x_config_pkg.sv.backup

# 2. Update cache type to WT_NEW
sed -i 's/DCacheType: config_pkg::WT,/DCacheType: config_pkg::WT_NEW,/' core/include/cv32a60x_config_pkg.sv

# 3. Clean and rebuild
make clean
make verilate target=cv32a60x

# 4. Run test
make sim-verilator target=cv32a60x elf_file=tmp/riscv-tests/build/benchmarks/dhrystone.riscv

# 5. Restore original config
mv core/include/cv32a60x_config_pkg.sv.backup core/include/cv32a60x_config_pkg.sv
```

## Method 2: Using the Verification Framework

### Step 1: Navigate to simulation directory
```bash
cd verif/sim
```

### Step 2: Run with verification framework

For WT cache:
```bash
python3 cva6.py \
    --target cv32a60x \
    --iss veri-testharness \
    --iss_yaml cva6.yaml \
    --c_tests ../tests/custom/hello_world/hello_world.c \
    --gcc_opts "-static -mcmodel=medany -fvisibility=hidden -nostdlib -nostartfiles -I../tests/custom/env -I../tests/custom/common -lgcc"
```

For WT_NEW cache:
```bash
# Update config as shown in Method 1, then run the same command
```

## Method 3: Manual Test Compilation and Execution

### Step 1: Compile a test manually
```bash
cd verif/tests/custom/hello_world

# Compile hello_world test
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
    hello_world.c \
    ../common/crt.S \
    ../common/syscalls.c \
    -lgcc \
    -o hello_world.elf

cd ../../../../
```

### Step 2: Run the test
```bash
# Make sure Verilator model is built
make verilate target=cv32a60x

# Run the test
./work-ver/Variane_testharness verif/tests/custom/hello_world/hello_world.elf
```

## Key Make Targets

- `make verilate target=cv32a60x` - Build Verilator simulation model
- `make sim-verilator target=cv32a60x elf_file=<path>` - Run simulation with specific ELF
- `make clean` - Clean build artifacts

## Configuration Parameters for Cache Testing

In `cv32a60x_config_pkg.sv`, key cache-related parameters:

```systemverilog
DCacheType: config_pkg::WT,           // Cache type: WT or WT_NEW
DcacheByteSize: unsigned'(2028),      // Cache size in bytes
DcacheSetAssoc: unsigned'(2),         // Set associativity
DcacheLineWidth: unsigned'(128),      // Cache line width
WtDcacheWbufDepth: int'(8),          // Write buffer depth
```

## Expected Output

Successful test execution should show:
- Simulation starts
- Hello World message output
- Test completion without errors
- Return code 0

## Troubleshooting

1. **Build failures**: Check that RISCV toolchain is properly installed
2. **Simulation hangs**: Check that the ELF file is compatible with the target configuration
3. **Cache configuration errors**: Verify the config_pkg.sv syntax after modifications

## Performance Comparison

To compare cache performance:
1. Run the same test with both configurations
2. Check simulation time and cycle count
3. Analyze cache hit/miss statistics if available
4. Compare memory access patterns

This demonstrates the practical differences between WT and WT_NEW cache implementations in CVA6.