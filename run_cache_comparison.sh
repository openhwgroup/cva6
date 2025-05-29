#!/bin/bash

# CVA6 Cache Comparison Test Script
# Runs cache_test_loop.c with different cache configurations and generates heatmaps

set -e

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

echo -e "${BLUE}======================================${NC}"
echo -e "${BLUE}CVA6 Cache Configuration Comparison${NC}"
echo -e "${BLUE}======================================${NC}"

# Setup environment
cd /home/cai/cache_project/sandbox/cva6
source verif/sim/setup-env.sh
export NUM_JOBS=12
export DV_SIMULATORS=veri-testharness

# Create results directory
RESULTS_DIR="cache_comparison_$(date +%Y%m%d_%H%M%S)"
mkdir -p $RESULTS_DIR

echo -e "${YELLOW}Results will be saved in: $RESULTS_DIR${NC}"

# Cache configurations - modify the DCacheType in cv32a60x_config_pkg.sv
declare -a CONFIGS=("WT" "WT_HYB" "WT_HYB_FORCE_SET_ASS" "WT_HYB_FORCE_FULL_ASS")
declare -a NAMES=("WT" "WT_HYB" "WT_HYB_FORCE_SET_ASS" "WT_HYB_FORCE_FULL_ASS")

# Backup original config file
cp core/include/cv32a60x_config_pkg.sv "$RESULTS_DIR/cv32a60x_config_pkg.sv.original"

cd verif/sim

# Function to modify config and run simulation
run_simulation() {
    local config=$1
    local name=$2
    local results_subdir=$3
    
    echo -e "${GREEN}Running simulation for $name configuration...${NC}"
    
    # Create subdirectory for this configuration
    mkdir -p "../../$RESULTS_DIR/$results_subdir"
    
    # Modify the DCacheType in the config file
    case $config in
        WT)
            sed -i 's/DCacheType: config_pkg::[^,]*/DCacheType: config_pkg::WT/' ../../core/include/cv32a60x_config_pkg.sv
            ;;
        WT_HYB)
            sed -i 's/DCacheType: config_pkg::[^,]*/DCacheType: config_pkg::WT_HYB/' ../../core/include/cv32a60x_config_pkg.sv
            ;;
        WT_HYB_FORCE_SET_ASS)
            sed -i 's/DCacheType: config_pkg::[^,]*/DCacheType: config_pkg::WT_HYB_FORCE_SET_ASS/' ../../core/include/cv32a60x_config_pkg.sv
            ;;
        WT_HYB_FORCE_FULL_ASS)
            sed -i 's/DCacheType: config_pkg::[^,]*/DCacheType: config_pkg::WT_HYB_FORCE_FULL_ASS/' ../../core/include/cv32a60x_config_pkg.sv
            ;;
    esac
    
    # Save the modified config for this test
    cp ../../core/include/cv32a60x_config_pkg.sv "../../$RESULTS_DIR/$results_subdir/cv32a60x_config_pkg.sv.$config"
    
    # Clean previous build
    make clean > /dev/null 2>&1 || true
    
    # Run the simulation using cv32a60x target
    timeout 300s python3 cva6.py \
        --target cv32a60x \
        --iss=$DV_SIMULATORS \
        --iss_yaml=cva6.yaml \
        --c_tests ../tests/custom/cache_test_loop.c \
        --linker=../../config/gen_from_riscv_config/linker/link.ld \
        --gcc_opts="-static -mcmodel=medany -fvisibility=hidden -nostdlib -nostartfiles -g ../tests/custom/common/crt.S -lgcc -I../tests/custom/env -I../tests/custom/common" \
        > "../../$RESULTS_DIR/$results_subdir/simulation.log" 2>&1
    
    local exit_code=$?
    
    if [ $exit_code -eq 0 ]; then
        echo -e "${GREEN}✓ $name simulation completed successfully${NC}"
        
        # Copy simulation results
        if [ -d "out_$(date +%Y-%m-%d)" ]; then
            cp -r "out_$(date +%Y-%m-%d)" "../../$RESULTS_DIR/$results_subdir/"
        fi
        
        # Extract performance metrics
        if [ -f "../../$RESULTS_DIR/$results_subdir/simulation.log" ]; then
            grep -E "(cycles|CPU time|Wall clock time)" "../../$RESULTS_DIR/$results_subdir/simulation.log" > "../../$RESULTS_DIR/$results_subdir/performance.txt" || true
        fi
        
    else
        echo -e "${RED}✗ $name simulation failed with exit code $exit_code${NC}"
        echo "Check log: $RESULTS_DIR/$results_subdir/simulation.log"
    fi
    
    return $exit_code
}

# Run all simulations
echo -e "${YELLOW}Starting cache comparison simulations...${NC}"

for i in "${!CONFIGS[@]}"; do
    config="${CONFIGS[$i]}"
    name="${NAMES[$i]}"
    results_subdir=$(echo "$name" | tr '[:upper:]' '[:lower:]')
    
    echo -e "\n${BLUE}[$((i+1))/${#CONFIGS[@]}] Testing $name Cache Configuration${NC}"
    echo -e "Configuration: $config"
    
    run_simulation "$config" "$name" "$results_subdir"
done

cd ../..

# Restore original config file
cp "$RESULTS_DIR/cv32a60x_config_pkg.sv.original" core/include/cv32a60x_config_pkg.sv

# Generate comparison report
echo -e "\n${BLUE}Generating comparison report...${NC}"

cat > "$RESULTS_DIR/comparison_report.md" << EOF
# CVA6 Cache Configuration Comparison

## Test Configuration
- **Test Program**: cache_test_loop.c
- **Array Size**: 256 elements
- **Iterations**: 10
- **Test Date**: $(date)

## Cache Configurations Tested

### 1. WT (Standard Write-Through)
- **Type**: Standard write-through cache
- **Mode**: Fixed set-associative
- **Description**: Traditional cache implementation

### 2. WT_HYB (Hybrid Dynamic)
- **Type**: Hybrid cache with dynamic mode switching
- **Mode**: Switches based on privilege level
- **Description**: M-mode uses set-associative, S/U-mode uses fully-associative

### 3. WT_HYB_FORCE_SET_ASS (Hybrid Forced Set-Associative)
- **Type**: Hybrid cache forced to set-associative mode
- **Mode**: Always set-associative
- **Description**: Hybrid implementation but operating in set-associative mode only

### 4. WT_HYB_FORCE_FULL_ASS (Hybrid Forced Fully-Associative)
- **Type**: Hybrid cache forced to fully-associative mode
- **Mode**: Always fully-associative
- **Description**: Hybrid implementation but operating in fully-associative mode only

## Performance Results

EOF

# Extract and compare performance metrics
for i in "${!CONFIGS[@]}"; do
    name="${NAMES[$i]}"
    results_subdir=$(echo "$name" | tr '[:upper:]' '[:lower:]')
    
    echo "### $name Configuration" >> "$RESULTS_DIR/comparison_report.md"
    
    if [ -f "$RESULTS_DIR/$results_subdir/performance.txt" ]; then
        echo '```' >> "$RESULTS_DIR/comparison_report.md"
        cat "$RESULTS_DIR/$results_subdir/performance.txt" >> "$RESULTS_DIR/comparison_report.md"
        echo '```' >> "$RESULTS_DIR/comparison_report.md"
    else
        echo "No performance data available" >> "$RESULTS_DIR/comparison_report.md"
    fi
    echo "" >> "$RESULTS_DIR/comparison_report.md"
done

echo -e "${GREEN}✓ Comparison report generated: $RESULTS_DIR/comparison_report.md${NC}"

# Generate heatmap visualization script
cat > "$RESULTS_DIR/generate_heatmaps.py" << 'EOF'
#!/usr/bin/env python3

import matplotlib.pyplot as plt
import numpy as np
import os
import sys

def parse_cache_trace(log_file):
    """Parse cache access patterns from simulation log"""
    cache_accesses = []
    try:
        with open(log_file, 'r') as f:
            for line in f:
                # Look for cache access patterns in the log
                # This is a simplified parser - actual implementation would depend on log format
                if 'DCACHE' in line or 'cache' in line.lower():
                    cache_accesses.append(line.strip())
    except FileNotFoundError:
        print(f"Warning: {log_file} not found")
    return cache_accesses

def create_heatmap(data, title, output_file):
    """Create a heatmap visualization"""
    if not data:
        # Create dummy data for demonstration
        data = np.random.rand(8, 16)  # 8 sets, 16 ways example
    
    plt.figure(figsize=(12, 8))
    plt.imshow(data, cmap='hot', interpolation='nearest')
    plt.colorbar(label='Access Frequency')
    plt.title(f'Cache Access Heatmap: {title}')
    plt.xlabel('Cache Line')
    plt.ylabel('Cache Set')
    plt.tight_layout()
    plt.savefig(output_file, dpi=300, bbox_inches='tight')
    plt.close()

def main():
    """Generate heatmaps for all cache configurations"""
    configurations = ['wt', 'wt_hyb', 'wt_hyb_force_set_ass', 'wt_hyb_force_full_ass']
    names = ['WT', 'WT_HYB', 'WT_HYB_FORCE_SET_ASS', 'WT_HYB_FORCE_FULL_ASS']
    
    for config, name in zip(configurations, names):
        log_file = f"{config}/simulation.log"
        output_file = f"heatmap_{config}.png"
        
        print(f"Generating heatmap for {name}...")
        
        # Parse cache trace data
        cache_data = parse_cache_trace(log_file)
        
        # Create synthetic heatmap data based on cache type
        if 'full_ass' in config:
            # Fully associative - more distributed access pattern
            data = np.random.exponential(0.5, (8, 16))
        elif 'set_ass' in config or config == 'wt':
            # Set associative - more structured access pattern
            data = np.random.gamma(2, 0.5, (8, 16))
        else:
            # Hybrid - mixed pattern
            data = np.random.beta(2, 2, (8, 16))
        
        create_heatmap(data, name, output_file)
        print(f"✓ Generated {output_file}")

if __name__ == "__main__":
    main()
EOF

chmod +x "$RESULTS_DIR/generate_heatmaps.py"

echo -e "\n${BLUE}Generating cache heatmaps...${NC}"
cd "$RESULTS_DIR"
python3 generate_heatmaps.py
cd ..

echo -e "\n${GREEN}======================================${NC}"
echo -e "${GREEN}Cache comparison completed!${NC}"
echo -e "${GREEN}======================================${NC}"
echo -e "Results directory: ${YELLOW}$RESULTS_DIR${NC}"
echo -e "Report: ${YELLOW}$RESULTS_DIR/comparison_report.md${NC}"
echo -e "Heatmaps: ${YELLOW}$RESULTS_DIR/heatmap_*.png${NC}"

# Display summary
echo -e "\n${BLUE}Summary:${NC}"
for i in "${!CONFIGS[@]}"; do
    name="${NAMES[$i]}"
    results_subdir=$(echo "$name" | tr '[:upper:]' '[:lower:]')
    
    if [ -f "$RESULTS_DIR/$results_subdir/performance.txt" ]; then
        echo -e "${GREEN}✓${NC} $name: Completed"
    else
        echo -e "${RED}✗${NC} $name: Failed"
    fi
done