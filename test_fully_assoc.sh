#!/bin/bash

# Script to test fully associative cache configuration

echo "Testing CVA6 with fully associative WT_CLN cache..."

# Backup original config
cp core/include/cv32a60x_config_pkg.sv core/include/cv32a60x_config_pkg.sv.bak

# Use fully associative config
cp core/include/cv32a60x_fully_assoc_config_pkg.sv core/include/cv32a60x_config_pkg.sv

# Run simulation with hello world test
echo "Running simulation with fully associative cache..."
make sim elf_file=verif/tests/custom/hello_world/hello_world.elf

# Restore original config
cp core/include/cv32a60x_config_pkg.sv.bak core/include/cv32a60x_config_pkg.sv
rm core/include/cv32a60x_config_pkg.sv.bak

echo "Test complete!"