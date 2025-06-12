#!/bin/bash

# Script to easily switch between cache configurations for cv32a6_imac_sv32 target

# Get the script directory and set config file path
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
CONFIG_FILE="$SCRIPT_DIR/core/include/cv32a6_imac_sv32_config_pkg.sv"

if [ "$1" = "original" ]; then
    echo "Switching to original 32KB 8-way set-associative cache configuration..."
    
    # Comment out all fully associative configs
    sed -i 's/^  localparam CVA6ConfigDcacheByteSize = 256;/  \/\/ localparam CVA6ConfigDcacheByteSize = 256;/' "$CONFIG_FILE"
    sed -i 's/^  localparam CVA6ConfigDcacheSetAssoc = 16;/  \/\/ localparam CVA6ConfigDcacheSetAssoc = 16;/' "$CONFIG_FILE"
    sed -i 's/^  localparam CVA6ConfigDcacheByteSize = 2048;/  \/\/ localparam CVA6ConfigDcacheByteSize = 2048;/' "$CONFIG_FILE"
    sed -i 's/^  localparam CVA6ConfigDcacheSetAssoc = 128;/  \/\/ localparam CVA6ConfigDcacheSetAssoc = 128;/' "$CONFIG_FILE"
    sed -i 's/^  localparam CVA6ConfigDcacheByteSize = 32768;/  \/\/ localparam CVA6ConfigDcacheByteSize = 32768;/' "$CONFIG_FILE"
    sed -i 's/^  localparam CVA6ConfigDcacheSetAssoc = 2048;/  \/\/ localparam CVA6ConfigDcacheSetAssoc = 2048;/' "$CONFIG_FILE"
    
    # Uncomment original config
    sed -i 's/^  \/\/ localparam CVA6ConfigDcacheByteSize = 32768;/  localparam CVA6ConfigDcacheByteSize = 32768;/' "$CONFIG_FILE"
    sed -i 's/^  \/\/ localparam CVA6ConfigDcacheSetAssoc = 8;/  localparam CVA6ConfigDcacheSetAssoc = 8;/' "$CONFIG_FILE"
    
    echo "Switched to original configuration: 32KB, 8-way set-associative"
    
elif [ "$1" = "small-assoc" ]; then
    echo "Switching to small fully associative cache configuration..."
    
    # Comment out original, medium, and large configs
    sed -i 's/^  localparam CVA6ConfigDcacheByteSize = 32768;/  \/\/ localparam CVA6ConfigDcacheByteSize = 32768;/' "$CONFIG_FILE"
    sed -i 's/^  localparam CVA6ConfigDcacheSetAssoc = 8;/  \/\/ localparam CVA6ConfigDcacheSetAssoc = 8;/' "$CONFIG_FILE"
    sed -i 's/^  localparam CVA6ConfigDcacheByteSize = 2048;/  \/\/ localparam CVA6ConfigDcacheByteSize = 2048;/' "$CONFIG_FILE"
    sed -i 's/^  localparam CVA6ConfigDcacheSetAssoc = 128;/  \/\/ localparam CVA6ConfigDcacheSetAssoc = 128;/' "$CONFIG_FILE"
    sed -i 's/^  localparam CVA6ConfigDcacheByteSize = 32768;/  \/\/ localparam CVA6ConfigDcacheByteSize = 32768;/' "$CONFIG_FILE"
    sed -i 's/^  localparam CVA6ConfigDcacheSetAssoc = 2048;/  \/\/ localparam CVA6ConfigDcacheSetAssoc = 2048;/' "$CONFIG_FILE"
    
    # Uncomment small fully associative config
    sed -i 's/^  \/\/ localparam CVA6ConfigDcacheByteSize = 256;/  localparam CVA6ConfigDcacheByteSize = 256;/' "$CONFIG_FILE"
    sed -i 's/^  \/\/ localparam CVA6ConfigDcacheSetAssoc = 16;/  localparam CVA6ConfigDcacheSetAssoc = 16;/' "$CONFIG_FILE"
    
    echo "Switched to small fully associative configuration: 256B, 16-way fully associative"
    
elif [ "$1" = "large-assoc" ]; then
    echo "Switching to large fully associative cache configuration..."
    
    # Comment out original, small, and medium configs  
    sed -i 's/^  localparam CVA6ConfigDcacheByteSize = 32768;/  \/\/ localparam CVA6ConfigDcacheByteSize = 32768;/' "$CONFIG_FILE"
    sed -i 's/^  localparam CVA6ConfigDcacheSetAssoc = 8;/  \/\/ localparam CVA6ConfigDcacheSetAssoc = 8;/' "$CONFIG_FILE"
    sed -i 's/^  localparam CVA6ConfigDcacheByteSize = 256;/  \/\/ localparam CVA6ConfigDcacheByteSize = 256;/' "$CONFIG_FILE"
    sed -i 's/^  localparam CVA6ConfigDcacheSetAssoc = 16;/  \/\/ localparam CVA6ConfigDcacheSetAssoc = 16;/' "$CONFIG_FILE"
    sed -i 's/^  localparam CVA6ConfigDcacheByteSize = 2048;/  \/\/ localparam CVA6ConfigDcacheByteSize = 2048;/' "$CONFIG_FILE"
    sed -i 's/^  localparam CVA6ConfigDcacheSetAssoc = 128;/  \/\/ localparam CVA6ConfigDcacheSetAssoc = 128;/' "$CONFIG_FILE"
    
    # Uncomment large fully associative config
    sed -i 's/^  \/\/ localparam CVA6ConfigDcacheByteSize = 32768;/  localparam CVA6ConfigDcacheByteSize = 32768;/' "$CONFIG_FILE"
    sed -i 's/^  \/\/ localparam CVA6ConfigDcacheSetAssoc = 2048;/  localparam CVA6ConfigDcacheSetAssoc = 2048;/' "$CONFIG_FILE"
    
    echo "Switched to large fully associative configuration: 32KB, 2048-way fully associative"
    
elif [ "$1" = "medium-assoc" ]; then
    echo "Switching to medium fully associative cache configuration..."
    
    # Comment out original, small, and large configs
    sed -i 's/^  localparam CVA6ConfigDcacheByteSize = 32768;/  \/\/ localparam CVA6ConfigDcacheByteSize = 32768;/' "$CONFIG_FILE"
    sed -i 's/^  localparam CVA6ConfigDcacheSetAssoc = 8;/  \/\/ localparam CVA6ConfigDcacheSetAssoc = 8;/' "$CONFIG_FILE"
    sed -i 's/^  localparam CVA6ConfigDcacheByteSize = 256;/  \/\/ localparam CVA6ConfigDcacheByteSize = 256;/' "$CONFIG_FILE"
    sed -i 's/^  localparam CVA6ConfigDcacheSetAssoc = 16;/  \/\/ localparam CVA6ConfigDcacheSetAssoc = 16;/' "$CONFIG_FILE"
    sed -i 's/^  localparam CVA6ConfigDcacheByteSize = 32768;/  \/\/ localparam CVA6ConfigDcacheByteSize = 32768;/' "$CONFIG_FILE"
    sed -i 's/^  localparam CVA6ConfigDcacheSetAssoc = 2048;/  \/\/ localparam CVA6ConfigDcacheSetAssoc = 2048;/' "$CONFIG_FILE"
    
    # Uncomment medium fully associative config
    sed -i 's/^  \/\/ localparam CVA6ConfigDcacheByteSize = 2048;/  localparam CVA6ConfigDcacheByteSize = 2048;/' "$CONFIG_FILE"
    sed -i 's/^  \/\/ localparam CVA6ConfigDcacheSetAssoc = 128;/  localparam CVA6ConfigDcacheSetAssoc = 128;/' "$CONFIG_FILE"
    
    echo "Switched to medium fully associative configuration: 2KB, 128-way fully associative"
    
else
    echo "Usage: $0 [original|small-assoc|medium-assoc|large-assoc]"
    echo ""
    echo "  original     - Use original 32KB 8-way set-associative cache"
    echo "  small-assoc  - Use 256B 16-way fully associative cache"
    echo "  medium-assoc - Use 2KB 128-way fully associative cache (current working config)"
    echo "  large-assoc  - Use 32KB 2048-way fully associative cache (may cause Verilator crash)"
    echo ""
    echo "Current configuration:"
    grep -E "localparam CVA6ConfigDcacheByteSize|localparam CVA6ConfigDcacheSetAssoc" "$CONFIG_FILE" | grep -v "//"
fi