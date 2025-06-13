#!/bin/bash

# Script to easily switch between original and fully associative cache configurations
# for cv32a60x target

# Get the script directory and set config file path
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
CONFIG_FILE="$SCRIPT_DIR/core/include/cv32a60x_config_pkg.sv"

if [ "$1" = "original" ]; then
    echo "Switching to original 2028 bytes 2-way set-associative cache configuration..."
    
    # Comment out fully associative config
    sed -i 's/^      DcacheByteSize: unsigned'\''(2048),/      \/\/ DcacheByteSize: unsigned'\''(2048),/' "$CONFIG_FILE"
    sed -i 's/^      DcacheSetAssoc: unsigned'\''(128),/      \/\/ DcacheSetAssoc: unsigned'\''(128),/' "$CONFIG_FILE"
    
    # Uncomment original config
    sed -i 's/^      \/\/ DcacheByteSize: unsigned'\''(2028),/      DcacheByteSize: unsigned'\''(2028),/' "$CONFIG_FILE"
    sed -i 's/^      \/\/ DcacheSetAssoc: unsigned'\''(2),/      DcacheSetAssoc: unsigned'\''(2),/' "$CONFIG_FILE"
    
    echo "Switched to original configuration: 2028 bytes, 2-way set-associative"
    
elif [ "$1" = "fully-assoc" ]; then
    echo "Switching to fully associative cache configuration..."
    
    # Comment out original config
    sed -i 's/^      DcacheByteSize: unsigned'\''(2028),/      \/\/ DcacheByteSize: unsigned'\''(2028),/' "$CONFIG_FILE"
    sed -i 's/^      DcacheSetAssoc: unsigned'\''(2),/      \/\/ DcacheSetAssoc: unsigned'\''(2),/' "$CONFIG_FILE"
    
    # Uncomment fully associative config
    sed -i 's/^      \/\/ DcacheByteSize: unsigned'\''(2048),/      DcacheByteSize: unsigned'\''(2048),/' "$CONFIG_FILE"
    sed -i 's/^      \/\/ DcacheSetAssoc: unsigned'\''(128),/      DcacheSetAssoc: unsigned'\''(128),/' "$CONFIG_FILE"
    
    echo "Switched to fully associative configuration: 2KB, 128-way fully associative"
    
else
    echo "Usage: $0 [original|fully-assoc]"
    echo ""
    echo "  original    - Use original 2028 bytes 2-way set-associative cache"
    echo "  fully-assoc - Use 2KB 128-way fully associative cache"
    echo ""
    echo "Current configuration:"
    grep -E "DcacheByteSize|DcacheSetAssoc" "$CONFIG_FILE" | grep -v "//" | grep -E "unsigned"
fi