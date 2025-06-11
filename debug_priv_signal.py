#!/usr/bin/env python3
"""
Debug privilege signal format in VCD files
"""

import subprocess
import sys

def debug_privilege_signal(vcd_file):
    print(f"Debugging privilege signal in: {vcd_file}")
    
    # 1. Find all lines with wW!
    print("\n1. All lines containing wW!:")
    cmd = f"grep 'wW!' '{vcd_file}'"
    result = subprocess.run(cmd, shell=True, capture_output=True, text=True)
    lines = result.stdout.strip().split('\n')
    for i, line in enumerate(lines):
        print(f"  {i+1:2d}: {line}")
    
    # 2. Find just the value changes
    print("\n2. Lines starting with 'b' and containing wW!:")
    value_lines = [line for line in lines if line.startswith('b') and 'wW!' in line]
    for i, line in enumerate(value_lines):
        print(f"  {i+1:2d}: {line}")
    
    # 3. Parse the values
    print("\n3. Parsed privilege values:")
    values = []
    for line in value_lines:
        parts = line.split()
        if len(parts) >= 2:
            value_part = parts[0][1:]  # Remove 'b'
            try:
                priv_val = int(value_part, 2)
                values.append(priv_val)
                print(f"     {line} -> {priv_val}")
            except ValueError:
                print(f"     {line} -> PARSE ERROR")
    
    print(f"\n4. Transition analysis:")
    print(f"   Total value entries: {len(values)}")
    print(f"   Privilege sequence: {values}")
    if len(values) > 1:
        transitions = 0
        for i in range(1, len(values)):
            if values[i] != values[i-1]:
                transitions += 1
                print(f"     Transition {transitions}: {values[i-1]} -> {values[i]}")
        print(f"   Total transitions: {transitions}")
    else:
        print(f"   No transitions (need at least 2 values)")

if __name__ == "__main__":
    if len(sys.argv) != 2:
        print("Usage: python3 debug_priv_signal.py <vcd_file>")
        sys.exit(1)
    
    debug_privilege_signal(sys.argv[1])