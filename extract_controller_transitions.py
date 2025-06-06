#!/usr/bin/env python3
"""
Extract WT_NEW Controller Transition Counts from VCD files
Focused on extracting the final controller switch counts from each test.
"""

import os
import sys
import subprocess
from pathlib import Path

def extract_final_controller_count(vcd_file):
    """Extract the final controller switch count from a VCD file"""
    try:
        # Look for the final value of wt_new_ctrl_switches (signal I$")
        # This signal is a 16-bit counter showing total controller switches
        cmd = f"grep 'I\\$\"' '{vcd_file}' | tail -1"
        result = subprocess.run(cmd, shell=True, capture_output=True, text=True)
        
        if result.stdout.strip():
            line = result.stdout.strip()
            # Extract binary value before 'I$"'
            if 'I$"' in line:
                value_part = line.split('I$"')[0]
                if value_part.startswith('b'):
                    # Binary format: b0000000000000101I$"
                    binary_value = value_part[1:]  # Remove 'b' prefix
                    try:
                        return int(binary_value, 2)
                    except ValueError:
                        return 0
        return 0
    except Exception:
        return 0

def extract_final_privilege_count(vcd_file):
    """Extract the final privilege change count from a VCD file"""
    try:
        # Look for the final value of wt_new_priv_changes (signal J$")
        cmd = f"grep 'J\\$\"' '{vcd_file}' | tail -1"
        result = subprocess.run(cmd, shell=True, capture_output=True, text=True)
        
        if result.stdout.strip():
            line = result.stdout.strip()
            if 'J$"' in line:
                value_part = line.split('J$"')[0]
                if value_part.startswith('b'):
                    binary_value = value_part[1:]
                    try:
                        return int(binary_value, 2)
                    except ValueError:
                        return 0
        return 0
    except Exception:
        return 0

def extract_cache_miss_count(vcd_file):
    """Extract cache miss count by counting dcache miss events"""
    try:
        # Look for WT_NEW dcache miss signal transitions (1~V" indicates miss_o going high)
        cmd = f"grep -c '1~V\"' '{vcd_file}'"
        result = subprocess.run(cmd, shell=True, capture_output=True, text=True)
        
        if result.stdout.strip():
            try:
                return int(result.stdout.strip())
            except ValueError:
                return 0
        return 0
    except Exception:
        return 0

def analyze_test_directory(output_dir):
    """Analyze all VCD files in the test output directory"""
    vcd_dir = Path(output_dir) / 'veri-testharness_sim'
    
    if not vcd_dir.exists():
        print(f"Error: VCD directory not found: {vcd_dir}")
        return
    
    vcd_files = list(vcd_dir.glob("*.vcd"))
    
    if not vcd_files:
        print(f"No VCD files found in {vcd_dir}")
        return
    
    print(f"Found {len(vcd_files)} VCD files to analyze")
    print()
    print(f"{'Test Name':<45} {'Ctrl Switches':<13} {'Priv Changes':<13} {'Cache Misses':<12}")
    print("-" * 83)
    
    total_ctrl_switches = 0
    total_priv_changes = 0
    total_cache_misses = 0
    results = []
    
    for vcd_file in sorted(vcd_files):
        test_name = vcd_file.name.replace('.cv32a6_imac_sv32.vcd', '')
        
        ctrl_switches = extract_final_controller_count(vcd_file)
        priv_changes = extract_final_privilege_count(vcd_file)
        cache_misses = extract_cache_miss_count(vcd_file)
        
        total_ctrl_switches += ctrl_switches
        total_priv_changes += priv_changes
        total_cache_misses += cache_misses
        
        results.append({
            'test_name': test_name,
            'controller_switches': ctrl_switches,
            'privilege_changes': priv_changes,
            'cache_misses': cache_misses
        })
        
        print(f"{test_name:<45} {ctrl_switches:<13} {priv_changes:<13} {cache_misses:<12}")
    
    print("-" * 83)
    print(f"{'TOTAL':<45} {total_ctrl_switches:<13} {total_priv_changes:<13} {total_cache_misses:<12}")
    print()
    
    # Summary statistics
    tests_with_switches = sum(1 for r in results if r['controller_switches'] > 0)
    tests_with_priv_changes = sum(1 for r in results if r['privilege_changes'] > 0)
    tests_with_cache_misses = sum(1 for r in results if r['cache_misses'] > 0)
    
    print("SUMMARY:")
    print(f"  Total tests analyzed: {len(results)}")
    print(f"  Tests with controller switches: {tests_with_switches}")
    print(f"  Tests with privilege changes: {tests_with_priv_changes}")
    print(f"  Tests with cache misses: {tests_with_cache_misses}")
    print(f"  Average controller switches per test: {total_ctrl_switches / len(results):.1f}")
    print(f"  Average privilege changes per test: {total_priv_changes / len(results):.1f}")
    print(f"  Average cache misses per test: {total_cache_misses / len(results):.1f}")
    
    if total_ctrl_switches > 0:
        print(f"  Privilege changes per controller switch: {total_priv_changes / total_ctrl_switches:.1f}")
        print(f"  Cache misses per controller switch: {total_cache_misses / total_ctrl_switches:.1f}")
    
    # Show most active tests
    active_tests = [r for r in results if r['controller_switches'] > 0]
    if active_tests:
        active_tests.sort(key=lambda x: x['controller_switches'], reverse=True)
        print(f"\nMOST ACTIVE TESTS (Controller Switches):")
        for i, test in enumerate(active_tests[:10]):
            print(f"  {i+1:2d}. {test['test_name']:<35} {test['controller_switches']} switches, {test['cache_misses']} misses")
    
    # Show tests with highest cache miss activity
    cache_tests = [r for r in results if r['cache_misses'] > 0]
    if cache_tests:
        cache_tests.sort(key=lambda x: x['cache_misses'], reverse=True)
        print(f"\nMOST CACHE MISS ACTIVITY:")
        for i, test in enumerate(cache_tests[:10]):
            print(f"  {i+1:2d}. {test['test_name']:<35} {test['cache_misses']} misses, {test['controller_switches']} switches")

def main():
    if len(sys.argv) != 2:
        print("Usage: python3 extract_controller_transitions.py <test_output_directory>")
        print("Example: python3 extract_controller_transitions.py verif/sim/out_2025-06-05_sv32_WT_NEW_w_controller_counter")
        sys.exit(1)
    
    output_dir = sys.argv[1]
    
    if not os.path.exists(output_dir):
        print(f"Error: Directory not found: {output_dir}")
        sys.exit(1)
    
    analyze_test_directory(output_dir)

if __name__ == "__main__":
    main()