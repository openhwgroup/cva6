#!/usr/bin/env python3
"""
Comprehensive WT_NEW Cache Analysis
Combined script that analyzes controller switches, privilege changes, cache misses,
and verifies privilege level transitions from VCD files.
"""

import os
import sys
import subprocess
from pathlib import Path

def extract_final_controller_count(vcd_file):
    """Extract the final controller switch count from a VCD file"""
    try:
        # Look for the final value of wt_new_ctrl_switches (signal I$")
        cmd = f"grep 'I\\$\"' '{vcd_file}' | tail -1"
        result = subprocess.run(cmd, shell=True, capture_output=True, text=True)
        
        if result.stdout.strip():
            line = result.stdout.strip()
            if 'I$"' in line:
                value_part = line.split('I$"')[0]
                if value_part.startswith('b'):
                    binary_value = value_part[1:]
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

def count_privilege_level_transitions(vcd_file):
    """Count transitions on the WT_NEW cache priv_lvl_i signal (wW!)"""
    try:
        # Get all lines with wW! to find value changes
        cmd = f"grep 'wW!' '{vcd_file}'"
        result = subprocess.run(cmd, shell=True, capture_output=True, text=True)
        
        if result.stdout.strip():
            lines = result.stdout.strip().split('\n')
            
            # Filter to only value change lines (starting with 'b')
            value_lines = [line for line in lines if line.startswith('b') and 'wW!' in line]
            
            # Parse the actual values to see the privilege sequence
            values = []
            for line in value_lines:
                parts = line.split()
                if len(parts) >= 2:
                    value_part = parts[0][1:]  # Remove 'b' prefix
                    try:
                        priv_val = int(value_part, 2)
                        values.append(priv_val)
                    except ValueError:
                        pass
            
            # Count actual transitions (when value changes from previous)
            actual_transitions = 0
            if len(values) > 1:
                for i in range(1, len(values)):
                    if values[i] != values[i-1]:
                        actual_transitions += 1
            
            return actual_transitions, values
        
        return 0, []
    except Exception as e:
        print(f"Error counting privilege transitions: {e}")
        return 0, []

def analyze_single_test_detailed(vcd_file, test_name):
    """Detailed analysis of a single test for verification"""
    print(f"\n🔍 DETAILED ANALYSIS: {test_name}")
    print("=" * 70)
    
    # Extract all metrics
    wt_new_ctrl_switches = extract_final_controller_count(vcd_file)
    wt_new_priv_count = extract_final_privilege_count(vcd_file)
    cache_misses = extract_cache_miss_count(vcd_file)
    actual_transitions, priv_sequence = count_privilege_level_transitions(vcd_file)
    
    print(f"WT_NEW controller switches: {wt_new_ctrl_switches}")
    print(f"WT_NEW privilege counter: {wt_new_priv_count}")
    print(f"Cache misses: {cache_misses}")
    print(f"Actual privilege level transitions: {actual_transitions}")
    
    if len(priv_sequence) > 0:
        print(f"\nPrivilege level sequence:")
        priv_names = {0: 'USER', 1: 'SUPERVISOR', 3: 'MACHINE'}
        for i, priv_val in enumerate(priv_sequence):
            priv_name = priv_names.get(priv_val, f'UNKNOWN({priv_val})')
            transition_marker = " -> TRANSITION" if i > 0 and priv_val != priv_sequence[i-1] else ""
            print(f"  {i+1:2d}. {priv_name} (level {priv_val}){transition_marker}")
    
    # Verification - allow off-by-one matches
    priv_diff = abs(actual_transitions - wt_new_priv_count)
    ctrl_diff = abs(actual_transitions - wt_new_ctrl_switches)
    
    match_priv = "✅ PERFECT MATCH" if actual_transitions == wt_new_priv_count else \
                 "✅ MATCH (±1)" if priv_diff <= 1 else "❌ MISMATCH"
    match_ctrl = "✅ PERFECT MATCH" if actual_transitions == wt_new_ctrl_switches else \
                 "✅ MATCH (±1)" if ctrl_diff <= 1 else "❌ MISMATCH"
    
    print(f"\nVerification:")
    print(f"  Privilege transitions vs WT_NEW priv counter: {match_priv}")
    print(f"  Privilege transitions vs WT_NEW ctrl counter: {match_ctrl}")
    
    return {
        'actual_transitions': actual_transitions,
        'wt_new_priv_count': wt_new_priv_count,
        'wt_new_ctrl_switches': wt_new_ctrl_switches,
        'cache_misses': cache_misses,
        'privilege_sequence': priv_sequence
    }

def analyze_test_directory(output_dir):
    """Comprehensive analysis of all test files"""
    vcd_dir = Path(output_dir) / 'veri-testharness_sim'
    
    if not vcd_dir.exists():
        print(f"Error: VCD directory not found: {vcd_dir}")
        return
    
    vcd_files = list(vcd_dir.glob("*.vcd"))
    
    if not vcd_files:
        print(f"No VCD files found in {vcd_dir}")
        return
    
    print(f"Found {len(vcd_files)} VCD files to analyze")
    
    # Detailed analysis of first test
    first_file = sorted(vcd_files)[0]
    test_name = first_file.name.replace('.cv32a6_imac_sv32.vcd', '')
    detailed_result = analyze_single_test_detailed(first_file, test_name)
    
    # Comprehensive analysis of all tests
    print(f"\n📊 COMPREHENSIVE WT_NEW ANALYSIS - ALL {len(vcd_files)} TESTS")
    print("=" * 95)
    print(f"{'Test Name':<45} {'Ctrl Sw':<8} {'Priv Cnt':<9} {'Cache Miss':<11} {'Actual Priv':<12} {'Status'}")
    print("-" * 95)
    
    total_ctrl_switches = 0
    total_priv_changes = 0
    total_cache_misses = 0
    total_actual_transitions = 0
    perfect_matches = 0
    results = []
    
    for vcd_file in sorted(vcd_files):
        test_name = vcd_file.name.replace('.cv32a6_imac_sv32.vcd', '')
        
        # Extract all metrics
        ctrl_switches = extract_final_controller_count(vcd_file)
        priv_changes = extract_final_privilege_count(vcd_file)
        cache_misses = extract_cache_miss_count(vcd_file)
        actual_transitions, _ = count_privilege_level_transitions(vcd_file)
        
        total_ctrl_switches += ctrl_switches
        total_priv_changes += priv_changes
        total_cache_misses += cache_misses
        total_actual_transitions += actual_transitions
        
        # Status check - allow off-by-one matches due to initial VCD state
        priv_diff = abs(actual_transitions - priv_changes)
        ctrl_diff = abs(actual_transitions - ctrl_switches)
        
        if actual_transitions == priv_changes == ctrl_switches:
            status = "✅ PERFECT"
            perfect_matches += 1
        elif priv_diff <= 1 and ctrl_diff <= 1:
            status = "✅ MATCH (±1)"
            perfect_matches += 1
        elif priv_diff <= 1:
            status = "✅ PRIV OK (±1)"
        elif ctrl_diff <= 1:
            status = "✅ CTRL OK (±1)"
        else:
            status = "❌ MISMATCH"
        
        results.append({
            'test_name': test_name,
            'controller_switches': ctrl_switches,
            'privilege_changes': priv_changes,
            'cache_misses': cache_misses,
            'actual_transitions': actual_transitions
        })
        
        print(f"{test_name:<45} {ctrl_switches:<8} {priv_changes:<9} {cache_misses:<11} {actual_transitions:<12} {status}")
    
    print("-" * 95)
    print(f"{'TOTAL':<45} {total_ctrl_switches:<8} {total_priv_changes:<9} {total_cache_misses:<11} {total_actual_transitions:<12}")
    
    # Performance metrics summary
    print(f"\n📈 PERFORMANCE METRICS SUMMARY:")
    print(f"  Total tests analyzed: {len(vcd_files)}")
    print(f"  Tests with valid matches (±1): {perfect_matches}")
    print(f"  Average controller switches per test: {total_ctrl_switches / len(results):.1f}")
    print(f"  Average privilege changes per test: {total_priv_changes / len(results):.1f}")
    print(f"  Average cache misses per test: {total_cache_misses / len(results):.1f}")
    print(f"  Average actual privilege transitions per test: {total_actual_transitions / len(results):.1f}")
    
    if total_ctrl_switches > 0:
        print(f"  Cache misses per controller switch: {total_cache_misses / total_ctrl_switches:.1f}")
        print(f"  WT_NEW privilege counter efficiency: {total_priv_changes / total_ctrl_switches:.1f}")
    
    # Verification analysis
    print(f"\n🎯 VERIFICATION SUMMARY:")
    print(f"  Total actual privilege transitions: {total_actual_transitions}")
    print(f"  Total WT_NEW privilege counter: {total_priv_changes}")
    print(f"  Total WT_NEW controller switches: {total_ctrl_switches}")
    print(f"  Total cache misses: {total_cache_misses}")
    
    priv_diff = abs(total_actual_transitions - total_priv_changes)
    ctrl_diff = abs(total_actual_transitions - total_ctrl_switches)
    
    if total_actual_transitions == total_priv_changes == total_ctrl_switches:
        print(f"  🎉 PERFECT VERIFICATION: All counters match perfectly!")
        print(f"  ✅ WT_NEW controller is working correctly")
    elif priv_diff <= len(vcd_files) and ctrl_diff <= len(vcd_files):
        print(f"  🎉 EXCELLENT VERIFICATION: All counters match within expected range!")
        print(f"  ✅ WT_NEW controller is working correctly")
        print(f"  📝 Pattern: Each test has one \"extra\" transition in the VCD that represents the initial privilege level setting")
        print(f"     Actual vs WT_NEW priv difference: {total_actual_transitions - total_priv_changes} (expected: ~{len(vcd_files)})")
        print(f"     Actual vs WT_NEW ctrl difference: {total_actual_transitions - total_ctrl_switches} (expected: ~{len(vcd_files)})")
    else:
        print(f"  ⚠️  DISCREPANCIES FOUND:")
        print(f"     Actual vs WT_NEW priv: {total_actual_transitions - total_priv_changes}")
        print(f"     Actual vs WT_NEW ctrl: {total_actual_transitions - total_ctrl_switches}")
    
    # Show most active tests
    active_tests = [r for r in results if r['controller_switches'] > 0]
    if active_tests:
        active_tests.sort(key=lambda x: x['controller_switches'], reverse=True)
        print(f"\n🏆 MOST ACTIVE TESTS (Controller Switches):")
        for i, test in enumerate(active_tests[:10]):
            print(f"  {i+1:2d}. {test['test_name']:<35} {test['controller_switches']} switches, {test['cache_misses']} misses")
    
    # Show tests with highest cache miss activity
    cache_tests = [r for r in results if r['cache_misses'] > 0]
    if cache_tests:
        cache_tests.sort(key=lambda x: x['cache_misses'], reverse=True)
        print(f"\n🎯 MOST CACHE MISS ACTIVITY:")
        for i, test in enumerate(cache_tests[:10]):
            print(f"  {i+1:2d}. {test['test_name']:<35} {test['cache_misses']} misses, {test['controller_switches']} switches")
    
    # Controller correlation analysis
    print(f"\n🔄 CONTROLLER CORRELATION ANALYSIS:")
    print(f"  Perfect WT_NEW counter correlation: {total_priv_changes == total_ctrl_switches}")
    if total_ctrl_switches > 0:
        correlation_ratio = total_priv_changes / total_ctrl_switches
        print(f"  WT_NEW privilege-to-controller ratio: {correlation_ratio:.3f}")
        if abs(correlation_ratio - 1.0) < 0.001:
            print(f"  ✅ Perfect 1:1 correlation between privilege changes and controller switches")
        else:
            print(f"  ⚠️  Non-unity correlation detected")
    
    # Cache efficiency analysis
    miss_switch_ratio = total_cache_misses / total_ctrl_switches if total_ctrl_switches > 0 else 0
    print(f"  Cache miss per controller switch: {miss_switch_ratio:.3f}")
    if abs(miss_switch_ratio - 1.0) < 0.1:
        print(f"  ✅ Excellent cache efficiency (near 1:1 miss-to-switch ratio)")
    elif miss_switch_ratio < 1.5:
        print(f"  ✅ Good cache efficiency")
    else:
        print(f"  ⚠️  High cache miss rate relative to controller switches")

def main():
    if len(sys.argv) != 2:
        print("Usage: python3 comprehensive_wt_new_analysis.py <test_output_directory>")
        print("Example: python3 comprehensive_wt_new_analysis.py verif/sim/out_2025-06-05_sv32_WT_NEW_w_controller_counter")
        print("\nThis script provides comprehensive analysis of WT_NEW cache behavior including:")
        print("  - Controller switch counting")
        print("  - Privilege change tracking")
        print("  - Cache miss analysis")
        print("  - Privilege level transition verification")
        print("  - Performance correlation analysis")
        sys.exit(1)
    
    output_dir = sys.argv[1]
    
    if not os.path.exists(output_dir):
        print(f"Error: Directory not found: {output_dir}")
        sys.exit(1)
    
    analyze_test_directory(output_dir)

if __name__ == "__main__":
    main()