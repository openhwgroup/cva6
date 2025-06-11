#!/usr/bin/env python3
"""
WT_NEW Controller Transition Analysis
Analyzes VCD files to count controller transitions in WT_NEW cache
and correlates them with privilege mode changes and cache behavior.
"""

import os
import sys
import subprocess
import tempfile
from pathlib import Path
import json
from collections import defaultdict

class ControllerTransitionAnalyzer:
    def __init__(self):
        self.results = {}
        
    def extract_privilege_transitions(self, vcd_file):
        """Extract privilege level transitions with timestamps"""
        try:
            with tempfile.NamedTemporaryFile(mode='w', delete=False, suffix='.txt') as temp_file:
                # Extract privilege level signal changes with timestamps
                # Signal wW! is priv_lvl (2 bits)
                cmd = f"grep -E '^b[01]{{1,2}}wW!|^#' '{vcd_file}' > {temp_file.name}"
                subprocess.run(cmd, shell=True)
                
                transitions = []
                current_time = 0
                
                with open(temp_file.name, 'r') as f:
                    for line in f:
                        line = line.strip()
                        if line.startswith('#'):
                            # Time marker: #1234
                            current_time = int(line[1:])
                        elif line.startswith('b') and 'wW!' in line:
                            # Privilege level change: b11wW!
                            value_str = line[1:line.find('wW!')]
                            try:
                                priv_level = int(value_str, 2)
                                priv_name = {0: 'USER', 1: 'SUPERVISOR', 3: 'MACHINE'}.get(priv_level, f'UNKNOWN({priv_level})')
                                transitions.append({
                                    'time': current_time,
                                    'level': priv_level,
                                    'name': priv_name
                                })
                            except ValueError:
                                pass
                
                os.unlink(temp_file.name)
                return transitions
                
        except Exception as e:
            print(f"Error extracting privilege transitions: {e}")
            return []
    
    def extract_cache_miss_events(self, vcd_file):
        """Extract cache miss events with timestamps"""
        try:
            with tempfile.NamedTemporaryFile(mode='w', delete=False, suffix='.txt') as temp_file:
                # Extract dcache miss signal changes with timestamps
                cmd = f"grep -E '^1xV\"|^#' '{vcd_file}' > {temp_file.name}"
                subprocess.run(cmd, shell=True)
                
                misses = []
                current_time = 0
                
                with open(temp_file.name, 'r') as f:
                    for line in f:
                        line = line.strip()
                        if line.startswith('#'):
                            current_time = int(line[1:])
                        elif line.startswith('1xV"'):
                            # Cache miss occurred
                            misses.append(current_time)
                
                os.unlink(temp_file.name)
                return misses
                
        except Exception as e:
            print(f"Error extracting cache misses: {e}")
            return []
    
    def analyze_controller_transitions(self, privilege_transitions):
        """Analyze when WT_NEW would switch controllers based on privilege changes"""
        if len(privilege_transitions) < 2:
            return []
        
        controller_switches = []
        
        # WT_NEW dual controller logic:
        # - Controller 0: User/Supervisor modes (levels 0, 1)
        # - Controller 1: Machine mode (level 3)
        
        prev_controller = self.get_controller_for_privilege(privilege_transitions[0]['level'])
        
        for i in range(1, len(privilege_transitions)):
            current_priv = privilege_transitions[i]
            current_controller = self.get_controller_for_privilege(current_priv['level'])
            
            if current_controller != prev_controller:
                controller_switches.append({
                    'time': current_priv['time'],
                    'from_controller': prev_controller,
                    'to_controller': current_controller,
                    'from_privilege': privilege_transitions[i-1]['name'],
                    'to_privilege': current_priv['name'],
                    'privilege_level': current_priv['level']
                })
            
            prev_controller = current_controller
        
        return controller_switches
    
    def get_controller_for_privilege(self, priv_level):
        """Determine which WT_NEW controller handles this privilege level"""
        # WT_NEW dual controller architecture:
        # Controller 0: User (0) and Supervisor (1) modes
        # Controller 1: Machine mode (3)
        if priv_level in [0, 1]:  # User, Supervisor
            return 0
        elif priv_level == 3:     # Machine
            return 1
        else:
            return 0  # Default to controller 0 for unknown levels
    
    def correlate_events(self, privilege_transitions, controller_switches, cache_misses):
        """Correlate privilege changes, controller switches, and cache misses"""
        correlations = []
        
        # For each controller switch, find nearby cache misses
        for switch in controller_switches:
            switch_time = switch['time']
            
            # Find cache misses within ±50 cycles of the controller switch
            nearby_misses = []
            for miss_time in cache_misses:
                if abs(miss_time - switch_time) <= 50:
                    nearby_misses.append({
                        'time': miss_time,
                        'offset': miss_time - switch_time
                    })
            
            correlations.append({
                'controller_switch': switch,
                'nearby_cache_misses': nearby_misses,
                'miss_count_nearby': len(nearby_misses)
            })
        
        return correlations
    
    def analyze_test_file(self, vcd_file, test_name):
        """Comprehensive analysis of a single test file"""
        print(f"\nAnalyzing WT_NEW controller behavior: {test_name}")
        print("="*60)
        
        # Extract all events
        privilege_transitions = self.extract_privilege_transitions(vcd_file)
        cache_misses = self.extract_cache_miss_events(vcd_file)
        
        print(f"Privilege transitions found: {len(privilege_transitions)}")
        print(f"Cache misses found: {len(cache_misses)}")
        
        if not privilege_transitions:
            print("⚠ No privilege transitions detected - cannot analyze controller switches")
            return {
                'test_name': test_name,
                'privilege_transitions': 0,
                'controller_switches': 0,
                'cache_misses': len(cache_misses),
                'correlations': []
            }
        
        # Analyze controller transitions
        controller_switches = self.analyze_controller_transitions(privilege_transitions)
        print(f"Controller switches calculated: {len(controller_switches)}")
        
        # Show privilege sequence
        if privilege_transitions:
            print(f"\nPrivilege sequence:")
            for i, trans in enumerate(privilege_transitions[:10]):  # Show first 10
                controller = self.get_controller_for_privilege(trans['level'])
                print(f"  {i+1:2d}: Time {trans['time']:6d} -> {trans['name']} (Level {trans['level']}, Controller {controller})")
            
            if len(privilege_transitions) > 10:
                print(f"  ... and {len(privilege_transitions) - 10} more transitions")
        
        # Show controller switches
        if controller_switches:
            print(f"\nController switches:")
            for i, switch in enumerate(controller_switches):
                print(f"  {i+1:2d}: Time {switch['time']:6d} -> Controller {switch['from_controller']} to {switch['to_controller']} "
                     f"({switch['from_privilege']} -> {switch['to_privilege']})")
        else:
            print(f"\nNo controller switches detected")
            print(f"  This could mean:")
            print(f"  - Test operates within single privilege level")
            print(f"  - All privilege changes stay within same controller domain")
        
        # Correlate events
        correlations = self.correlate_events(privilege_transitions, controller_switches, cache_misses)
        
        if correlations:
            print(f"\nController switch vs Cache miss correlation:")
            for i, corr in enumerate(correlations):
                switch = corr['controller_switch']
                miss_count = corr['miss_count_nearby']
                print(f"  Switch {i+1}: Time {switch['time']} -> {miss_count} cache misses within ±50 cycles")
        
        # Calculate statistics
        total_time = privilege_transitions[-1]['time'] if privilege_transitions else 0
        switch_rate = len(controller_switches) / (total_time / 1000) if total_time > 0 else 0
        
        print(f"\nStatistics:")
        print(f"  Total simulation time: {total_time} cycles")
        print(f"  Controller switch rate: {switch_rate:.3f} switches per 1000 cycles")
        print(f"  Cache misses per controller switch: {len(cache_misses) / max(1, len(controller_switches)):.1f}")
        
        return {
            'test_name': test_name,
            'privilege_transitions': len(privilege_transitions),
            'controller_switches': len(controller_switches),
            'cache_misses': len(cache_misses),
            'total_cycles': total_time,
            'switch_rate_per_1k_cycles': switch_rate,
            'misses_per_switch': len(cache_misses) / max(1, len(controller_switches)),
            'privilege_sequence': privilege_transitions,
            'controller_switch_details': controller_switches,
            'correlations': correlations
        }

def analyze_multiple_tests(base_dir, test_pattern="*.vcd"):
    """Analyze multiple WT_NEW test files"""
    vcd_dir = Path(base_dir) / 'veri-testharness_sim'
    vcd_files = list(vcd_dir.glob(test_pattern))
    
    analyzer = ControllerTransitionAnalyzer()
    results = []
    
    print(f"Found {len(vcd_files)} VCD files to analyze")
    
    for vcd_file in sorted(vcd_files):
        test_name = vcd_file.name.replace('.cv32a6_imac_sv32.vcd', '')
        result = analyzer.analyze_test_file(vcd_file, test_name)
        results.append(result)
    
    return results

def generate_summary_report(results):
    """Generate summary report of all controller transition analysis"""
    print("\n" + "="*80)
    print("WT_NEW CONTROLLER TRANSITION SUMMARY")
    print("="*80)
    
    # Summary table
    print(f"\n{'Test Name':<35} {'Priv Trans':<10} {'Ctrl Switch':<11} {'Cache Miss':<10} {'Switch Rate':<12}")
    print("-" * 85)
    
    total_priv_trans = 0
    total_ctrl_switches = 0
    total_cache_misses = 0
    tests_with_switches = 0
    
    for result in results:
        test_name = result['test_name']
        priv_trans = result['privilege_transitions']
        ctrl_switches = result['controller_switches']
        cache_misses = result['cache_misses']
        switch_rate = result['switch_rate_per_1k_cycles']
        
        total_priv_trans += priv_trans
        total_ctrl_switches += ctrl_switches
        total_cache_misses += cache_misses
        
        if ctrl_switches > 0:
            tests_with_switches += 1
        
        print(f"{test_name:<35} {priv_trans:<10} {ctrl_switches:<11} {cache_misses:<10} {switch_rate:<12.3f}")
    
    # Summary statistics
    print(f"\n{'TOTALS':<35} {total_priv_trans:<10} {total_ctrl_switches:<11} {total_cache_misses:<10}")
    
    print(f"\nSUMMARY STATISTICS:")
    print(f"  Total tests analyzed: {len(results)}")
    print(f"  Tests with controller switches: {tests_with_switches}")
    print(f"  Tests with no switches: {len(results) - tests_with_switches}")
    print(f"  Total privilege transitions: {total_priv_trans}")
    print(f"  Total controller switches: {total_ctrl_switches}")
    print(f"  Total cache misses: {total_cache_misses}")
    
    if total_ctrl_switches > 0:
        print(f"  Average cache misses per controller switch: {total_cache_misses / total_ctrl_switches:.1f}")
        print(f"  Controller switch efficiency: {total_priv_trans / total_ctrl_switches:.1f} privilege changes per switch")
    
    # Identify tests with most controller activity
    active_tests = [r for r in results if r['controller_switches'] > 0]
    if active_tests:
        active_tests.sort(key=lambda x: x['controller_switches'], reverse=True)
        print(f"\nMOST ACTIVE CONTROLLER SWITCHING TESTS:")
        for result in active_tests[:10]:
            print(f"  {result['test_name']:<35} {result['controller_switches']} switches, {result['cache_misses']} misses")

def main():
    if len(sys.argv) < 2:
        print("Usage: python3 wt_new_controller_analyzer.py <WT_NEW_DIR> [specific_test.vcd]")
        print("Example: python3 wt_new_controller_analyzer.py out_2025-06-05_sv32_WT_NEW")
        print("Example: python3 wt_new_controller_analyzer.py out_2025-06-05_sv32_WT_NEW rv32_vm_satp_access.cv32a6_imac_sv32.vcd")
        sys.exit(1)
    
    base_dir = sys.argv[1]
    
    if not os.path.exists(base_dir):
        print(f"Error: Directory not found: {base_dir}")
        sys.exit(1)
    
    if len(sys.argv) > 2:
        # Analyze specific test
        test_file = sys.argv[2]
        vcd_file = Path(base_dir) / 'veri-testharness_sim' / test_file
        
        if not vcd_file.exists():
            print(f"Error: VCD file not found: {vcd_file}")
            sys.exit(1)
        
        analyzer = ControllerTransitionAnalyzer()
        test_name = vcd_file.name.replace('.cv32a6_imac_sv32.vcd', '')
        result = analyzer.analyze_test_file(vcd_file, test_name)
        
        # Save detailed results for single test
        with open(f"controller_analysis_{test_name}.json", 'w') as f:
            json.dump(result, f, indent=2)
        print(f"\nDetailed analysis saved to: controller_analysis_{test_name}.json")
        
    else:
        # Analyze all tests
        results = analyze_multiple_tests(base_dir)
        generate_summary_report(results)
        
        # Save comprehensive results
        with open("wt_new_controller_analysis.json", 'w') as f:
            json.dump(results, f, indent=2)
        print(f"\nComprehensive analysis saved to: wt_new_controller_analysis.json")

if __name__ == "__main__":
    main()