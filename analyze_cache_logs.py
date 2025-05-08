#!/usr/bin/env python3
"""
Cache Log Analysis Script

This script analyzes existing log files from hello_world.c test runs across different cache implementations:
1. Write-Through Cache (WT)
2. Hybrid Cache in Set Associative Mode (WT_HYB_FORCE_SET_ASS)
3. Hybrid Cache in Fully Associative Mode (WT_HYB_FORCE_FULL_ASS)

It looks for:
- Memory address increments (0 to 9)
- Execution completion status
- Performance metrics (cycles)
"""

import os
import re
import sys
import subprocess
import glob
from pathlib import Path
from datetime import datetime

# Configuration
CACHE_MODES = {
    "WT": "Standard Write-Through Cache",
    "WT_HYB_FORCE_SET_ASS": "Hybrid Cache in Set Associative Mode",
    "WT_HYB_FORCE_FULL_ASS": "Hybrid Cache in Fully Associative Mode"
}

# Paths
BASE_DIR = Path('/home/cai/cache_project/sandbox/cva6')
SIMULATION_DIR = BASE_DIR / 'verif/sim'
OUTPUT_DIR = BASE_DIR / f'cache_log_analysis_{datetime.now().strftime("%Y%m%d_%H%M%S")}'

# Create directories
os.makedirs(OUTPUT_DIR, exist_ok=True)

# Initialize log file
log_path = OUTPUT_DIR / 'analysis_log.txt'
with open(log_path, 'w') as f:
    f.write(f"Cache Log Analysis Run: {datetime.now()}\n")
    f.write("="*80 + "\n\n")

def log_message(message):
    """Log a message to both console and log file"""
    print(message)
    with open(log_path, 'a') as f:
        f.write(message + "\n")

def find_log_files():
    """Find all relevant log files in the simulation directory"""
    log_message("Searching for log files...")
    
    # Look for several patterns in different locations
    patterns = [
        # Main simulation output directories with date pattern
        str(SIMULATION_DIR / "out_*" / "veri-testharness_sim" / "hello_world.cv32a60x.log*"),
        str(SIMULATION_DIR / "cache_comparison_*" / "wt_results" / "hello_world.cv32a60x.log*"),
        str(SIMULATION_DIR / "cache_comparison_*" / "wt_hyb_*_results" / "hello_world.cv32a60x.log*"),
        str(SIMULATION_DIR / "wt_cache_*" / "out_wt_*" / "hello_world.cv32a60x.log*"),
        str(SIMULATION_DIR / "wt_vs_wthyb_*" / "wt_results" / "hello_world.cv32a60x.log*"),
        str(SIMULATION_DIR / "wt_vs_wthyb_*" / "wthyb_results" / "hello_world.cv32a60x.log*"),
    ]
    
    log_files = []
    for pattern in patterns:
        found = glob.glob(pattern)
        log_message(f"Found {len(found)} log files matching {pattern}")
        log_files.extend(found)
    
    # Sort by modification time (newest first)
    log_files.sort(key=os.path.getmtime, reverse=True)
    
    log_message(f"Found a total of {len(log_files)} log files")
    return log_files

def identify_cache_mode(log_file):
    """Try to identify which cache mode was used for a log file"""
    # From the log file path
    path = log_file.lower()
    if "wt_hyb_full" in path or "wt_hyb_force_full" in path:
        return "WT_HYB_FORCE_FULL_ASS"
    elif "wt_hyb_set" in path or "wt_hyb_force_set" in path:
        return "WT_HYB_FORCE_SET_ASS"
    elif "wt_hyb" in path:
        # Generic hybrid cache (could be either mode)
        return "WT_HYB"
    elif "wt_results" in path or "wt/" in path or "/wt_" in path:
        return "WT"
    
    # Look in the file content for cache type
    try:
        with open(log_file, 'r') as f:
            first_lines = ''.join([f.readline() for _ in range(100)])  # Read first 100 lines
            if "DCacheType: config_pkg::WT_HYB_FORCE_FULL_ASS" in first_lines:
                return "WT_HYB_FORCE_FULL_ASS"
            elif "DCacheType: config_pkg::WT_HYB_FORCE_SET_ASS" in first_lines:
                return "WT_HYB_FORCE_SET_ASS"
            elif "DCacheType: config_pkg::WT" in first_lines:
                return "WT"
    except:
        pass
    
    # Default
    return "Unknown"

def analyze_log_file(log_file):
    """Analyze a single log file for execution details"""
    log_message(f"Analyzing log file: {log_file}")
    
    results = {
        'file': log_file,
        'cycles': None,
        'status': 'Unknown',
        'memory_increments': [],
        'tohost_value': None,
        'completion': False,
        'mode': identify_cache_mode(log_file)
    }
    
    try:
        with open(log_file, 'r') as f:
            content = f.read(10000000)  # Read up to 10MB to avoid memory issues
            
            # Check completion status
            if 'tohost = 1337' in content:
                results['status'] = 'Failed'
                results['tohost_value'] = 1337
            elif 'tohost = 0' in content:
                results['status'] = 'Passed'
                results['tohost_value'] = 0
                results['completion'] = True
            
            # Look for success/failure markers
            if "Test completed successfully" in content or "PASSED" in content or "test passed" in content:
                results['status'] = 'Passed'
                results['completion'] = True
            elif "Failed" in content or "FAILED" in content:
                results['status'] = 'Failed'
            
            # Extract cycle count
            cycle_match = re.search(r'after (\d+) cycles', content)
            if cycle_match:
                results['cycles'] = int(cycle_match.group(1))
            
            # Memory operations - find increments (0-9)
            # Check several patterns for memory writes
            patterns = [
                r'memory\[\w+\] = (\d)',                       # Basic pattern
                r'memory\[0x([0-9a-fA-F]+)\] = (\d+)',         # Address with data
                r'Store: addr=0x([0-9a-fA-F]+) data=(\d+)',    # Store instruction
                r'(?:ST|SW).*\[0x([0-9a-fA-F]+)\].*= (\d+)',   # Store/SW instruction
                r'MEM\[\w+\] <= (\d+)'                         # Memory update
            ]
            
            memory_ops = []
            addr_values = {}
            
            for pattern in patterns:
                if '[0x' in pattern:  # Pattern includes address
                    matches = re.findall(pattern, content)
                    for addr, value in matches:
                        memory_ops.append((addr, value))
                        if addr not in addr_values:
                            addr_values[addr] = []
                        addr_values[addr].append(int(value))
                else:  # Pattern is just values
                    matches = re.findall(pattern, content)
                    for value in matches:
                        memory_ops.append(value)
                        results['memory_increments'].append(value)
            
            # Check if values at any address show an incrementing pattern
            for addr, values in addr_values.items():
                if len(values) > 1:
                    # Check for consecutive integers
                    values.sort()
                    consecutive = all(values[i] == values[i-1]+1 for i in range(1, len(values)))
                    if consecutive and 0 in values and len(values) > 2:
                        results['incrementing_addr'] = addr
                        results['incrementing_values'] = values
                        break
            
            # Check "Hello World" output
            if "Hello World" in content or "hello, world" in content:
                results['hello_world_output'] = True
            
            # If completion status is still unknown but we have incrementing values, 
            # it's probably successful
            if results['status'] == 'Unknown' and results.get('incrementing_values'):
                results['status'] = 'Likely Passed'
                results['completion'] = True
            
    except Exception as e:
        log_message(f"Error processing file {log_file}: {e}")
        results['error'] = str(e)
    
    return results

def validate_execution(results):
    """Validate execution across different cache modes"""
    log_message("\nValidating execution across cache modes...")
    
    # Group by cache mode
    by_mode = {}
    for result in results:
        mode = result['mode']
        if mode not in by_mode:
            by_mode[mode] = []
        by_mode[mode].append(result)
    
    summary = {}
    
    # Analyze each mode
    for mode, mode_results in by_mode.items():
        passing = [r for r in mode_results if r['status'] in ('Passed', 'Likely Passed')]
        failing = [r for r in mode_results if r['status'] == 'Failed']
        unknown = [r for r in mode_results if r['status'] == 'Unknown']
        
        increments_found = any(r.get('incrementing_values') for r in mode_results)
        hello_world = any(r.get('hello_world_output') for r in mode_results)
        
        # Get performance from passing runs
        cycles = [r['cycles'] for r in passing if r['cycles'] is not None]
        avg_cycles = sum(cycles) / len(cycles) if cycles else None
        
        summary[mode] = {
            'total_runs': len(mode_results),
            'passing': len(passing),
            'failing': len(failing),
            'unknown': len(unknown),
            'increments_found': increments_found,
            'hello_world_output': hello_world,
            'avg_cycles': avg_cycles,
            'min_cycles': min(cycles) if cycles else None,
            'max_cycles': max(cycles) if cycles else None,
            'validation': 'Passed' if passing and increments_found else 'Failed'
        }
        
    return summary

def generate_report(results, summary):
    """Generate a report of the log analysis"""
    log_message("\nGenerating analysis report...")
    
    report_path = OUTPUT_DIR / 'cache_log_analysis_report.md'
    with open(report_path, 'w') as f:
        f.write("# Cache Log Analysis Report\n\n")
        f.write(f"Generated on: {datetime.now()}\n\n")
        
        # Summary table
        f.write("## Summary\n\n")
        f.write("| Cache Type | Total Runs | Passing | Failing | Increments Found | Avg Cycles | Validation |\n")
        f.write("|------------|------------|---------|---------|------------------|------------|------------|\n")
        
        for mode, data in summary.items():
            avg_cycles = f"{data['avg_cycles']:.0f}" if data['avg_cycles'] else "N/A"
            f.write(f"| {mode} | {data['total_runs']} | {data['passing']} | {data['failing']} | {'Yes' if data['increments_found'] else 'No'} | {avg_cycles} | {data['validation']} |\n")
        
        f.write("\n## Detailed Results\n\n")
        
        # Detailed results for each cache type
        for mode, data in summary.items():
            f.write(f"### {mode}\n\n")
            f.write(f"- **Total Runs**: {data['total_runs']}\n")
            f.write(f"- **Passing**: {data['passing']}\n")
            f.write(f"- **Failing**: {data['failing']}\n")
            f.write(f"- **Unknown**: {data['unknown']}\n")
            f.write(f"- **Memory Increments Found**: {'Yes' if data['increments_found'] else 'No'}\n")
            f.write(f"- **Hello World Output**: {'Yes' if data['hello_world_output'] else 'No'}\n")
            
            if data['avg_cycles']:
                f.write(f"- **Average Cycles**: {data['avg_cycles']:.0f}\n")
                f.write(f"- **Min Cycles**: {data['min_cycles']}\n")
                f.write(f"- **Max Cycles**: {data['max_cycles']}\n")
            else:
                f.write("- **Cycles**: N/A\n")
            
            f.write(f"- **Validation**: {data['validation']}\n")
            f.write("\n")
        
        # List of all analyzed log files
        f.write("## Analyzed Log Files\n\n")
        for i, result in enumerate(results):
            f.write(f"{i+1}. **{result['mode']}**: {result['file']}\n")
            f.write(f"   - Status: {result['status']}\n")
            f.write(f"   - Cycles: {result['cycles']}\n")
            if result.get('incrementing_values'):
                f.write(f"   - Memory Increments: {result['incrementing_values']}\n")
            f.write("\n")
        
        # Final analysis
        f.write("## Analysis\n\n")
        all_passed = all(data['validation'] == 'Passed' for data in summary.values())
        if all_passed:
            f.write("🟢 **All cache implementations have successfully executed the hello_world.c test.**\n\n")
        else:
            failing_modes = [mode for mode, data in summary.items() if data['validation'] != 'Passed']
            f.write(f"🔴 **Some cache implementations have failed to execute the hello_world.c test properly: {', '.join(failing_modes)}**\n\n")
        
        # Performance comparison
        f.write("### Performance Comparison\n\n")
        modes_with_cycles = {mode: data for mode, data in summary.items() if data['avg_cycles'] is not None}
        if len(modes_with_cycles) > 1:
            # Find the fastest implementation
            fastest = min(modes_with_cycles.items(), key=lambda x: x[1]['avg_cycles'])
            
            f.write(f"The fastest implementation was **{fastest[0]}** with an average of {fastest[1]['avg_cycles']:.0f} cycles.\n\n")
            
            # Compare others to the fastest
            f.write("Relative performance:\n\n")
            for mode, data in modes_with_cycles.items():
                if mode != fastest[0]:
                    relative_perf = (data['avg_cycles'] / fastest[1]['avg_cycles']) * 100 - 100
                    f.write(f"- {mode}: {relative_perf:.2f}% slower than the fastest\n")
        elif len(modes_with_cycles) == 1:
            mode, data = next(iter(modes_with_cycles.items()))
            f.write(f"Only {mode} has cycle data with an average of {data['avg_cycles']:.0f} cycles.\n")
        else:
            f.write("Not enough data to compare performance.\n")
    
    log_message(f"Report generated at {report_path}")
    return report_path

def main():
    """Main function that analyzes log files"""
    log_message("Starting cache log analysis...")
    
    # Find relevant log files
    log_files = find_log_files()
    
    if not log_files:
        log_message("No log files found for analysis!")
        return
    
    # Analyze each log file
    results = []
    for log_file in log_files:
        result = analyze_log_file(log_file)
        results.append(result)
        log_message(f"  - {result['mode']}: {result['status']}, Cycles: {result['cycles']}, Increments: {'Yes' if result.get('incrementing_values') else 'No'}")
    
    # Validate execution
    summary = validate_execution(results)
    
    # Generate report
    report_path = generate_report(results, summary)
    
    log_message(f"\nAnalysis completed. Report available at: {report_path}")

if __name__ == "__main__":
    main()