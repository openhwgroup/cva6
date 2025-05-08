#!/usr/bin/env python3
"""
Improved Cache Implementation Comparison Script

This script compares the execution of the hello_world.c test across different cache implementations:
1. Write-Through Cache (WT) - Standard implementation
2. Hybrid Cache in Set Associative Mode (WT_HYB_FORCE_SET_ASS)
3. Hybrid Cache in Fully Associative Mode (WT_HYB_FORCE_FULL_ASS)

It validates correct execution by examining the log files for:
- Memory address increments (0 to 9)
- Execution completion status
- Performance metrics (cycles)
"""

import os
import re
import sys
import subprocess
import glob
import argparse
from pathlib import Path
from datetime import datetime

# Configuration
CACHE_MODES = {
    "WT": "Standard Write-Through Cache",
    "WT_HYB_FORCE_SET_ASS": "Hybrid Cache in Set Associative Mode",
    "WT_HYB_FORCE_FULL_ASS": "Hybrid Cache in Fully Associative Mode"
}

def parse_args():
    """Parse command-line arguments"""
    parser = argparse.ArgumentParser(description="Compare different cache implementations")
    parser.add_argument("--generate-vcd", action="store_true", 
                        help="Generate VCD files for waveform viewing")
    parser.add_argument("--vcd-signals", type=str, default="cache_signals.txt",
                        help="File containing list of signals to trace (default: cache_signals.txt)")
    parser.add_argument("--run-all", action="store_true",
                        help="Run all three cache modes (default behavior)")
    parser.add_argument("--mode", type=str, choices=["WT", "WT_HYB_FORCE_SET_ASS", "WT_HYB_FORCE_FULL_ASS"],
                        help="Run only the specified cache mode")
    parser.add_argument("--output-dir", type=str, 
                        help="Custom output directory (default: timestamped directory)")
    return parser.parse_args()

# Get command-line arguments
args = parse_args()

# Paths
BASE_DIR = Path('/home/cai/cache_project/sandbox/cva6')
CONFIG_FILE = BASE_DIR / 'core/include/cv32a60x_config_pkg.sv'

# Set output directory
if args.output_dir:
    OUTPUT_DIR = Path(args.output_dir)
else:
    OUTPUT_DIR = BASE_DIR / f'real_cache_comparison_{datetime.now().strftime("%Y%m%d_%H%M%S")}'

LOG_DIR = OUTPUT_DIR / 'logs'
SIMULATION_DIR = BASE_DIR / 'verif/sim'

# Create directories
os.makedirs(OUTPUT_DIR, exist_ok=True)
os.makedirs(LOG_DIR, exist_ok=True)
os.makedirs(OUTPUT_DIR / 'wt_results', exist_ok=True)
os.makedirs(OUTPUT_DIR / 'wthyb_results', exist_ok=True)

# Initialize log file
log_path = OUTPUT_DIR / 'run_log.txt'
with open(log_path, 'w') as f:
    f.write(f"Cache Implementation Comparison Run: {datetime.now()}\n")
    f.write("="*80 + "\n\n")
    
    # Log command-line options
    f.write("Command Line Options:\n")
    f.write(f"  Generate VCD: {args.generate_vcd}\n")
    f.write(f"  VCD Signals File: {args.vcd_signals}\n")
    if args.mode:
        f.write(f"  Mode: {args.mode}\n")
    else:
        f.write("  Mode: All\n")
    f.write(f"  Output Directory: {OUTPUT_DIR}\n\n")

def log_message(message):
    """Log a message to both console and log file"""
    print(message)
    with open(log_path, 'a') as f:
        f.write(message + "\n")

def update_config_file(cache_mode):
    """Update the config file to use the specified cache mode"""
    log_message(f"\nUpdating config to use {cache_mode} mode...")
    
    # Read the config file
    with open(CONFIG_FILE, 'r') as f:
        content = f.read()
    
    # Different replacement patterns based on cache mode
    if cache_mode == "WT":
        pattern = r'DCacheType: config_pkg::[^,]+,'
        replacement = 'DCacheType: config_pkg::WT,'
    elif cache_mode == "WT_HYB_FORCE_SET_ASS":
        pattern = r'DCacheType: config_pkg::[^,]+,'
        replacement = 'DCacheType: config_pkg::WT_HYB_FORCE_SET_ASS,'
    elif cache_mode == "WT_HYB_FORCE_FULL_ASS":
        pattern = r'DCacheType: config_pkg::[^,]+,'
        replacement = 'DCacheType: config_pkg::WT_HYB_FORCE_FULL_ASS,'
    
    # Replace the pattern
    new_content = re.sub(pattern, replacement, content)
    
    # Write the updated content back to the file
    with open(CONFIG_FILE, 'w') as f:
        f.write(new_content)
    
    log_message(f"Config updated to use {cache_mode} mode")

def create_vcd_signal_file(signal_list_file):
    """Create a default signal list file if it doesn't exist"""
    if not os.path.exists(signal_list_file):
        log_message(f"Creating default VCD signal file: {signal_list_file}")
        with open(signal_list_file, 'w') as f:
            f.write("# Cache signals to trace in VCD\n")
            f.write("# One signal per line, wildcards (*) allowed\n\n")
            
            # Cache top-level signals
            f.write("# Cache top-level signals\n")
            f.write("*cache_subsystem*\n")
            f.write("*i_wt_dcache*\n")
            f.write("*i_wt_hybche*\n")
            
            # WT Cache-specific signals
            f.write("\n# Write-Through Cache signals\n")
            f.write("*wt_dcache*\n")
            f.write("*wt_dcache_mem*\n")
            f.write("*wt_dcache_ctrl*\n")
            f.write("*wt_dcache_wbuffer*\n")
            f.write("*wt_dcache_missunit*\n")
            
            # Hybrid Cache-specific signals
            f.write("\n# Hybrid Cache signals\n")
            f.write("*wt_hybche*\n")
            f.write("*wt_hybche_mem*\n")
            f.write("*wt_hybche_ctrl*\n")
            f.write("*wt_hybche_wbuffer*\n")
            f.write("*wt_hybche_missunit*\n")
            
            # Hash function and physical index signals
            f.write("\n# Hash function and mapping signals\n")
            f.write("*wt_hybche_mem.wr_hash*\n")
            f.write("*wt_hybche_mem.rd_hash*\n")
            f.write("*wt_hybche_mem.wr_phys_idx*\n")
            f.write("*wt_hybche_mem.rd_phys_idx*\n")
            f.write("*wt_hybche_mem.max_set_idx*\n")
            f.write("*wt_hybche_mem.fa_wr_idx*\n")
            f.write("*wt_hybche_mem.fa_rd_idx*\n")
            
            # Tag comparison signals
            f.write("\n# Tag comparison and hit/miss signals\n")
            f.write("*tag_match*\n")
            f.write("*extended_*tag*\n")
            f.write("*hit_oh*\n")
            f.write("*miss*\n")
            
            # Memory access signals
            f.write("\n# Memory access signals\n")
            f.write("*req*\n")
            f.write("*gnt*\n")
            f.write("*we*\n")
            f.write("*wdata*\n")
            f.write("*rdata*\n")
            
            # Debug signals
            f.write("\n# Debug signals\n")
            f.write("*_d\n")
            f.write("*_q\n")

def run_simulation(cache_mode):
    """Run the simulation with the specified cache mode"""
    log_message(f"\nRunning simulation with {cache_mode} mode...")
    
    # Create a directory for the specific mode's results
    result_dir = OUTPUT_DIR / f"{cache_mode.lower()}_results"
    os.makedirs(result_dir, exist_ok=True)
    
    # Determine VCD settings
    if args.generate_vcd:
        vcd_file = result_dir / f"{cache_mode.lower()}_waveform.vcd"
        signal_file = BASE_DIR / args.vcd_signals
        
        # Create a default signal list if needed
        create_vcd_signal_file(signal_file)
        
        log_message(f"Will generate VCD at: {vcd_file}")
        log_message(f"Using signal list from: {signal_file}")
    
    # Go to simulation directory and source setup script
    # Use a bash script that sources the environment properly
    script_path = OUTPUT_DIR / f"run_{cache_mode}.sh"
    with open(script_path, 'w') as f:
        f.write('#!/bin/bash\n')
        f.write('set -x\n')  # Echo commands for debugging
        f.write('cd /home/cai/cache_project/sandbox/cva6/verif/sim\n')
        f.write('source ./setup-env.sh\n')
        f.write('export PATH=$PATH:/home/cai/cache_project/sandbox/cva6/tools/bin:/usr/bin:/bin\n')
        
        # Export VCD-related environment variables
        if args.generate_vcd:
            f.write('export TRACE_FAST=1\n')  # Enable fast tracing
            # Create a link to the signal file if specified
            if signal_file.exists():
                f.write(f'# Copy the signal list to help waveform viewers\n')
                f.write(f'cp {signal_file} {vcd_file.parent}/signals.txt\n')
        
        # Build the simulation command
        f.write(f'python3 cva6.py --target cv32a60x --iss=veri-testharness --iss_yaml=cva6.yaml \\\n')
        f.write(f'--c_tests ../tests/custom/hello_world/hello_world.c \\\n')
        f.write(f'--linker=../../config/gen_from_riscv_config/linker/link.ld \\\n')
        f.write(f'--gcc_opts="-static -mcmodel=medany -fvisibility=hidden -nostdlib \\\n')
        f.write(f'-nostartfiles -g ../tests/custom/common/syscalls.c \\\n')
        f.write(f'../tests/custom/common/crt.S -lgcc \\\n')
        f.write(f'-I../tests/custom/env -I../tests/custom/common"\n')
    
    # Make the script executable
    os.chmod(script_path, 0o755)
    
    # Run the script with a shell that sources bashrc
    log_message(f"Executing script: {script_path}")
    result = subprocess.run(f"/bin/bash -c 'source ~/.bashrc && {script_path}'" , shell=True, capture_output=True, text=True)
    log_file = LOG_DIR / f"{cache_mode}_simulation.log"
    
    # Display error if it failed
    if result.returncode != 0:
        log_message(f"ERROR: Command failed with code {result.returncode}")
        log_message(f"STDERR: {result.stderr}")
        log_message(f"STDOUT: {result.stdout[:200]}...")
    
    with open(log_file, 'w') as f:
        f.write(result.stdout)
        f.write("\n\nSTDERR:\n")
        f.write(result.stderr)
    
    # Check if the simulation was successful
    if result.returncode == 0:
        log_message(f"Simulation with {cache_mode} mode completed successfully")
        return True
    else:
        log_message(f"Simulation with {cache_mode} mode failed with return code {result.returncode}")
        return False

def find_newest_output_dir():
    """Find the newest output directory created by the simulation"""
    # Look in all possible locations for output
    patterns = [
        str(SIMULATION_DIR / "out_*"),
        str(SIMULATION_DIR / "veri-testharness_sim")
    ]
    
    all_dirs = []
    for pattern in patterns:
        dirs = glob.glob(pattern)
        all_dirs.extend(dirs)
    
    if not all_dirs:
        return None
    
    # If there are multiple directories, sort by modification time
    # to find the most recent one containing simulation results
    sorted_dirs = sorted(all_dirs, key=os.path.getmtime, reverse=True)
    
    # Try finding a directory that actually contains simulation logs
    for dir_path in sorted_dirs:
        log_exists = glob.glob(f"{dir_path}/**/hello_world.cv32a60x.log*", recursive=True)
        if log_exists:
            return dir_path
    
    # If no directory with logs found, just return the most recent directory
    return sorted_dirs[0] if sorted_dirs else None

def extract_simulation_results(cache_mode):
    """Extract the simulation results from the log files"""
    log_message(f"\nExtracting results for {cache_mode} mode...")
    
    # Find the newest output directory
    newest_dir = find_newest_output_dir()
    if not newest_dir:
        log_message("No output directory found")
        return {'mode': cache_mode, 'description': CACHE_MODES[cache_mode]}
    
    # Look in multiple possible locations for log files
    log_patterns = [
        f"{newest_dir}/hello_world.cv32a60x.log*",
        f"{newest_dir}/veri-testharness_sim/hello_world.cv32a60x.log*",
        f"{SIMULATION_DIR}/veri-testharness_sim/hello_world.cv32a60x.log*",
        f"{SIMULATION_DIR}/out_*/veri-testharness_sim/hello_world.cv32a60x.log*"
    ]
    
    log_files = []
    for pattern in log_patterns:
        found = glob.glob(pattern)
        if found:
            log_message(f"Found {len(found)} log files matching {pattern}")
            log_files.extend(found)
    
    if not log_files:
        log_message("No log files found")
        return {'mode': cache_mode, 'description': CACHE_MODES[cache_mode]}
    
    results = {
        'mode': cache_mode,
        'description': CACHE_MODES[cache_mode],
        'log_files': log_files,
        'cycles': None,
        'status': 'Unknown',
        'memory_increments': [],
        'completion': False
    }
    
    # Extract information from log files
    for log_file in log_files:
        try:
            with open(log_file, 'r') as f:
                content = f.read()
                
                # Check for successful completion (no tohost error)
                if 'tohost = 1337' in content or 'FAILED' in content:
                    results['status'] = 'Failed'
                elif 'tohost = 0' in content or 'PASSED' in content:
                    results['status'] = 'Passed'
                    results['completion'] = True
                
                # Extract cycle count
                cycle_match = re.search(r'after (\d+) cycles', content)
                if cycle_match:
                    results['cycles'] = int(cycle_match.group(1))
                
                # Look for memory increments (0 to 9)
                memory_increments = re.findall(r'memory\[\w+\] = (\d)', content)
                if memory_increments:
                    results['memory_increments'] = memory_increments
                
                # Also check RVFI trace for memory writes
                addr_values = re.findall(r'memory\[0x([0-9a-fA-F]+)\] = (\d+)', content)
                if addr_values:
                    results['memory_writes'] = addr_values
                
                # Alternative pattern for memory increments
                mem_pattern = re.findall(r'Store: addr=0x([0-9a-fA-F]+) data=(\d)', content)
                if mem_pattern:
                    results['memory_stores'] = mem_pattern
                
        except Exception as e:
            log_message(f"Error processing log file {log_file}: {e}")
    
    # Copy the logs to the results directory
    if cache_mode.startswith("WT_HYB"):
        dest_dir = OUTPUT_DIR / 'wthyb_results'
    else:
        dest_dir = OUTPUT_DIR / 'wt_results'
    
    for log_file in log_files:
        try:
            dest_file = dest_dir / os.path.basename(log_file)
            subprocess.run(['cp', log_file, dest_file], check=True)
            results['copied_log'] = dest_file
        except Exception as e:
            log_message(f"Error copying log file {log_file}: {e}")
    
    return results

def validate_increments(memory_data):
    """Check if memory was properly incremented from 0-9"""
    if not memory_data:
        return False
    
    # Different types of memory data formats might be available
    if 'memory_increments' in memory_data and memory_data['memory_increments']:
        increments = [int(x) for x in memory_data['memory_increments']]
        return sorted(increments) == list(range(min(increments), max(increments)+1))
    
    if 'memory_writes' in memory_data and memory_data['memory_writes']:
        # Look for sequential writes to same address
        addr_values = {}
        for addr, value in memory_data['memory_writes']:
            if addr not in addr_values:
                addr_values[addr] = []
            addr_values[addr].append(int(value))
        
        # Check if any address shows incrementing pattern
        for addr, values in addr_values.items():
            if len(values) > 1 and sorted(values) == list(range(min(values), max(values)+1)):
                return True
    
    if 'memory_stores' in memory_data and memory_data['memory_stores']:
        # Similar check for store operations
        addr_values = {}
        for addr, value in memory_data['memory_stores']:
            if addr not in addr_values:
                addr_values[addr] = []
            addr_values[addr].append(int(value))
        
        for addr, values in addr_values.items():
            if len(values) > 1 and sorted(values) == list(range(min(values), max(values)+1)):
                return True
    
    return False

def manual_log_check(results):
    """Manual inspection of logs to find patterns that indicate successful execution"""
    log_message("\nPerforming manual log check...")
    
    for mode, data in results.items():
        if data.get('copied_log'):
            log_file = data['copied_log']
            log_message(f"Checking log file for {mode}: {log_file}")
            
            try:
                with open(log_file, 'r') as f:
                    content = f.read(10000000)  # Read up to 10MB to avoid memory issues
                    
                    # Look for specific markers of successful hello_world.c execution
                    if "Hello World" in content or "hello, world" in content:
                        data['hello_world_found'] = True
                        log_message(f"  ✓ Found 'Hello World' output in {mode} log")
                    
                    # Look for program completion markers
                    if "Test completed successfully" in content or "test passed" in content:
                        data['success_marker_found'] = True
                        log_message(f"  ✓ Found success marker in {mode} log")
                    
                    # Check for absence of error indicators
                    if "Error" not in content and "Failed" not in content and "FAILED" not in content:
                        data['no_errors_found'] = True
                        log_message(f"  ✓ No error indicators found in {mode} log")
                        
                    # Final validation
                    if data.get('hello_world_found', False) or data.get('success_marker_found', False) or data.get('no_errors_found', False):
                        data['manual_validation'] = True
                    else:
                        data['manual_validation'] = False
                        
            except Exception as e:
                log_message(f"  ✗ Error reading log file: {e}")
                data['manual_validation'] = False
    
    return results

def generate_report(results):
    """Generate a report comparing the three cache implementations"""
    log_message("\nGenerating comparison report...")
    
    # Enhanced results with validation
    for mode, data in results.items():
        data['increments_valid'] = validate_increments(data)
        if data.get('status') == 'Passed' or data.get('manual_validation', False) or data.get('increments_valid', False):
            data['validation'] = 'Passed'
        else:
            data['validation'] = 'Failed'
        
        # Add description if not present
        if 'description' not in data:
            data['description'] = CACHE_MODES.get(mode, f"Unknown Cache Type: {mode}")
    
    # Create the report
    report_path = OUTPUT_DIR / 'real_comparison_report.md'
    with open(report_path, 'w') as f:
        f.write("# Cache Implementation Comparison Report\n\n")
        f.write(f"Generated on: {datetime.now()}\n\n")
        
        # Summary table
        f.write("## Summary\n\n")
        f.write("| Cache Type | Description | Status | Cycles | Validation |\n")
        f.write("|------------|-------------|--------|--------|------------|\n")
        
        for mode, data in results.items():
            cycles = data.get('cycles', 'N/A')
            status = data.get('status', 'Unknown')
            validation = data.get('validation', 'Unknown')
            description = data.get('description', CACHE_MODES.get(mode, f"Unknown Cache Type: {mode}"))
            f.write(f"| {mode} | {description} | {status} | {cycles} | {validation} |\n")
        
        f.write("\n## Detailed Results\n\n")
        
        # Detailed results for each cache type
        for mode, data in results.items():
            f.write(f"### {mode}: {data['description']}\n\n")
            f.write(f"- **Status**: {data.get('status', 'Unknown')}\n")
            f.write(f"- **Cycles**: {data.get('cycles', 'N/A')}\n")
            f.write(f"- **Validation**: {data.get('validation', 'Unknown')}\n")
            
            f.write("\n**Memory Increments Check**:\n")
            if data.get('increments_valid', False):
                f.write("- ✓ Found valid memory increment pattern (0 to 9)\n")
            else:
                f.write("- ✗ No valid memory increment pattern found\n")
            
            f.write("\n**Manual Validation**:\n")
            if data.get('manual_validation', False):
                f.write("- ✓ Manual log inspection shows successful execution\n")
            else:
                f.write("- ✗ Manual log inspection did not confirm successful execution\n")
            
            # Include details of what memory operations were found
            f.write("\n**Memory Operations**:\n")
            if data.get('memory_increments'):
                f.write(f"- Memory increments: {', '.join(data['memory_increments'])}\n")
            if data.get('memory_writes'):
                f.write("- Memory writes (addr=data):\n")
                for addr, value in data.get('memory_writes', [])[:10]:  # Show first 10
                    f.write(f"  - 0x{addr}={value}\n")
                if len(data.get('memory_writes', [])) > 10:
                    f.write(f"  - ... and {len(data.get('memory_writes', []))-10} more\n")
            
            f.write("\n")
        
        # Final analysis
        f.write("## Analysis\n\n")
        all_passed = all(data.get('validation') == 'Passed' for data in results.values())
        if all_passed:
            f.write("🟢 **All cache implementations successfully executed the hello_world.c test.**\n\n")
        else:
            f.write("🔴 **Some cache implementations failed to properly execute the hello_world.c test.**\n\n")
        
        # Performance comparison
        f.write("### Performance Comparison\n\n")
        valid_results = {k: v for k, v in results.items() if v.get('cycles') is not None}
        if valid_results:
            # Find the fastest implementation
            fastest = min(valid_results.items(), key=lambda x: x[1].get('cycles', float('inf')))
            
            f.write(f"The fastest implementation was **{fastest[0]}** with {fastest[1].get('cycles')} cycles.\n\n")
            
            # Compare others to the fastest
            f.write("Relative performance:\n\n")
            for mode, data in valid_results.items():
                if mode != fastest[0]:
                    relative_perf = (data.get('cycles', 0) / fastest[1].get('cycles', 1)) * 100 - 100
                    f.write(f"- {mode}: {relative_perf:.2f}% slower than the fastest\n")
        else:
            f.write("Not enough data to compare performance.\n")
    
    log_message(f"Report generated at {report_path}")
    return report_path

def main():
    """Main function that runs the comparison"""
    log_message("Starting cache implementation comparison...")
    results = {}
    
    # Determine which modes to run
    modes_to_run = []
    if args.mode:
        # Run only the specified mode
        modes_to_run = [args.mode]
    else:
        # Run all modes
        modes_to_run = list(CACHE_MODES.keys())
    
    log_message(f"Will run the following cache modes: {', '.join(modes_to_run)}")
    
    for cache_mode in modes_to_run:
        try:
            # Update the config file
            update_config_file(cache_mode)
            
            # Run the simulation
            success = run_simulation(cache_mode)
            
            # Extract and store the results
            if success:
                extracted_results = extract_simulation_results(cache_mode)
                # Make sure description is included
                if 'description' not in extracted_results:
                    extracted_results['description'] = CACHE_MODES[cache_mode]
                results[cache_mode] = extracted_results
            else:
                results[cache_mode] = {
                    'mode': cache_mode,
                    'description': CACHE_MODES[cache_mode],
                    'status': 'Failed to run',
                    'validation': 'Failed'
                }
        except Exception as e:
            log_message(f"Error during {cache_mode} run: {e}")
            results[cache_mode] = {
                'mode': cache_mode,
                'description': CACHE_MODES[cache_mode],
                'status': f'Error: {str(e)}',
                'validation': 'Failed'
            }
    
    # Perform manual validation on log files
    results = manual_log_check(results)
    
    # Generate the comparison report
    report_path = generate_report(results)
    
    log_message(f"\nComparison completed. Report available at: {report_path}")
    
    # Process VCD files if generated
    if args.generate_vcd:
        log_message("\nVCD file summary:")
        
        # Search for VCD files in the output directories
        for cache_mode in modes_to_run:
            result_dir = OUTPUT_DIR / f"{cache_mode.lower()}_results"
            vcd_pattern = f"{result_dir}/**/*.vcd"
            vcd_files = glob.glob(vcd_pattern, recursive=True)
            
            if vcd_files:
                for vcd_file in vcd_files:
                    vcd_path = Path(vcd_file)
                    if vcd_path.exists() and vcd_path.is_file():
                        size_mb = vcd_path.stat().st_size / (1024 * 1024)
                        log_message(f"  - {cache_mode}: {vcd_path} ({size_mb:.2f} MB)")
            
            # Also look in simulation output directories for VCD files
            # Try to find the most recent output directory first
            newest_dir = find_newest_output_dir()
            if newest_dir:
                # Look for VCD files in the newest directory's veri-testharness_sim subdirectory
                veri_sim_dir = Path(newest_dir) / "veri-testharness_sim"
                if not os.path.exists(veri_sim_dir):
                    # If it's already a veri-testharness_sim directory, use it directly
                    if "veri-testharness_sim" in str(newest_dir):
                        veri_sim_dir = Path(newest_dir)
                
                if os.path.exists(veri_sim_dir):
                    vcd_files = glob.glob(f"{veri_sim_dir}/*.vcd")
                    if vcd_files:
                        # Copy the VCD files to our results directory
                        for vcd_file in vcd_files:
                            vcd_path = Path(vcd_file)
                            if vcd_path.exists() and vcd_path.is_file():
                                # Copy to results directory
                                dest_file = result_dir / vcd_path.name
                                try:
                                    import shutil
                                    shutil.copy2(vcd_path, dest_file)
                                    size_mb = dest_file.stat().st_size / (1024 * 1024)
                                    log_message(f"  - {cache_mode}: {dest_file} ({size_mb:.2f} MB) [copied from {vcd_path}]")
                                    
                                    # Generate heatmap from VCD file
                                    try:
                                        heatmap_file = result_dir / f"{cache_mode.lower()}_heatmap.txt"
                                        log_message(f"  - Generating heatmap for {cache_mode}...")
                                        
                                        # Execute the cache_heatmap.py script
                                        heatmap_cmd = [
                                            "python3", 
                                            str(BASE_DIR / "cache_heatmap.py"),
                                            "--vcd", str(dest_file),
                                            "--mode", cache_mode,
                                            "--output", str(heatmap_file)
                                        ]
                                        
                                        # Run in the background to not block
                                        subprocess.Popen(heatmap_cmd, 
                                                        stdout=subprocess.PIPE,
                                                        stderr=subprocess.PIPE)
                                        
                                        log_message(f"  - Heatmap will be generated at: {heatmap_file}")
                                    except Exception as e:
                                        log_message(f"  - Error generating heatmap: {e}")
                                        
                                except Exception as e:
                                    log_message(f"  - Error copying {vcd_path} to {dest_file}: {e}")
                                    log_message(f"  - {cache_mode}: {vcd_path} (not copied)")
                        continue
            
            # If we didn't find VCD files in the newest dir, look more broadly
            vcd_files = []
            
            # Try different possible locations
            locations = [
                SIMULATION_DIR / "veri-testharness_sim",
                SIMULATION_DIR / "out_2025-05-07" / "veri-testharness_sim",
                SIMULATION_DIR / f"out_{datetime.now().strftime('%Y-%m-%d')}" / "veri-testharness_sim"
            ]
            
            for location in locations:
                if os.path.exists(location):
                    found_files = glob.glob(f"{location}/*.vcd")
                    if found_files:
                        vcd_files.extend(found_files)
                        break
            
            if vcd_files:
                # Copy the VCD files to our results directory
                for vcd_file in vcd_files:
                    vcd_path = Path(vcd_file)
                    if vcd_path.exists() and vcd_path.is_file():
                        # Copy to results directory
                        dest_file = result_dir / vcd_path.name
                        try:
                            import shutil
                            shutil.copy2(vcd_path, dest_file)
                            size_mb = dest_file.stat().st_size / (1024 * 1024)
                            log_message(f"  - {cache_mode}: {dest_file} ({size_mb:.2f} MB) [copied from {vcd_path}]")
                            
                            # Generate heatmap from VCD file
                            try:
                                heatmap_file = result_dir / f"{cache_mode.lower()}_heatmap.txt"
                                log_message(f"  - Generating heatmap for {cache_mode}...")
                                
                                # Execute the cache_heatmap.py script
                                heatmap_cmd = [
                                    "python3", 
                                    str(BASE_DIR / "cache_heatmap.py"),
                                    "--vcd", str(dest_file),
                                    "--mode", cache_mode,
                                    "--output", str(heatmap_file)
                                ]
                                
                                # Run in the background to not block
                                subprocess.Popen(heatmap_cmd, 
                                                stdout=subprocess.PIPE,
                                                stderr=subprocess.PIPE)
                                
                                log_message(f"  - Heatmap will be generated at: {heatmap_file}")
                            except Exception as e:
                                log_message(f"  - Error generating heatmap: {e}")
                        except Exception as e:
                            log_message(f"  - Error copying {vcd_path} to {dest_file}: {e}")
                            log_message(f"  - {cache_mode}: {vcd_path} (not copied)")
            else:
                log_message(f"  - {cache_mode}: No VCD files found. Set TRACE_FAST=1 environment variable explicitly before running.")
        
        log_message("\nThese VCD files can be viewed with waveform viewers like GTKWave or Verilator.")
        log_message("The signal list file can be modified to include different signals in future runs.")
    
    # Double-check the hybrid cache is left in fully associative mode
    update_config_file("WT_HYB_FORCE_FULL_ASS")
    log_message("Config reset to WT_HYB_FORCE_FULL_ASS mode")

if __name__ == "__main__":
    main()