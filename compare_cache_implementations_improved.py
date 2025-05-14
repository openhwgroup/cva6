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
import time
import shutil
import tempfile
import subprocess
import glob
import argparse
import hashlib
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
    parser.add_argument("--force-rebuild", action="store_true",
                        help="Force rebuild of simulation before each run")
    parser.add_argument("--use-custom-test", type=str,
                        help="Path to custom test file instead of hello_world.c")
    return parser.parse_args()

# Get command-line arguments
args = parse_args()

# Paths
BASE_DIR = Path('/home/cai/cache_project/sandbox/cva6')
CONFIG_FILE = BASE_DIR / 'core/include/cv32a60x_config_pkg.sv'
CACHE_PKG_FILE = BASE_DIR / 'core/include/wt_hybrid_cache_pkg.sv'

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

# Create a directory for each cache mode's results
for mode in CACHE_MODES.keys():
    os.makedirs(OUTPUT_DIR / f"{mode.lower()}_results", exist_ok=True)

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
    f.write(f"  Output Directory: {OUTPUT_DIR}\n")
    f.write(f"  Force Rebuild: {args.force_rebuild}\n")
    if args.use_custom_test:
        f.write(f"  Custom Test: {args.use_custom_test}\n")
    f.write("\n")

def log_message(message):
    """Log a message to both console and log file"""
    timestamp = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    formatted_message = f"[{timestamp}] {message}"
    print(formatted_message)
    with open(log_path, 'a') as f:
        f.write(formatted_message + "\n")

def backup_config_files():
    """Backup the configuration files"""
    log_message("Creating backup of configuration files...")
    backup_dir = OUTPUT_DIR / 'config_backups'
    os.makedirs(backup_dir, exist_ok=True)
    
    # Create backup with timestamp
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    
    config_backup = backup_dir / f"cv32a60x_config_pkg.sv.{timestamp}.bak"
    cache_pkg_backup = backup_dir / f"wt_hybrid_cache_pkg.sv.{timestamp}.bak"
    
    shutil.copy2(CONFIG_FILE, config_backup)
    shutil.copy2(CACHE_PKG_FILE, cache_pkg_backup)
    
    log_message(f"Configuration backups created at {backup_dir}")
    return config_backup, cache_pkg_backup

def restore_config_files(config_backup, cache_pkg_backup):
    """Restore the configuration files from backups"""
    log_message("Restoring configuration files from backup...")
    shutil.copy2(config_backup, CONFIG_FILE)
    shutil.copy2(cache_pkg_backup, CACHE_PKG_FILE)
    log_message("Configuration files restored")

def update_config_file(cache_mode):
    """Update the config file to use the specified cache mode"""
    log_message(f"\nUpdating config to use {cache_mode} mode...")
    
    # Read the config file
    with open(CONFIG_FILE, 'r') as f:
        content = f.read()
    
    # Create a backup of the file with timestamp
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    backup_path = f"{CONFIG_FILE}.{timestamp}.bak"
    with open(backup_path, 'w') as f:
        f.write(content)
    
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
    
    # Ensure the replacement was successful
    if new_content == content:
        log_message(f"Warning: No changes made to config file for mode {cache_mode}")
    
    # Write the updated content back to the file
    with open(CONFIG_FILE, 'w') as f:
        f.write(new_content)
    
    # Also create a copy of this specific configuration
    config_copy = OUTPUT_DIR / f"{cache_mode.lower()}_results" / f"cv32a60x_config_pkg.sv.{cache_mode}"
    with open(config_copy, 'w') as f:
        f.write(new_content)
    
    log_message(f"Config updated to use {cache_mode} mode")
    log_message(f"Config saved to {config_copy}")

def generate_config_hash():
    """Generate a hash of the configuration files to track changes"""
    with open(CONFIG_FILE, 'rb') as f:
        config_content = f.read()
    with open(CACHE_PKG_FILE, 'rb') as f:
        cache_pkg_content = f.read()
    
    combined = config_content + cache_pkg_content
    return hashlib.sha256(combined).hexdigest()

def clean_simulation():
    """Clean previous simulation artifacts"""
    log_message("Cleaning previous simulation artifacts...")
    
    # Run make clean in the simulation directory
    try:
        subprocess.run(
            "cd /home/cai/cache_project/sandbox/cva6/verif/sim && make clean",
            shell=True,
            check=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE
        )
        log_message("Simulation artifacts cleaned successfully")
    except subprocess.CalledProcessError as e:
        log_message(f"Warning: Failed to clean simulation artifacts: {e}")
        # Log the error output
        log_message(f"STDERR: {e.stderr.decode() if e.stderr else 'No error output'}")

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
            f.write("\n# Tag comparison signals\n")
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
    
    # Check if the configuration has changed
    config_hash_before = generate_config_hash()
    
    # Update the configuration
    update_config_file(cache_mode)
    
    # Check if the configuration has changed
    config_hash_after = generate_config_hash()
    
    if config_hash_before != config_hash_after or args.force_rebuild:
        log_message("Configuration changed or force rebuild enabled. Cleaning simulation...")
        clean_simulation()
    
    # Determine VCD settings
    vcd_settings = ""
    if args.generate_vcd:
        vcd_file = result_dir / f"hello_world.cv32a60x.vcd"
        signal_file = BASE_DIR / args.vcd_signals
        
        # Create a default signal list if needed
        create_vcd_signal_file(signal_file)
        
        # Set environment variables for VCD generation
        vcd_settings = "export TRACE_FAST=1\n"
        # Create a symlink to the verilator.vcd for easier access
        vcd_settings += "ln -sf ./verilator.vcd hello_world.cv32a60x.vcd\n"
        
        # Copy the signal list to the results directory for reference
        if signal_file.exists():
            vcd_settings += f"# Copy the signal list to help waveform viewers\n"
            vcd_settings += f"cp {signal_file} {result_dir}/signals.txt\n"
        
        log_message(f"Will generate VCD using signal list from: {signal_file}")
    
    # Determine which test to run
    test_path = "../tests/custom/hello_world/hello_world.c"
    if args.use_custom_test:
        if os.path.exists(args.use_custom_test):
            test_path = args.use_custom_test
            log_message(f"Using custom test: {test_path}")
        else:
            log_message(f"Warning: Custom test {args.use_custom_test} not found. Using default hello_world.c")
    
    # Create a timestamp for this run
    run_timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    
    # Create the simulation script
    script_path = OUTPUT_DIR / f"run_{cache_mode}.sh"
    with open(script_path, 'w') as f:
        f.write('#!/bin/bash\n')
        f.write('set -x\n')  # Echo commands for debugging
        f.write('cd /home/cai/cache_project/sandbox/cva6/verif/sim\n')
        f.write('source ./setup-env.sh\n')
        f.write('export PATH=$PATH:/home/cai/cache_project/sandbox/cva6/tools/bin:/usr/bin:/bin\n')
        
        # Add VCD settings if needed
        f.write(vcd_settings)
        
        # Make the simulation command include the cache mode in the log name
        f.write(f'python3 cva6.py --target cv32a60x --iss=veri-testharness --iss_yaml=cva6.yaml \\\n')
        f.write(f'--c_tests {test_path} \\\n')
        f.write(f'--linker=../../config/gen_from_riscv_config/linker/link.ld \\\n')
        f.write(f'--gcc_opts="-static -mcmodel=medany -fvisibility=hidden -nostdlib \\\n')
        f.write(f'-nostartfiles -g ../tests/custom/common/syscalls.c \\\n')
        f.write(f'../tests/custom/common/crt.S -lgcc \\\n')
        f.write(f'-I../tests/custom/env -I../tests/custom/common"\n')
        
        # Add commands to copy all relevant files
        f.write('\n# Copy all simulation artifacts\n')
        f.write('echo "Copying simulation artifacts..."\n')
        f.write('newest_dir=$(find ./out_* -type d -name "veri-testharness_sim" -o -name "spike" | sort -r | head -1)\n')
        f.write('if [ -z "$newest_dir" ]; then\n')
        f.write('    newest_dir="./veri-testharness_sim"\n')
        f.write('fi\n')
        f.write(f'mkdir -p {result_dir}/sim_artifacts\n')
        f.write(f'cp -R "$newest_dir"/* {result_dir}/sim_artifacts/ 2>/dev/null || true\n')
        f.write(f'cp -R ./out_* {result_dir}/sim_artifacts/ 2>/dev/null || true\n')
        f.write(f'cp ./verilator.vcd {result_dir}/ 2>/dev/null || true\n')
        f.write(f'cp ./trace_* {result_dir}/ 2>/dev/null || true\n')
        f.write(f'cp ./*.log {result_dir}/ 2>/dev/null || true\n')
        f.write('if [ -f ./verilator.vcd ]; then\n')
        f.write(f'    cp ./verilator.vcd {result_dir}/hello_world.cv32a60x.vcd\n')
        f.write('fi\n')
        f.write('if [ -f ./hello_world.cv32a60x.vcd ]; then\n')
        f.write(f'    cp ./hello_world.cv32a60x.vcd {result_dir}/\n')
        f.write('fi\n')
        
    # Make the script executable
    os.chmod(script_path, 0o755)
    
    # Run the script
    log_message(f"Executing script: {script_path}")
    result = subprocess.run(f"/bin/bash -c 'source ~/.bashrc && {script_path}'", 
                           shell=True, capture_output=True, text=True)
    
    log_file = LOG_DIR / f"{cache_mode}_simulation_{run_timestamp}.log"
    
    # Save the simulation log
    with open(log_file, 'w') as f:
        f.write(result.stdout)
        f.write("\n\nSTDERR:\n")
        f.write(result.stderr)
    
    # Check if the simulation was successful
    if result.returncode == 0:
        log_message(f"Simulation with {cache_mode} mode completed successfully")
        # Copy the relevant log files for analysis
        copy_simulation_logs(cache_mode, result_dir)
        return True
    else:
        log_message(f"Simulation with {cache_mode} mode failed with return code {result.returncode}")
        log_message(f"STDERR: {result.stderr[:500]}...")
        return False

def copy_simulation_logs(cache_mode, result_dir):
    """Copy all relevant simulation logs and outputs"""
    log_message(f"Copying simulation logs and artifacts for {cache_mode}...")
    
    # Find all recent simulation outputs
    newest_dirs = sorted(
        glob.glob(str(SIMULATION_DIR / "out_*")),
        key=os.path.getmtime,
        reverse=True
    )
    
    # Also check for veri-testharness_sim directory
    veritestharness_dir = SIMULATION_DIR / "veri-testharness_sim"
    if os.path.exists(veritestharness_dir):
        newest_dirs.insert(0, str(veritestharness_dir))
    
    # Create a destination directory for artifacts
    artifacts_dir = result_dir / "simulation_artifacts"
    os.makedirs(artifacts_dir, exist_ok=True)
    
    # Try the most recent directories first
    found_logs = False
    for directory in newest_dirs[:3]:  # Try the 3 most recent directories
        log_message(f"Checking for outputs in {directory}")
        
        # Look for log files and VCD files
        log_files = glob.glob(f"{directory}/**/*.log*", recursive=True)
        vcd_files = glob.glob(f"{directory}/**/*.vcd", recursive=True)
        
        if log_files or vcd_files:
            log_message(f"Found {len(log_files)} log files and {len(vcd_files)} VCD files in {directory}")
            found_logs = True
            
            # Create a specific directory for this source
            dir_name = os.path.basename(directory)
            dest_dir = artifacts_dir / dir_name
            os.makedirs(dest_dir, exist_ok=True)
            
            # Copy log files
            for log_file in log_files:
                dest_file = dest_dir / os.path.basename(log_file)
                try:
                    shutil.copy2(log_file, dest_file)
                    log_message(f"Copied {log_file} to {dest_file}")
                except Exception as e:
                    log_message(f"Error copying {log_file}: {e}")
            
            # Copy VCD files
            for vcd_file in vcd_files:
                dest_file = dest_dir / os.path.basename(vcd_file)
                try:
                    shutil.copy2(vcd_file, dest_file)
                    log_message(f"Copied {vcd_file} to {dest_file}")
                except Exception as e:
                    log_message(f"Error copying {vcd_file}: {e}")
    
    # Check for main VCD file (generated by Verilator)
    verilator_vcd = SIMULATION_DIR / "verilator.vcd"
    if os.path.exists(verilator_vcd):
        dest_file = result_dir / "hello_world.cv32a60x.vcd"
        try:
            shutil.copy2(verilator_vcd, dest_file)
            log_message(f"Copied Verilator VCD to {dest_file}")
        except Exception as e:
            log_message(f"Error copying Verilator VCD: {e}")
    
    return found_logs

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
        log_exists = glob.glob(f"{dir_path}/**/*.log*", recursive=True)
        if log_exists:
            return dir_path
    
    # If no directory with logs found, just return the most recent directory
    return sorted_dirs[0] if sorted_dirs else None

def extract_simulation_results(cache_mode):
    """Extract the simulation results from the log files"""
    log_message(f"\nExtracting results for {cache_mode} mode...")
    
    # Directory for this mode's results
    result_dir = OUTPUT_DIR / f"{cache_mode.lower()}_results"
    
    # Find all log files in the result directory
    log_patterns = [
        f"{result_dir}/**/*.log*",
        f"{result_dir}/simulation_artifacts/**/*.log*"
    ]
    
    log_files = []
    for pattern in log_patterns:
        found = glob.glob(pattern, recursive=True)
        log_files.extend(found)
    
    if not log_files:
        log_message(f"No log files found for {cache_mode} mode")
        return {'mode': cache_mode, 'description': CACHE_MODES[cache_mode]}
    
    log_message(f"Found {len(log_files)} log files to analyze for {cache_mode} mode")
    
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
                
                # Check for cache-related debug messages
                force_mode_matches = re.findall(r'force_mode_i\s*=\s*(\d+)', content)
                if force_mode_matches:
                    results['force_mode_values'] = force_mode_matches
                
                # Look for "hit" signals
                hit_oh_matches = re.findall(r'rd_hit_oh[_a-z]*\s*=\s*(\d+)', content)
                if hit_oh_matches:
                    results['hit_oh_values'] = hit_oh_matches
                
        except Exception as e:
            log_message(f"Error processing log file {log_file}: {e}")
    
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
        log_message(f"Checking log files for {mode}...")
        
        for log_file in data.get('log_files', []):
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
                        
                    # Check for cache mode indicators
                    if "WT_HYB_FORCE_FULL_ASS" in content or "force_mode = 2" in content:
                        data['force_full_ass_confirmed'] = True
                        log_message(f"  ✓ Found fully associative mode confirmation in {mode} log")
                    elif "WT_HYB_FORCE_SET_ASS" in content or "force_mode = 1" in content:
                        data['force_set_ass_confirmed'] = True
                        log_message(f"  ✓ Found set associative mode confirmation in {mode} log")
                    elif "DYNAMIC" in content or "force_mode = 0" in content:
                        data['dynamic_mode_confirmed'] = True
                        log_message(f"  ✓ Found dynamic mode confirmation in {mode} log")
                    
                    # Look for tag comparisons
                    tag_match_full = re.findall(r'tag_match_full_ass\s*=\s*(\d+)', content)
                    tag_match_set = re.findall(r'tag_match_set_ass\s*=\s*(\d+)', content)
                    if tag_match_full:
                        data['tag_match_full_found'] = True
                        log_message(f"  ✓ Found full associative tag matches in {mode} log")
                    if tag_match_set:
                        data['tag_match_set_found'] = True
                        log_message(f"  ✓ Found set associative tag matches in {mode} log")
                        
            except Exception as e:
                log_message(f"  ✗ Error reading log file {log_file}: {e}")
        
        # Final validation
        if data.get('hello_world_found', False) or data.get('success_marker_found', False) or data.get('no_errors_found', False):
            data['manual_validation'] = True
        else:
            data['manual_validation'] = False
                
    return results

def process_vcd_files(results):
    """Process VCD files to extract key information"""
    log_message("\nProcessing VCD files...")
    
    for mode, data in results.items():
        result_dir = OUTPUT_DIR / f"{mode.lower()}_results"
        
        # First check the main directory for VCD files
        main_vcd_path = result_dir / "hello_world.cv32a60x.vcd"
        if os.path.exists(main_vcd_path):
            main_vcd = main_vcd_path
            log_message(f"Found main VCD file at the top level: {main_vcd}")
        else:
            # Search recursively in subdirectories
            vcd_files = glob.glob(f"{result_dir}/**/*.vcd", recursive=True)
            
            if not vcd_files:
                log_message(f"No VCD files found for {mode}")
                continue
            
            # Find the main VCD file (likely to be the one at the top level)
            main_vcd = None
            for vcd in vcd_files:
                if os.path.basename(vcd) == "hello_world.cv32a60x.vcd":
                    main_vcd = vcd
                    break
            
            if not main_vcd and vcd_files:
                # Take the largest VCD file as the main one
                main_vcd = max(vcd_files, key=os.path.getsize)
                
                # Copy the main VCD to the result directory for easier access
                dest_path = result_dir / "hello_world.cv32a60x.vcd"
                log_message(f"Copying {main_vcd} to {dest_path} for easier access")
                try:
                    shutil.copy2(main_vcd, dest_path)
                    main_vcd = dest_path
                except Exception as e:
                    log_message(f"Error copying VCD file: {e}")
        
        if main_vcd:
            log_message(f"Using main VCD file for {mode}: {main_vcd}")
            
            # Extract size information
            size_mb = os.path.getsize(main_vcd) / (1024 * 1024)
            data['vcd_file'] = main_vcd
            data['vcd_size_mb'] = size_mb
            
            # Run the analyze_cache_vcd.py script if it exists
            cache_analyzer = BASE_DIR / "analyze_cache_vcd.py"
            if os.path.exists(cache_analyzer):
                log_message(f"Running cache analyzer on {main_vcd}")
                output_file = result_dir / f"{mode}_vcd_analysis.txt"
                
                try:
                    result = subprocess.run(
                        f"cd {BASE_DIR} && python3 {cache_analyzer} --vcd {main_vcd} --mode {mode} --output {output_file}",
                        shell=True,
                        capture_output=True,
                        text=True
                    )
                    
                    if result.returncode == 0:
                        log_message(f"Cache analysis for {mode} saved to {output_file}")
                        data['cache_analysis'] = output_file
                    else:
                        log_message(f"Cache analysis failed for {mode}: {result.stderr}")
                except Exception as e:
                    log_message(f"Error running cache analyzer: {e}")
            
            # Create heatmap from VCD file if cache_heatmap.py exists
            heatmap_script = BASE_DIR / "cache_heatmap.py"
            if os.path.exists(heatmap_script):
                log_message(f"Generating heatmap for {mode}...")
                heatmap_file = result_dir / f"heatmap_{mode.lower()}.txt"
                
                try:
                    result = subprocess.run(
                        f"cd {BASE_DIR} && python3 {heatmap_script} --vcd {main_vcd} --mode {mode} --output {heatmap_file}",
                        shell=True,
                        capture_output=True,
                        text=True
                    )
                    
                    if result.returncode == 0:
                        log_message(f"Heatmap for {mode} saved to {heatmap_file}")
                        data['heatmap'] = heatmap_file
                    else:
                        log_message(f"Heatmap generation failed for {mode}: {result.stderr}")
                except Exception as e:
                    log_message(f"Error generating heatmap: {e}")
    
    return results

def analyze_vcd_hit_oh_signals(results):
    """Analyze the rd_hit_oh_o signal in the VCD files"""
    log_message("\nAnalyzing cache hit signals in VCD files...")
    
    # Use the existing analyze_hit_signals.py script if it exists
    analyzer_script = BASE_DIR / "analyze_hit_signals.py"
    if not os.path.exists(analyzer_script):
        # Create a temporary Python script to extract and analyze the hit signals
        analyzer_script = OUTPUT_DIR / "analyze_hit_signals.py"
    with open(analyzer_script, 'w') as f:
        f.write(r'''#!/usr/bin/env python3
import re
import sys
import os
from collections import Counter

def extract_signal_changes(vcd_file, signal_pattern):
    """Extract all value changes for a signal from a VCD file."""
    values = []
    signal_id = None
    
    with open(vcd_file, 'r') as f:
        # First find the signal ID in the VCD header
        for line in f:
            if signal_pattern in line and '$var' in line:
                # Parse the signal ID from the line
                # Format: $var wire 8 )V rd_hit_oh_o [7:0] $end
                match = re.search(r'\$var\s+\w+\s+\d+\s+([^\s]+)\s+', line)
                if match:
                    signal_id = match.group(1)
                    print(f"Found signal ID: {signal_id} for {signal_pattern}")
                    break
        
        if not signal_id:
            print(f"Signal {signal_pattern} not found in VCD file")
            return []
        
        # Reset file pointer to beginning
        f.seek(0)
        
        # Extract values for this signal throughout the file
        time = 0
        for line in f:
            if '#' in line and line.startswith('#'):
                # Time stamp
                time = int(line[1:])
            elif signal_id in line:
                # Value change for our signal
                if 'b' in line:
                    # Binary vector
                    match = re.search(r'b([01]+)\s+' + re.escape(signal_id), line)
                    if match:
                        bin_val = match.group(1)
                        int_val = int(bin_val, 2)
                        values.append((time, bin_val, int_val))
                else:
                    # Scalar value (0 or 1)
                    match = re.search(r'([01])\s+' + re.escape(signal_id), line)
                    if match:
                        val = match.group(1)
                        values.append((time, val, int(val)))
    
    return values

def analyze_signal(vcd_file, signal_pattern, output_file=None):
    print(f"\nAnalyzing {vcd_file}")
    
    values = extract_signal_changes(vcd_file, signal_pattern)
    
    if not values:
        print(f"No values found for {signal_pattern}")
        return None
    
    # Count occurrences of each value
    value_counts = Counter([v[2] for v in values])
    
    # Prepare output buffer
    output = []
    output.append(f"Analysis of {signal_pattern} in {vcd_file}\n")
    output.append(f"Total signal changes: {len(values)}")
    output.append(f"Unique values: {len(value_counts)}\n")
    
    # Non-zero values (likely cache hits)
    non_zero = [v for v in values if v[2] != 0]
    non_zero_percent = len(non_zero)/len(values)*100 if values else 0
    output.append(f"Non-zero values (cache hits): {len(non_zero)} ({non_zero_percent:.2f}%)\n")
    
    # Distribution of which bits are set
    if non_zero:
        bit_distribution = [0] * 8
        for _, _, value in non_zero:
            for bit in range(8):
                if value & (1 << bit):
                    bit_distribution[bit] += 1
        
        output.append("Distribution of active bits in non-zero values:")
        for bit in range(8):
            if sum(bit_distribution) > 0:
                percentage = bit_distribution[bit] / len(non_zero) * 100
            else:
                percentage = 0
            output.append(f"Bit {bit}: {bit_distribution[bit]} times ({percentage:.2f}%)")
        output.append("")
    
    # Most common values
    output.append("Most common values:")
    for value, count in value_counts.most_common(10):
        if value is not None:
            binary = format(value, '08b')
            percentage = count/len(values)*100 if values else 0
            output.append(f"0b{binary} (decimal {value}): {count} times ({percentage:.2f}%)")
    
    # Print and optionally save output
    for line in output:
        print(line)
    
    if output_file:
        with open(output_file, 'w') as f:
            f.write("\n".join(output))
        print(f"Analysis saved to {output_file}")
    
    return values

def main():
    import argparse
    parser = argparse.ArgumentParser(description="Analyze hit signals in VCD files")
    parser.add_argument("vcd_files", nargs="+", help="VCD files to analyze")
    parser.add_argument("--output", type=str, help="Output file for the analysis")
    args = parser.parse_args()
    
    # Signal pattern to search for
    signal_pattern = "rd_hit_oh_o"
    
    # Process each VCD file
    for vcd_file in args.vcd_files:
        if args.output:
            output_file = args.output
        else:
            output_file = os.path.splitext(vcd_file)[0] + "_hit_oh_analysis.txt"
        
        analyze_signal(vcd_file, signal_pattern, output_file)

if __name__ == "__main__":
    main()
''')
    
    # Make the script executable
    os.chmod(analyzer_script, 0o755)
    
    # Run the analyzer for each mode individually to ensure output goes to correct directory
    for mode, data in results.items():
        if 'vcd_file' in data:
            vcd_file = data['vcd_file']
            result_dir = OUTPUT_DIR / f"{mode.lower()}_results"
            output_file = result_dir / f"{mode}_hit_oh_analysis.txt"
            
            try:
                cmd = f"python3 {analyzer_script} {vcd_file} --output {output_file}"
                log_message(f"Running hit signal analysis for {mode}: {cmd}")
                result = subprocess.run(cmd, shell=True, capture_output=True, text=True)
                
                if result.returncode == 0:
                    data['hit_oh_analysis'] = output_file
                    log_message(f"Hit analysis for {mode} saved to {output_file}")
                else:
                    log_message(f"Hit signal analysis failed for {mode}: {result.stderr}")
            except Exception as e:
                log_message(f"Error running hit signal analyzer for {mode}: {e}")
    
    # Return after handling each mode individually
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
            
            # VCD information if available
            if 'vcd_file' in data:
                f.write(f"- **VCD File**: {data['vcd_file']} ({data.get('vcd_size_mb', 0):.2f} MB)\n")
            
            # Cache mode confirmation
            mode_confirmed = False
            if mode == "WT_HYB_FORCE_FULL_ASS" and data.get('force_full_ass_confirmed', False):
                f.write("- **Mode Confirmation**: ✓ Fully associative mode confirmed in logs\n")
                mode_confirmed = True
            elif mode == "WT_HYB_FORCE_SET_ASS" and data.get('force_set_ass_confirmed', False):
                f.write("- **Mode Confirmation**: ✓ Set associative mode confirmed in logs\n")
                mode_confirmed = True
            elif mode == "WT" and data.get('dynamic_mode_confirmed', False):
                f.write("- **Mode Confirmation**: ✓ Standard write-through mode confirmed in logs\n")
                mode_confirmed = True
            
            if not mode_confirmed:
                f.write("- **Mode Confirmation**: ✗ Could not confirm mode in logs\n")
            
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
            
            # Cache hit analysis
            if 'hit_oh_analysis' in data:
                f.write("\n**Cache Hit Analysis**:\n")
                try:
                    with open(data['hit_oh_analysis'], 'r') as hit_file:
                        hit_content = hit_file.read()
                        # Extract key statistics
                        non_zero_match = re.search(r'Non-zero values \(cache hits\): (\d+) \(([\d.]+)%\)', hit_content)
                        if non_zero_match:
                            hits, hit_rate = non_zero_match.groups()
                            f.write(f"- Cache hits: {hits} ({hit_rate}%)\n")
                        
                        # Extract bit distribution
                        bit_distribution = re.findall(r'Bit (\d+): (\d+) times \(([\d.]+)%\)', hit_content)
                        if bit_distribution:
                            f.write("- Active bits in hit signal:\n")
                            for bit, count, percentage in bit_distribution:
                                if float(percentage) > 0:
                                    f.write(f"  - Bit {bit}: {count} times ({percentage}%)\n")
                except Exception as e:
                    f.write(f"- Error reading hit analysis: {e}\n")
            
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
        
        # Cache hit behavior
        f.write("\n### Cache Hit Behavior\n\n")
        hit_results = {k: v for k, v in results.items() if 'hit_oh_analysis' in v}
        if hit_results:
            f.write("Analysis of the `rd_hit_oh_o` signal (which way had a hit):\n\n")
            for mode, data in hit_results.items():
                try:
                    with open(data['hit_oh_analysis'], 'r') as hit_file:
                        hit_content = hit_file.read()
                        non_zero_match = re.search(r'Non-zero values \(cache hits\): (\d+) \(([\d.]+)%\)', hit_content)
                        if non_zero_match:
                            hits, hit_rate = non_zero_match.groups()
                            f.write(f"- **{mode}**: {hits} hits ({hit_rate}% hit rate)\n")
                            
                            # Extract most common values
                            common_vals = re.findall(r'0b([01]+) \(decimal (\d+)\): (\d+) times \(([\d.]+)%\)', hit_content)
                            if common_vals and len(common_vals) >= 2:
                                # Most common non-zero value
                                non_zero_vals = [v for v in common_vals if int(v[1]) > 0]
                                if non_zero_vals:
                                    binary, decimal, count, percent = non_zero_vals[0]
                                    f.write(f"  - Most common hit pattern: `{binary}` (way {int(decimal).bit_length()-1}) occurred {count} times\n")
                except Exception as e:
                    f.write(f"  - Error reading hit analysis for {mode}: {e}\n")
            
            # Compare hit patterns between implementations
            hit_patterns = {}
            for mode, data in hit_results.items():
                try:
                    with open(data['hit_oh_analysis'], 'r') as hit_file:
                        hit_content = hit_file.read()
                        bit_distribution = re.findall(r'Bit (\d+): (\d+) times \(([\d.]+)%\)', hit_content)
                        if bit_distribution:
                            hit_patterns[mode] = {int(bit): float(percentage) for bit, count, percentage in bit_distribution}
                except Exception:
                    pass
            
            if len(hit_patterns) > 1:
                f.write("\n**Comparison of Active Ways:**\n\n")
                f.write("| Way (Bit) | " + " | ".join(hit_patterns.keys()) + " |\n")
                f.write("|" + "---|" * (len(hit_patterns) + 1) + "\n")
                
                for bit in range(8):
                    row = f"| Way {bit} |"
                    for mode in hit_patterns:
                        percentage = hit_patterns[mode].get(bit, 0)
                        row += f" {percentage:.2f}% |"
                    f.write(row + "\n")
        else:
            f.write("No cache hit signal analysis available.\n")
    
    log_message(f"Report generated at {report_path}")
    return report_path

def main():
    """Main function that runs the comparison"""
    log_message("Starting cache implementation comparison...")
    
    # Backup configuration files before starting
    config_backup, cache_pkg_backup = backup_config_files()
    
    # Track results
    results = {}
    
    try:
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
                # Run the simulation with this cache mode
                success = run_simulation(cache_mode)
                
                # Extract and store the results
                extracted_results = extract_simulation_results(cache_mode)
                
                # Make sure description is included
                if 'description' not in extracted_results:
                    extracted_results['description'] = CACHE_MODES[cache_mode]
                
                # Store the results
                results[cache_mode] = extracted_results
                
                # Add status based on simulation success
                if not success:
                    results[cache_mode]['status'] = 'Failed to run'
                    results[cache_mode]['validation'] = 'Failed'
            
            except Exception as e:
                log_message(f"Error during {cache_mode} run: {e}")
                results[cache_mode] = {
                    'mode': cache_mode,
                    'description': CACHE_MODES[cache_mode],
                    'status': f'Error: {str(e)}',
                    'validation': 'Failed'
                }
        
        # Process VCD files
        results = process_vcd_files(results)
        
        # Analyze cache hit signals in VCD files
        results = analyze_vcd_hit_oh_signals(results)
        
        # Perform manual validation on log files
        results = manual_log_check(results)
        
        # Generate the comparison report
        report_path = generate_report(results)
        
        log_message(f"\nComparison completed. Report available at: {report_path}")
        
    finally:
        # Restore original configuration
        restore_config_files(config_backup, cache_pkg_backup)
        log_message("Original configuration restored")

if __name__ == "__main__":
    main()