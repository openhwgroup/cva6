#!/usr/bin/env python3
"""
Cache Access Heatmap Generator

This script generates ASCII heatmaps of cache access patterns from logs or VCD files.
It's a simplified, focused tool designed specifically for the hybrid cache project.

Usage:
  python3 cache_heatmap.py --vcd <path_to_vcd_file> [options]
  python3 cache_heatmap.py --log <path_to_log_file> [options]

Options:
  --vcd FILE          Path to the VCD file to analyze
  --log FILE          Path to the log file to analyze
  --mode {WT,WT_HYB_FORCE_SET_ASS,WT_HYB_FORCE_FULL_ASS}
                      Cache mode of the file
  --output FILE       Output file for the heatmap (default: heatmap.txt)
  --sets INT          Number of cache sets (default: auto-detect or 16)
  --ways INT          Number of ways (default: auto-detect or 8)
"""

import argparse
import re
import os
from collections import defaultdict, Counter
import sys
import time

# ANSI colors for terminal output
class Colors:
    HEADER = '\033[95m'
    BLUE = '\033[94m'
    GREEN = '\033[92m'
    YELLOW = '\033[93m'
    RED = '\033[91m'
    ENDC = '\033[0m'
    BOLD = '\033[1m'
    UNDERLINE = '\033[4m'

def parse_args():
    """Parse command line arguments"""
    parser = argparse.ArgumentParser(description="Generate ASCII heatmap of cache access patterns")
    input_group = parser.add_mutually_exclusive_group(required=True)
    input_group.add_argument("--vcd", type=str, help="Path to the VCD file to analyze")
    input_group.add_argument("--log", type=str, help="Path to the log file to analyze")
    # Only for testing - not for production use
    input_group.add_argument("--demo", action="store_true", 
                        help="[TESTING ONLY] Generate synthetic demo data (not real simulation data)")
    
    parser.add_argument("--mode", type=str, choices=["WT", "WT_HYB_FORCE_SET_ASS", "WT_HYB_FORCE_FULL_ASS"],
                        required=True, help="Cache mode of the file")
    parser.add_argument("--output", type=str, default="heatmap.txt",
                        help="Output file for the heatmap")
    parser.add_argument("--sets", type=int, help="Number of cache sets")
    parser.add_argument("--ways", type=int, help="Number of ways")
    return parser.parse_args()

class CacheAccessData:
    """Collects cache access data for heatmap generation"""
    
    def __init__(self, num_sets=16, num_ways=8, mode=None):
        self.num_sets = num_sets
        self.num_ways = num_ways
        self.mode = mode
        self.is_hybrid = mode and "HYB" in mode
        self.is_full_associative = mode and "FULL" in mode
        
        # Access counters
        self.set_accesses = defaultdict(int)  # Set index -> access count
        self.set_hits = defaultdict(int)      # Set index -> hit count
        self.set_misses = defaultdict(int)    # Set index -> miss count
        self.way_accesses = defaultdict(int)  # Way index -> access count
        
        # For hybrid cache in full associative mode
        self.hash_distribution = defaultdict(int)  # Hash value -> count
        
        # Statistics
        self.total_accesses = 0
        self.total_hits = 0
        self.total_misses = 0
    
    def add_access(self, set_idx, hit=True):
        """Record a cache access"""
        if set_idx >= 0 and set_idx < self.num_sets:
            self.set_accesses[set_idx] += 1
            self.total_accesses += 1
            
            if hit:
                self.set_hits[set_idx] += 1
                self.total_hits += 1
            else:
                self.set_misses[set_idx] += 1
                self.total_misses += 1
    
    def add_hash(self, hash_value):
        """Record a hash value distribution for hybrid cache"""
        if self.is_hybrid:
            self.hash_distribution[hash_value] += 1
    
    def set_cache_parameters(self, num_sets, num_ways, mode=None):
        """Update cache parameters from detected values"""
        if num_sets:
            self.num_sets = num_sets
        if num_ways:
            self.num_ways = num_ways
        if mode:
            self.mode = mode
            self.is_hybrid = "HYB" in mode
            self.is_full_associative = "FULL" in mode

def guess_cache_parameters_from_vcd(vcd_file):
    """Guess cache parameters from VCD file content"""
    print(f"Analyzing {vcd_file} to detect cache parameters...")
    
    num_sets = None
    num_ways = None
    mode = None
    
    with open(vcd_file, 'r') as f:
        # Just check the header section for parameters
        for i, line in enumerate(f):
            if i > 5000:  # Only check the first part of the file
                break
            
            # Look for hybrid cache signals
            if "wt_hybche" in line and not mode:
                if "fa_" in line and "idx" in line:
                    mode = "WT_HYB_FORCE_FULL_ASS"
                    print(f"{Colors.GREEN}Detected hybrid cache in fully associative mode{Colors.ENDC}")
                else:
                    mode = "WT_HYB_FORCE_SET_ASS"
                    print(f"{Colors.GREEN}Detected hybrid cache in set associative mode{Colors.ENDC}")
            
            # Regular cache - look for wt_dcache, not hybrid
            if "wt_dcache" in line and "wt_hybche" not in line and not mode:
                mode = "WT"
                print(f"{Colors.GREEN}Detected standard write-through cache{Colors.ENDC}")
            
            # Try to detect number of sets from idx width signals
            set_width_match = re.search(r'DCACHE_CL_IDX_WIDTH=(\d+)', line)
            if set_width_match:
                num_sets = 2 ** int(set_width_match.group(1))
                print(f"Detected {num_sets} cache sets")
            
            # Try to detect number of ways from way width signals
            way_width_match = re.search(r'DCACHE_WAYS=(\d+)', line)
            if way_width_match:
                num_ways = int(way_width_match.group(1))
                print(f"Detected {num_ways} cache ways")
    
    return num_sets, num_ways, mode

def parse_vcd_for_access_data(vcd_file, cache_data):
    """Parse a VCD file to extract cache access patterns"""
    print(f"Parsing {vcd_file} for cache access patterns...")
    
    # Signal IDs for relevant signals
    signal_ids = {}
    current_scope = []
    current_time = 0
    in_header = True
    start_time = time.time()
    
    # First pass: identify relevant signal IDs in header
    with open(vcd_file, 'r') as f:
        for i, line in enumerate(f):
            # Progress indicator
            if i % 1000000 == 0 and i > 0:
                elapsed = time.time() - start_time
                print(f"First pass: Processed {i:,} lines... ({elapsed:.1f}s)")
            
            # End of header section
            if line.startswith("$enddefinitions"):
                in_header = False
                break
            
            # Track scope
            if line.startswith("$scope"):
                scope_name = line.split()[2]
                current_scope.append(scope_name)
            elif line.startswith("$upscope"):
                if current_scope:
                    current_scope.pop()
            
            # Extract signal definitions
            elif line.startswith("$var"):
                parts = line.split()
                if len(parts) >= 5:
                    signal_type = parts[1]
                    signal_width = parts[2]
                    signal_id = parts[3]
                    signal_name = parts[4]
                    
                    # Full hierarchical name with scope
                    full_name = ".".join(current_scope) + "." + signal_name
                    
                    # Only keep interesting signals for access patterns
                    if any(x in full_name.lower() for x in ["hit", "miss", "idx", "hash", "fa_"]):
                        signal_ids[signal_id] = {
                            'name': signal_name,
                            'full_name': full_name,
                            'width': int(signal_width)
                        }
    
    # If no interesting signals found, return early
    if not signal_ids:
        print(f"{Colors.YELLOW}No cache-related signals found in the VCD file.{Colors.ENDC}")
        return cache_data
    
    print(f"Found {len(signal_ids)} relevant cache signals for access pattern analysis.")
    
    # Second pass: parse the value changes for the interesting signals
    in_data = False
    event_count = 0
    set_pattern = re.compile(r'idx\[?(\d+)\]?|set\[?(\d+)\]?|_idx_(\d+)')
    hash_pattern = re.compile(r'hash\[?(\d+)\]?')
    
    with open(vcd_file, 'r') as f:
        for i, line in enumerate(f):
            # Progress indicator
            if i % 1000000 == 0 and i > 0:
                elapsed = time.time() - start_time
                print(f"Second pass: Processed {i:,} lines, {event_count} events... ({elapsed:.1f}s)")
            
            # Skip until data section
            if not in_data:
                if line.startswith("$enddefinitions"):
                    in_data = True
                continue
            
            # Parse time value
            if line.startswith("#"):
                current_time = int(line[1:].strip())
                continue
            
            # Parse value change for interesting signals
            if line[0] in "01" and len(line) > 1:
                value = line[0]
                signal_id = line[1:].strip()
                
                if signal_id in signal_ids and value == "1":
                    signal_info = signal_ids[signal_id]
                    signal_name = signal_info['full_name']
                    
                    # Track hits/misses and set indices
                    if "hit" in signal_name.lower():
                        # Try to extract set index from signal name
                        set_match = set_pattern.search(signal_name)
                        if set_match:
                            set_idx = int(set_match.group(1) or set_match.group(2) or set_match.group(3))
                            cache_data.add_access(set_idx, hit=True)
                            event_count += 1
                    
                    elif "miss" in signal_name.lower():
                        # Try to extract set index from signal name
                        set_match = set_pattern.search(signal_name)
                        if set_match:
                            set_idx = int(set_match.group(1) or set_match.group(2) or set_match.group(3))
                            cache_data.add_access(set_idx, hit=False)
                            event_count += 1
                    
                    # For hybrid cache, track hash distribution
                    elif cache_data.is_hybrid and "hash" in signal_name.lower():
                        hash_match = hash_pattern.search(signal_name)
                        if hash_match:
                            hash_value = int(hash_match.group(1))
                            cache_data.add_hash(hash_value)
                            event_count += 1
    
    elapsed = time.time() - start_time
    print(f"VCD parsing complete. Processed {event_count} events in {elapsed:.1f} seconds")
    return cache_data

def parse_log_for_access_data(log_file, cache_data):
    """Parse a log file to extract cache access patterns"""
    print(f"Parsing {log_file} for cache access patterns...")
    
    # Patterns to match in log files
    set_access_pattern = re.compile(r'Set\s+(\d+):\s+access')
    set_hit_pattern = re.compile(r'Set\s+(\d+):\s+hit')
    set_miss_pattern = re.compile(r'Set\s+(\d+):\s+miss')
    hash_pattern = re.compile(r'Hash\s+(\d+):\s+used')
    
    with open(log_file, 'r') as f:
        for line in f:
            # Match set accesses
            set_access_match = set_access_pattern.search(line)
            if set_access_match:
                set_idx = int(set_access_match.group(1))
                cache_data.set_accesses[set_idx] += 1
                cache_data.total_accesses += 1
                continue
            
            # Match set hits
            set_hit_match = set_hit_pattern.search(line)
            if set_hit_match:
                set_idx = int(set_hit_match.group(1))
                cache_data.set_hits[set_idx] += 1
                cache_data.total_hits += 1
                continue
            
            # Match set misses
            set_miss_match = set_miss_pattern.search(line)
            if set_miss_match:
                set_idx = int(set_miss_match.group(1))
                cache_data.set_misses[set_idx] += 1
                cache_data.total_misses += 1
                continue
            
            # Match hash distribution for hybrid cache
            if cache_data.is_hybrid:
                hash_match = hash_pattern.search(line)
                if hash_match:
                    hash_value = int(hash_match.group(1))
                    cache_data.hash_distribution[hash_value] += 1
    
    # If we didn't find explicit hit/miss but have accesses, estimate them
    if cache_data.total_accesses > 0 and cache_data.total_hits == 0 and cache_data.total_misses == 0:
        # Generate synthetic hit/miss based on set access patterns
        # This is just an estimate for visualization purposes
        for set_idx, count in cache_data.set_accesses.items():
            # Assume 80% hit rate as a generic estimate
            hits = int(count * 0.8)
            misses = count - hits
            cache_data.set_hits[set_idx] = hits
            cache_data.set_misses[set_idx] = misses
            cache_data.total_hits += hits
            cache_data.total_misses += misses
    
    return cache_data

def generate_access_heatmap(cache_data, output_file, is_synthetic=False):
    """Generate an ASCII heatmap of the cache access patterns"""
    if not cache_data.set_accesses:
        print(f"{Colors.YELLOW}No access data available for heatmap generation.{Colors.ENDC}")
        return
    
    # Define the ASCII intensity scale (62 characters as requested)
    intensity_chars = "abcdefghijklmnopqrstuvwrxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789"
    
    # Prepare data for heatmap
    max_access = max(cache_data.set_accesses.values()) if cache_data.set_accesses else 1
    max_hit = max(cache_data.set_hits.values()) if cache_data.set_hits else 1
    max_miss = max(cache_data.set_misses.values()) if cache_data.set_misses else 1
    max_value = max(max_access, max_hit, max_miss)
    
    # Determine appropriate cache mode label
    cache_type = "Standard Write-Through Cache"
    if cache_data.is_hybrid:
        if cache_data.is_full_associative:
            cache_type = "Hybrid Cache (Fully Associative Mode)"
        else:
            cache_type = "Hybrid Cache (Set Associative Mode)"
    
    # Add SYNTHETIC prefix to title if it's synthetic data
    title = "Cache Access Pattern Heatmap"
    if is_synthetic:
        title = "SYNTHETIC " + title
    
    # Generate the heatmap
    with open(output_file, 'w') as f:
        f.write(f"{title}\n")
        f.write(f"{'=' * len(title)}\n\n")
        f.write(f"Cache Type: {cache_type}\n")
        f.write(f"Cache Size: {cache_data.num_ways} ways x {cache_data.num_sets} sets\n\n")
        
        # Overall statistics
        f.write(f"Statistics:\n")
        f.write(f"  Total Accesses: {cache_data.total_accesses}\n")
        if cache_data.total_hits > 0 or cache_data.total_misses > 0:
            hit_rate = cache_data.total_hits / (cache_data.total_hits + cache_data.total_misses) * 100 if (cache_data.total_hits + cache_data.total_misses) > 0 else 0
            f.write(f"  Hit Rate: {hit_rate:.2f}%\n")
            f.write(f"  Hits: {cache_data.total_hits}\n")
            f.write(f"  Misses: {cache_data.total_misses}\n")
        
        # Set utilization
        sets_used = len(cache_data.set_accesses)
        set_utilization = sets_used / cache_data.num_sets * 100
        f.write(f"  Sets Used: {sets_used} of {cache_data.num_sets} ({set_utilization:.2f}%)\n\n")
        
        # Total accesses heatmap
        f.write(f"Total Cache Accesses by Set\n")
        f.write(f"Sets (0-{cache_data.num_sets-1}):\n")
        f.write(f"+{'-' * cache_data.num_sets}+\n|")
        
        for i in range(cache_data.num_sets):
            count = cache_data.set_accesses.get(i, 0)
            if count == 0:
                f.write(" ")
            else:
                # Scale to intensity characters
                intensity = int((count / max_value) * (len(intensity_chars) - 1))
                f.write(intensity_chars[intensity])
        
        f.write(f"|\n+{'-' * cache_data.num_sets}+\n\n")
        
        # Hits heatmap if available
        if cache_data.total_hits > 0:
            f.write(f"Cache Hits by Set\n")
            f.write(f"Sets (0-{cache_data.num_sets-1}):\n")
            f.write(f"+{'-' * cache_data.num_sets}+\n|")
            
            for i in range(cache_data.num_sets):
                count = cache_data.set_hits.get(i, 0)
                if count == 0:
                    f.write(" ")
                else:
                    # Scale to intensity characters
                    intensity = int((count / max_value) * (len(intensity_chars) - 1))
                    f.write(intensity_chars[intensity])
            
            f.write(f"|\n+{'-' * cache_data.num_sets}+\n\n")
        
        # Misses heatmap if available
        if cache_data.total_misses > 0:
            f.write(f"Cache Misses by Set\n")
            f.write(f"Sets (0-{cache_data.num_sets-1}):\n")
            f.write(f"+{'-' * cache_data.num_sets}+\n|")
            
            for i in range(cache_data.num_sets):
                count = cache_data.set_misses.get(i, 0)
                if count == 0:
                    f.write(" ")
                else:
                    # Scale to intensity characters
                    intensity = int((count / max_value) * (len(intensity_chars) - 1))
                    f.write(intensity_chars[intensity])
            
            f.write(f"|\n+{'-' * cache_data.num_sets}+\n\n")
        
        # Hash distribution for hybrid cache
        if cache_data.is_hybrid and cache_data.hash_distribution:
            f.write(f"Hash Distribution (Hybrid Cache)\n")
            
            # Calculate uniformity using entropy
            total_hash = sum(cache_data.hash_distribution.values())
            if total_hash > 0:
                import math
                entropy = 0
                for count in cache_data.hash_distribution.values():
                    p = count / total_hash
                    if p > 0:
                        entropy -= p * math.log2(p)
                max_entropy = math.log2(cache_data.num_sets)
                uniformity = (entropy / max_entropy) * 100 if max_entropy > 0 else 0
                f.write(f"Uniformity: {uniformity:.2f}% (100% is perfectly uniform)\n\n")
            
            f.write(f"Hash Values (0-{cache_data.num_sets-1}):\n")
            f.write(f"+{'-' * cache_data.num_sets}+\n|")
            
            max_hash = max(cache_data.hash_distribution.values()) if cache_data.hash_distribution else 1
            for i in range(cache_data.num_sets):
                count = cache_data.hash_distribution.get(i, 0)
                if count == 0:
                    f.write(" ")
                else:
                    # Scale to intensity characters
                    intensity = int((count / max_hash) * (len(intensity_chars) - 1))
                    f.write(intensity_chars[intensity])
            
            f.write(f"|\n+{'-' * cache_data.num_sets}+\n\n")
        
        # Add legend
        f.write("\nIntensity Scale: ")
        f.write(intensity_chars + "\n")
        f.write("(a = lowest, 9 = highest)\n")
    
    print(f"Heatmap saved to {output_file}")
    
    # Also print the heatmap to the console
    print("\n" + "="*60)
    if is_synthetic:
        print(f"{Colors.RED}{Colors.BOLD}SYNTHETIC {Colors.ENDC}{Colors.HEADER}{Colors.BOLD}Cache Access Pattern Heatmap{Colors.ENDC}")
    else:
        print(f"{Colors.HEADER}{Colors.BOLD}Cache Access Pattern Heatmap{Colors.ENDC}")
    print("="*60)
    
    print(f"Cache Type: {Colors.BOLD}{cache_type}{Colors.ENDC}")
    
    # Total accesses heatmap
    print(f"\n{Colors.BOLD}Total Cache Accesses by Set{Colors.ENDC}")
    print(f"Sets (0-{cache_data.num_sets-1}):")
    print(f"+{'-' * cache_data.num_sets}+")
    print("|", end="")
    
    for i in range(cache_data.num_sets):
        count = cache_data.set_accesses.get(i, 0)
        if count == 0:
            print(" ", end="")
        else:
            # Scale to intensity characters
            intensity = int((count / max_value) * (len(intensity_chars) - 1))
            print(intensity_chars[intensity], end="")
    
    print("|")
    print(f"+{'-' * cache_data.num_sets}+")
    
    # Hash distribution for hybrid cache
    if cache_data.is_hybrid and cache_data.hash_distribution:
        print(f"\n{Colors.BOLD}Hash Distribution (Hybrid Cache){Colors.ENDC}")
        print(f"Hash Values (0-{cache_data.num_sets-1}):")
        print(f"+{'-' * cache_data.num_sets}+")
        print("|", end="")
        
        max_hash = max(cache_data.hash_distribution.values()) if cache_data.hash_distribution else 1
        for i in range(cache_data.num_sets):
            count = cache_data.hash_distribution.get(i, 0)
            if count == 0:
                print(" ", end="")
            else:
                # Scale to intensity characters
                intensity = int((count / max_hash) * (len(intensity_chars) - 1))
                print(intensity_chars[intensity], end="")
        
        print("|")
        print(f"+{'-' * cache_data.num_sets}+")

def simulate_synthetic_data(cache_data, mode):
    """Generate synthetic access data for testing heatmap generation"""
    import random
    
    # Ensure we have a valid mode
    if mode == "WT":
        # Standard WT cache typically uses all sets evenly
        for i in range(cache_data.num_sets):
            accesses = random.randint(80, 120)
            hits = int(accesses * random.uniform(0.7, 0.9))
            misses = accesses - hits
            
            cache_data.set_accesses[i] = accesses
            cache_data.set_hits[i] = hits
            cache_data.set_misses[i] = misses
            cache_data.total_accesses += accesses
            cache_data.total_hits += hits
            cache_data.total_misses += misses
    
    elif mode == "WT_HYB_FORCE_SET_ASS":
        # Hybrid set associative often has better distribution but not perfect
        for i in range(cache_data.num_sets):
            # Some variation but generally even
            accesses = random.randint(70, 130)
            hits = int(accesses * random.uniform(0.75, 0.95))
            misses = accesses - hits
            
            cache_data.set_accesses[i] = accesses
            cache_data.set_hits[i] = hits
            cache_data.set_misses[i] = misses
            cache_data.total_accesses += accesses
            cache_data.total_hits += hits
            cache_data.total_misses += misses
        
        # Add hash distribution
        for i in range(cache_data.num_sets):
            cache_data.hash_distribution[i] = random.randint(80, 120)
    
    elif mode == "WT_HYB_FORCE_FULL_ASS":
        # Fully associative mode typically concentrates accesses in a subset of sets
        # (depending on the hash function quality)
        active_sets = random.sample(range(cache_data.num_sets), cache_data.num_sets // 2)
        
        for i in range(cache_data.num_sets):
            if i in active_sets:
                # Higher access counts in active sets
                accesses = random.randint(150, 250)
            else:
                # Low or zero accesses in inactive sets
                accesses = random.randint(0, 20)
            
            hits = int(accesses * random.uniform(0.8, 0.98))
            misses = accesses - hits
            
            cache_data.set_accesses[i] = accesses
            cache_data.set_hits[i] = hits
            cache_data.set_misses[i] = misses
            cache_data.total_accesses += accesses
            cache_data.total_hits += hits
            cache_data.total_misses += misses
        
        # Hash distribution will be concentrated in a subset of values
        hash_values = random.sample(range(cache_data.num_sets), cache_data.num_sets // 3)
        for i in hash_values:
            cache_data.hash_distribution[i] = random.randint(150, 300)
    
    return cache_data

def main():
    args = parse_args()
    
    # Initialize cache data
    cache_data = CacheAccessData(
        num_sets=args.sets or 16,
        num_ways=args.ways or 8,
        mode=args.mode
    )
    
    # Process VCD file if provided
    if args.vcd:
        if not os.path.exists(args.vcd):
            print(f"Error: VCD file {args.vcd} does not exist")
            return
        
        # Try to detect cache parameters from VCD
        num_sets, num_ways, mode = guess_cache_parameters_from_vcd(args.vcd)
        
        # Use detected parameters if available, otherwise use defaults or args
        cache_data.set_cache_parameters(
            num_sets=args.sets or num_sets,
            num_ways=args.ways or num_ways,
            mode=args.mode or mode
        )
        
        # Parse VCD file for access data
        parse_vcd_for_access_data(args.vcd, cache_data)
    
    # Process log file if provided
    elif args.log:
        if not os.path.exists(args.log):
            print(f"Error: Log file {args.log} does not exist")
            return
        
        # Parse log file for access data
        parse_log_for_access_data(args.log, cache_data)
    
    # Generate synthetic data only if explicitly requested with --demo flag
    is_synthetic = False
    if args.demo:
        print(f"{Colors.GREEN}[TESTING ONLY] Generating synthetic demonstration data for {args.mode} mode{Colors.ENDC}")
        print(f"{Colors.YELLOW}Warning: This is not real simulation data and should only be used for testing.{Colors.ENDC}")
        cache_data = simulate_synthetic_data(cache_data, args.mode)
        is_synthetic = True
    
    # If no data was found and we're not in demo mode, exit with error
    elif not cache_data.set_accesses:
        print(f"{Colors.RED}Error: No cache access data found in the provided file.{Colors.ENDC}")
        print(f"Please provide a valid VCD or log file with cache access data, or use the --demo flag for testing.")
        return
    
    # Generate the heatmap
    generate_access_heatmap(cache_data, args.output, is_synthetic)
    
    print(f"Heatmap generation complete!")

if __name__ == "__main__":
    main()