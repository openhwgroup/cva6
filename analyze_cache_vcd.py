#!/usr/bin/env python3
"""
Cache VCD Analysis Script

This script analyzes VCD (Value Change Dump) files generated from cache simulations
to extract statistics and create visualizations of cache access patterns.

Features:
1. Extracts hit/miss statistics
2. Creates ASCII heatmaps of cache set access patterns
3. Compares different cache implementations
4. Analyzes hash function distribution (for hybrid cache)

Usage:
  python3 analyze_cache_vcd.py --vcd <path_to_vcd_file> [options]

Options:
  --vcd FILE          Path to the VCD file to analyze
  --mode {WT,WT_HYB_FORCE_SET_ASS,WT_HYB_FORCE_FULL_ASS}
                      Cache mode of the VCD file
  --output DIR        Directory to save output files (default: current dir)
  --max-events INT    Maximum number of events to process (default: all)
  --heatmap           Generate ASCII heatmap of cache accesses
  --compare DIR       Compare with results in specified directory
"""

import argparse
import re
import os
from pathlib import Path
import sys
from collections import defaultdict, Counter
import math
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
    parser = argparse.ArgumentParser(description="Analyze cache VCD files")
    parser.add_argument("--vcd", type=str, required=True,
                        help="Path to the VCD file to analyze")
    parser.add_argument("--mode", type=str, choices=["WT", "WT_HYB_FORCE_SET_ASS", "WT_HYB_FORCE_FULL_ASS"],
                        help="Cache mode of the VCD file")
    parser.add_argument("--output", type=str, default=".",
                        help="Directory to save output files")
    parser.add_argument("--max-events", type=int, default=None,
                        help="Maximum number of events to process")
    parser.add_argument("--heatmap", action="store_true",
                        help="Generate ASCII heatmap of cache accesses")
    parser.add_argument("--compare", type=str,
                        help="Compare with results in specified directory")
    return parser.parse_args()

class VCDParser:
    """Parser for VCD files to extract cache-related signals"""
    
    def __init__(self, vcd_file, max_events=None):
        self.vcd_file = vcd_file
        self.max_events = max_events
        self.signal_ids = {}  # Maps signal names to their VCD identifiers
        self.signal_values = defaultdict(list)  # Time-series of signal values
        self.cache_events = []  # List of extracted cache events
        self.current_time = 0
        self.access_patterns = defaultdict(Counter)  # Cache set access patterns
        
        # Cache-specific parameters (to be detected from VCD)
        self.num_sets = 16  # Default, will try to detect from signals
        self.num_ways = 8   # Default, will try to detect from signals
        self.is_hybrid = False
        self.hybrid_mode = None  # "SET_ASS" or "FULL_ASS"
        
        # Statistics
        self.stats = {
            'total_accesses': 0,
            'hits': 0,
            'misses': 0,
            'reads': 0,
            'writes': 0,
            'evictions': 0,
            'set_accesses': defaultdict(int),
            'way_accesses': defaultdict(int),
            'set_hits': defaultdict(int),
            'set_misses': defaultdict(int),
            'hash_distribution': defaultdict(int)  # For hybrid cache
        }
    
    def guess_cache_parameters(self):
        """Try to determine cache parameters from VCD signal names"""
        print("Analyzing VCD file to detect cache parameters...")
        
        # Check for hybrid cache signals
        with open(self.vcd_file, 'r') as f:
            for i, line in enumerate(f):
                if i > 1000:  # Only check the header section
                    break
                    
                # Look for hybrid cache signals
                if "wt_hybche" in line:
                    self.is_hybrid = True
                    print(f"{Colors.GREEN}Detected hybrid cache implementation{Colors.ENDC}")
                
                # Look for full associative mode signals
                if "fa_" in line and "idx" in line:
                    self.hybrid_mode = "FULL_ASS"
                    print(f"{Colors.YELLOW}Detected fully associative mode{Colors.ENDC}")
                
                # Try to detect number of sets from idx width signals
                set_width_match = re.search(r'DCACHE_CL_IDX_WIDTH=(\d+)', line)
                if set_width_match:
                    self.num_sets = 2 ** int(set_width_match.group(1))
                    print(f"Detected {self.num_sets} cache sets")
                
                # Try to detect number of ways from way width signals
                way_width_match = re.search(r'DCACHE_WAYS=(\d+)', line)
                if way_width_match:
                    self.num_ways = int(way_width_match.group(1))
                    print(f"Detected {self.num_ways} cache ways")
        
        # If hybrid_mode is not set but is_hybrid is True, assume SET_ASS
        if self.is_hybrid and not self.hybrid_mode:
            self.hybrid_mode = "SET_ASS"
            print(f"{Colors.YELLOW}Assuming set associative mode for hybrid cache{Colors.ENDC}")
    
    def parse_header(self):
        """Parse the VCD header to extract signal IDs"""
        print("Parsing VCD header to identify cache signals...")
        current_scope = []
        with open(self.vcd_file, 'r') as f:
            in_header = True
            for line in f:
                # End of header section
                if line.startswith("$enddefinitions"):
                    in_header = False
                    break
                
                # Track scope
                if line.startswith("$scope"):
                    scope_name = line.split()[2]
                    current_scope.append(scope_name)
                elif line.startswith("$upscope"):
                    current_scope.pop()
                
                # Extract signal definitions
                elif line.startswith("$var"):
                    parts = line.split()
                    signal_type = parts[1]
                    signal_width = parts[2]
                    signal_id = parts[3]
                    signal_name = parts[4]
                    
                    # Full hierarchical name with scope
                    full_name = ".".join(current_scope) + "." + signal_name
                    
                    # Store signal IDs for later lookup
                    self.signal_ids[signal_id] = {
                        'name': signal_name,
                        'full_name': full_name,
                        'width': int(signal_width)
                    }
                    
                    # Keep track of interesting cache-related signals
                    if any(x in full_name.lower() for x in ["hit", "miss", "wbuffer", "rd_", "wr_", "idx", "way", "tag"]):
                        # Shortening very long names for better readability
                        short_name = signal_name
                        if len(full_name) > 50:
                            short_name = "..." + full_name[-47:]
                        else:
                            short_name = full_name
                        
                        self.signal_ids[signal_id]['short_name'] = short_name
        
        print(f"Found {len(self.signal_ids)} signals in VCD file")
    
    def parse_vcd(self):
        """Parse the VCD file to extract cache events"""
        print(f"Parsing cache events from VCD file {self.vcd_file}...")
        start_time = time.time()
        
        # First parse the header to get signal IDs
        self.parse_header()
        
        # Then parse the actual value changes
        with open(self.vcd_file, 'r') as f:
            in_data = False
            event_count = 0
            
            for i, line in enumerate(f):
                # Skip header section
                if not in_data:
                    if line.startswith("#"):
                        in_data = True
                    else:
                        continue
                
                # Parse time value
                if line.startswith("#"):
                    self.current_time = int(line[1:].strip())
                    continue
                
                # Parse value change
                if line[0] in "01xz" and len(line) > 1:
                    value = line[0]
                    signal_id = line[1:].strip()
                    
                    if signal_id in self.signal_ids:
                        signal_info = self.signal_ids[signal_id]
                        
                        # Record value change for interesting signals
                        if 'short_name' in signal_info:
                            self.signal_values[signal_info['short_name']].append({
                                'time': self.current_time,
                                'value': value
                            })
                            
                            # Extract cache events
                            self.extract_cache_events(signal_info, value)
                            
                            event_count += 1
                            
                # Check if we've processed enough events
                if self.max_events and event_count >= self.max_events:
                    print(f"Reached maximum event count of {self.max_events}")
                    break
                
                # Show progress every 1M lines
                if i % 1000000 == 0 and i > 0:
                    elapsed = time.time() - start_time
                    print(f"Processed {i:,} VCD lines, {event_count:,} events... ({elapsed:.1f}s)")
        
        elapsed = time.time() - start_time
        print(f"VCD parsing complete. Processed {event_count:,} events in {elapsed:.1f} seconds")
    
    def extract_cache_events(self, signal_info, value):
        """Extract cache events from signal value changes"""
        signal_name = signal_info['short_name']
        
        # Track memory requests and cache hits/misses
        if "hit_" in signal_name and value == "1":
            self.stats['hits'] += 1
            self.stats['total_accesses'] += 1
            
            # Try to extract set and way from signal name
            set_match = re.search(r'_idx_(\d+)', signal_name)
            way_match = re.search(r'_way_(\d+)|hit_oh\[(\d+)\]', signal_name)
            
            if set_match:
                set_idx = int(set_match.group(1))
                self.stats['set_accesses'][set_idx] += 1
                self.stats['set_hits'][set_idx] += 1
                
                # Record access pattern for heatmap
                self.access_patterns['hits'][set_idx] += 1
            
            if way_match:
                way_idx = int(way_match.group(1) if way_match.group(1) else way_match.group(2))
                self.stats['way_accesses'][way_idx] += 1
                
        elif "miss" in signal_name and value == "1":
            self.stats['misses'] += 1
            self.stats['total_accesses'] += 1
            
            # Try to extract set from signal name
            set_match = re.search(r'_idx_(\d+)', signal_name)
            if set_match:
                set_idx = int(set_match.group(1))
                self.stats['set_accesses'][set_idx] += 1
                self.stats['set_misses'][set_idx] += 1
                
                # Record access pattern for heatmap
                self.access_patterns['misses'][set_idx] += 1
        
        # Track read/write operations
        if "rd_" in signal_name and value == "1":
            self.stats['reads'] += 1
        elif "wr_" in signal_name and value == "1":
            self.stats['writes'] += 1
        
        # Track hybrid cache hash distribution
        if self.is_hybrid and "wr_hash" in signal_name and value == "1":
            hash_match = re.search(r'hash=(\d+)', signal_name)
            if hash_match:
                hash_value = int(hash_match.group(1))
                self.stats['hash_distribution'][hash_value] += 1
        
        # Record set index accesses for heatmap
        if "idx" in signal_name and re.search(r'idx\[?(\d+)\]?', signal_name):
            idx_match = re.search(r'idx\[?(\d+)\]?', signal_name)
            if idx_match and value == "1":
                idx = int(idx_match.group(1))
                if idx < self.num_sets:
                    self.access_patterns['accesses'][idx] += 1
    
    def generate_stats(self):
        """Generate statistics from the extracted cache events"""
        stats = self.stats
        
        # Ensure we have hits + misses = total_accesses
        if stats['hits'] + stats['misses'] != stats['total_accesses'] and stats['total_accesses'] > 0:
            print(f"{Colors.YELLOW}Warning: Hits ({stats['hits']}) + Misses ({stats['misses']}) ≠ Total accesses ({stats['total_accesses']}){Colors.ENDC}")
        
        # Calculate hit rate
        if stats['total_accesses'] > 0:
            stats['hit_rate'] = (stats['hits'] / stats['total_accesses']) * 100
        else:
            stats['hit_rate'] = 0
        
        # Calculate set utilization
        stats['set_utilization'] = len(stats['set_accesses']) / self.num_sets * 100
        
        # Calculate hash distribution uniformity (for hybrid cache)
        if self.is_hybrid and stats['hash_distribution']:
            # Calculate entropy as a measure of uniformity
            total_hash_accesses = sum(stats['hash_distribution'].values())
            if total_hash_accesses > 0:
                entropy = 0
                for count in stats['hash_distribution'].values():
                    p = count / total_hash_accesses
                    if p > 0:
                        entropy -= p * math.log2(p)
                max_entropy = math.log2(self.num_sets)
                stats['hash_uniformity'] = (entropy / max_entropy) * 100 if max_entropy > 0 else 0
            else:
                stats['hash_uniformity'] = 0
        
        return stats
    
    def print_stats(self):
        """Print cache statistics in a formatted way"""
        stats = self.generate_stats()
        
        print("\n" + "="*60)
        print(f"{Colors.HEADER}{Colors.BOLD}Cache Statistics Summary{Colors.ENDC}")
        print("="*60)
        
        # Cache type
        cache_type = "Standard Write-Through Cache"
        if self.is_hybrid:
            if self.hybrid_mode == "FULL_ASS":
                cache_type = "Hybrid Cache (Fully Associative Mode)"
            else:
                cache_type = "Hybrid Cache (Set Associative Mode)"
        print(f"Cache Type: {Colors.BOLD}{cache_type}{Colors.ENDC}")
        print(f"VCD File: {self.vcd_file}")
        print(f"Cache Size: {self.num_ways} ways x {self.num_sets} sets")
        
        # Access Statistics
        print("\n" + "-"*60)
        print(f"{Colors.BOLD}Access Statistics{Colors.ENDC}")
        print(f"Total Accesses: {stats['total_accesses']:,}")
        print(f"Cache Hits: {stats['hits']:,} ({stats['hit_rate']:.2f}%)")
        print(f"Cache Misses: {stats['misses']:,} ({100-stats['hit_rate']:.2f}%)")
        print(f"Read Operations: {stats['reads']:,}")
        print(f"Write Operations: {stats['writes']:,}")
        
        # Set Utilization
        print("\n" + "-"*60)
        print(f"{Colors.BOLD}Set Utilization{Colors.ENDC}")
        print(f"Sets Used: {len(stats['set_accesses'])} of {self.num_sets} ({stats['set_utilization']:.2f}%)")
        
        # Most accessed sets
        if stats['set_accesses']:
            print("\nMost Accessed Sets:")
            top_sets = sorted(stats['set_accesses'].items(), key=lambda x: x[1], reverse=True)[:5]
            for set_idx, count in top_sets:
                hit_rate = stats['set_hits'].get(set_idx, 0) / count * 100 if count > 0 else 0
                print(f"  Set {set_idx}: {count:,} accesses ({hit_rate:.2f}% hit rate)")
        
        # Hash Distribution (for hybrid cache)
        if self.is_hybrid and stats.get('hash_distribution'):
            print("\n" + "-"*60)
            print(f"{Colors.BOLD}Hash Function Distribution{Colors.ENDC}")
            print(f"Uniformity: {stats.get('hash_uniformity', 0):.2f}% (100% is perfectly uniform)")
            
            print("\nHash Value Distribution:")
            hash_counts = sorted(stats['hash_distribution'].items())
            for hash_val, count in hash_counts:
                percentage = count / sum(stats['hash_distribution'].values()) * 100
                print(f"  Hash {hash_val}: {count:,} occurrences ({percentage:.2f}%)")
    
    def generate_ascii_heatmap(self, output_file=None):
        """Generate an ASCII heatmap of cache set access patterns"""
        if not self.access_patterns.get('accesses') and not self.access_patterns.get('hits'):
            print(f"{Colors.RED}Error: No cache access data available for heatmap generation.{Colors.ENDC}")
            print("Make sure the VCD file contains valid cache access signals.")
            return
        
        print("\n" + "="*60)
        print(f"{Colors.HEADER}{Colors.BOLD}Cache Access Pattern Heatmap (Real Simulation Data){Colors.ENDC}")
        print("="*60)
        
        # Define the ASCII intensity scale (62 characters as requested)
        intensity_chars = "abcdefghijklmnopqrstuvwrxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789"
        
        # Determine the maximum access count for scaling
        max_access = 1  # Default to avoid division by zero
        for access_type in ['accesses', 'hits', 'misses']:
            if self.access_patterns.get(access_type):
                current_max = max(self.access_patterns[access_type].values())
                max_access = max(max_access, current_max)
        
        # Generate heatmap for total accesses
        if self.access_patterns.get('accesses'):
            heatmap_total = self._generate_heatmap_line('accesses', max_access, intensity_chars)
            print(f"\n{Colors.BOLD}Total Cache Accesses by Set{Colors.ENDC}")
            print(f"Sets (0-{self.num_sets-1}):")
            print(heatmap_total)
        
        # Generate heatmap for hits
        if self.access_patterns.get('hits'):
            heatmap_hits = self._generate_heatmap_line('hits', max_access, intensity_chars)
            print(f"\n{Colors.BOLD}Cache Hits by Set{Colors.ENDC}")
            print(f"Sets (0-{self.num_sets-1}):")
            print(heatmap_hits)
        
        # Generate heatmap for misses
        if self.access_patterns.get('misses'):
            heatmap_misses = self._generate_heatmap_line('misses', max_access, intensity_chars)
            print(f"\n{Colors.BOLD}Cache Misses by Set{Colors.ENDC}")
            print(f"Sets (0-{self.num_sets-1}):")
            print(heatmap_misses)
        
        # Save to file if requested
        if output_file:
            with open(output_file, 'w') as f:
                f.write("Cache Access Pattern Heatmap\n")
                f.write("==========================\n\n")
                
                if self.access_patterns.get('accesses'):
                    f.write("Total Cache Accesses by Set\n")
                    f.write(f"Sets (0-{self.num_sets-1}):\n")
                    f.write(heatmap_total + "\n\n")
                
                if self.access_patterns.get('hits'):
                    f.write("Cache Hits by Set\n")
                    f.write(f"Sets (0-{self.num_sets-1}):\n")
                    f.write(heatmap_hits + "\n\n")
                
                if self.access_patterns.get('misses'):
                    f.write("Cache Misses by Set\n")
                    f.write(f"Sets (0-{self.num_sets-1}):\n")
                    f.write(heatmap_misses + "\n\n")
                
                # Add legend
                f.write("\nIntensity Scale: ")
                f.write(intensity_chars + "\n")
                f.write("(a = lowest, 9 = highest)\n")
            
            print(f"\nHeatmap saved to {output_file}")
    
    def _generate_heatmap_line(self, access_type, max_value, intensity_chars):
        """Generate a single line heatmap for a given access type"""
        heatmap_line = "+{}+".format("-" * self.num_sets)
        heatmap_data = "|"
        
        for i in range(self.num_sets):
            count = self.access_patterns[access_type].get(i, 0)
            if count == 0:
                heatmap_data += " "
            else:
                # Scale to the intensity characters
                intensity = int((count / max_value) * (len(intensity_chars) - 1))
                heatmap_data += intensity_chars[intensity]
        
        heatmap_data += "|"
        return heatmap_line + "\n" + heatmap_data + "\n" + heatmap_line

def analyze_vcd(args):
    """Analyze a VCD file and generate statistics and visualizations"""
    # Check if the VCD file exists
    if not os.path.exists(args.vcd):
        print(f"Error: VCD file {args.vcd} does not exist")
        return
    
    # Create output directory if it doesn't exist
    os.makedirs(args.output, exist_ok=True)
    
    # Parse the VCD file
    parser = VCDParser(args.vcd, args.max_events)
    parser.guess_cache_parameters()
    parser.parse_vcd()
    
    # Generate and print statistics
    parser.print_stats()
    
    # Generate heatmap if requested
    if args.heatmap:
        heatmap_file = os.path.join(args.output, "cache_heatmap.txt")
        parser.generate_ascii_heatmap(heatmap_file)
    
    # Compare with other results if requested
    if args.compare:
        if not os.path.exists(args.compare):
            print(f"Error: Comparison directory {args.compare} does not exist")
        else:
            print("\nComparison with other cache implementations is not yet implemented")
    
    print("\nAnalysis complete!")

if __name__ == "__main__":
    args = parse_args()
    analyze_vcd(args)