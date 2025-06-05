#!/usr/bin/env python3
"""
WT_NEW Cache Performance Monitor
Analyzes cache behavior and privilege-level switching patterns
"""

import sys
import re
import argparse
from typing import Dict, List, Tuple

class WTNewCacheMonitor:
    def __init__(self):
        self.machine_mode_accesses = 0
        self.user_mode_accesses = 0
        self.privilege_switches = 0
        self.cache_hits = 0
        self.cache_misses = 0
        self.dual_controller_usage = {"A": 0, "B": 0}
        
    def analyze_trace_line(self, line: str) -> None:
        """Analyze a single trace line for cache behavior patterns"""
        
        # Look for privilege level indicators
        if "PRIV_LVL_M" in line or "priv_lvl=11" in line:
            self.machine_mode_accesses += 1
            self.dual_controller_usage["A"] += 1
        elif "PRIV_LVL_U" in line or "priv_lvl=00" in line:
            self.user_mode_accesses += 1
            self.dual_controller_usage["B"] += 1
            
        # Look for privilege switches
        if "switch_ctrl" in line or "privilege_switch" in line:
            self.privilege_switches += 1
            
        # Look for cache hit/miss patterns
        if "cache_hit" in line or "hit_o=1" in line:
            self.cache_hits += 1
        elif "cache_miss" in line or "hit_o=0" in line:
            self.cache_misses += 1
            
    def analyze_file(self, filename: str) -> None:
        """Analyze an entire trace file"""
        try:
            with open(filename, 'r') as f:
                for line_num, line in enumerate(f, 1):
                    self.analyze_trace_line(line)
                    if line_num % 10000 == 0:
                        print(f"Processed {line_num} lines...", file=sys.stderr)
        except FileNotFoundError:
            print(f"Error: File {filename} not found")
            return False
        except Exception as e:
            print(f"Error analyzing file: {e}")
            return False
        return True
            
    def generate_report(self) -> str:
        """Generate a comprehensive performance report"""
        total_accesses = self.machine_mode_accesses + self.user_mode_accesses
        total_cache_ops = self.cache_hits + self.cache_misses
        
        report = []
        report.append("=== WT_NEW Cache Performance Report ===")
        report.append("")
        
        # Privilege level distribution
        report.append("Privilege Level Access Distribution:")
        if total_accesses > 0:
            machine_pct = (self.machine_mode_accesses * 100) // total_accesses
            user_pct = (self.user_mode_accesses * 100) // total_accesses
            report.append(f"  Machine Mode: {self.machine_mode_accesses} ({machine_pct}%)")
            report.append(f"  User Mode:    {self.user_mode_accesses} ({user_pct}%)")
        else:
            report.append("  No privilege level data found")
        report.append("")
        
        # Dual controller usage
        report.append("Dual Controller Usage:")
        total_controller = self.dual_controller_usage["A"] + self.dual_controller_usage["B"]
        if total_controller > 0:
            a_pct = (self.dual_controller_usage["A"] * 100) // total_controller
            b_pct = (self.dual_controller_usage["B"] * 100) // total_controller
            report.append(f"  Controller A (Set-Associative): {self.dual_controller_usage['A']} ({a_pct}%)")
            report.append(f"  Controller B (Fully-Associative): {self.dual_controller_usage['B']} ({b_pct}%)")
        else:
            report.append("  No controller usage data found")
        report.append("")
        
        # Cache performance
        report.append("Cache Performance:")
        if total_cache_ops > 0:
            hit_rate = (self.cache_hits * 100) // total_cache_ops
            miss_rate = (self.cache_misses * 100) // total_cache_ops
            report.append(f"  Cache Hits:   {self.cache_hits} ({hit_rate}%)")
            report.append(f"  Cache Misses: {self.cache_misses} ({miss_rate}%)")
            report.append(f"  Hit Rate:     {hit_rate}%")
        else:
            report.append("  No cache performance data found")
        report.append("")
        
        # Privilege switching
        report.append("Privilege Level Switching:")
        report.append(f"  Total Switches: {self.privilege_switches}")
        if total_accesses > 0:
            switch_freq = (self.privilege_switches * 1000) // total_accesses
            report.append(f"  Switch Frequency: {switch_freq/10:.1f}% of accesses")
        report.append("")
        
        # Analysis and recommendations
        report.append("Analysis:")
        if self.dual_controller_usage["A"] > 0 and self.dual_controller_usage["B"] > 0:
            report.append("  ✓ Both controllers are being utilized")
        elif self.dual_controller_usage["A"] > 0:
            report.append("  ⚠ Only Controller A (machine mode) is active")
        elif self.dual_controller_usage["B"] > 0:
            report.append("  ⚠ Only Controller B (user mode) is active")
        else:
            report.append("  ❌ No controller activity detected")
            
        if self.privilege_switches > 0:
            report.append("  ✓ Privilege level switching is working")
        else:
            report.append("  ⚠ No privilege switches detected")
            
        if total_cache_ops > 0:
            report.append("  ✓ Cache operations are being performed")
        else:
            report.append("  ❌ No cache operations detected")
        
        return "\n".join(report)

def main():
    parser = argparse.ArgumentParser(description="WT_NEW Cache Performance Monitor")
    parser.add_argument("trace_file", help="Trace file to analyze")
    parser.add_argument("-o", "--output", help="Output report file")
    parser.add_argument("-v", "--verbose", action="store_true", help="Verbose output")
    
    args = parser.parse_args()
    
    monitor = WTNewCacheMonitor()
    
    if args.verbose:
        print(f"Analyzing trace file: {args.trace_file}")
    
    success = monitor.analyze_file(args.trace_file)
    if not success:
        sys.exit(1)
        
    report = monitor.generate_report()
    
    if args.output:
        with open(args.output, 'w') as f:
            f.write(report)
        print(f"Report written to {args.output}")
    else:
        print(report)

if __name__ == "__main__":
    main()