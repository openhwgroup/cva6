#!/usr/bin/env python3
"""
Script to analyze hybrid cache performance and compare configurations.
This script parses simulation logs to extract cache performance metrics
and generates visualizations and reports.
"""

import os
import sys
import re
import glob
import argparse
import pandas as pd
import numpy as np
import matplotlib.pyplot as plt
from pathlib import Path

def parse_cache_stats(log_file):
    """Parse cache statistics from simulation log file"""
    stats = {
        'hits': 0,
        'misses': 0,
        'hit_ratio': 0.0,
        'mode_switches': 0,
        'set_assoc_hits': 0,
        'full_assoc_hits': 0,
        'cycles': 0,
        'set_assoc_time': 0,
        'full_assoc_time': 0
    }
    
    if not os.path.exists(log_file):
        print(f"Warning: Log file {log_file} not found")
        return stats
    
    with open(log_file, 'r') as f:
        content = f.read()
        
        # Extract cycle count
        match = re.search(r'Finished after (\d+) cycles', content)
        if match:
            stats['cycles'] = int(match.group(1))
        
        # Extract cache hits and misses
        hit_match = re.search(r'Cache hits: (\d+)', content)
        miss_match = re.search(r'Cache misses: (\d+)', content)
        
        if hit_match and miss_match:
            stats['hits'] = int(hit_match.group(1))
            stats['misses'] = int(miss_match.group(1))
            total = stats['hits'] + stats['misses']
            if total > 0:
                stats['hit_ratio'] = stats['hits'] / total * 100
        
        # For hybrid cache, extract mode-specific hits
        set_match = re.search(r'Set associative hits: (\d+)', content)
        full_match = re.search(r'Fully associative hits: (\d+)', content)
        
        if set_match:
            stats['set_assoc_hits'] = int(set_match.group(1))
        
        if full_match:
            stats['full_assoc_hits'] = int(full_match.group(1))
        
        # Extract mode switch count
        switch_match = re.search(r'Mode switches: (\d+)', content)
        if switch_match:
            stats['mode_switches'] = int(switch_match.group(1))
        
        # Extract time spent in each mode
        set_time_match = re.search(r'Time in set associative mode: (\d+) cycles', content)
        full_time_match = re.search(r'Time in fully associative mode: (\d+) cycles', content)
        
        if set_time_match:
            stats['set_assoc_time'] = int(set_time_match.group(1))
        
        if full_time_match:
            stats['full_assoc_time'] = int(full_time_match.group(1))
    
    return stats

def generate_comparison_chart(results, test_name, output_dir):
    """Generate comparison charts for cache configurations"""
    configs = list(results.keys())
    metrics = ['hit_ratio', 'cycles']
    
    # Create directory for charts
    os.makedirs(os.path.join(output_dir, 'charts'), exist_ok=True)
    
    for metric in metrics:
        values = [results[config].get(metric, 0) for config in configs]
        
        plt.figure(figsize=(10, 6))
        bars = plt.bar(configs, values)
        
        # Add values on top of bars
        for bar in bars:
            height = bar.get_height()
            plt.text(bar.get_x() + bar.get_width()/2., height,
                    f'{height:.1f}' if metric == 'hit_ratio' else f'{height}',
                    ha='center', va='bottom')
        
        plt.title(f'{test_name} - {metric.replace("_", " ").title()}')
        plt.ylabel(f'{metric.replace("_", " ").title()}' + (' (%)' if metric == 'hit_ratio' else ' (cycles)'))
        plt.tight_layout()
        
        # Save the chart
        plt.savefig(os.path.join(output_dir, 'charts', f'{test_name}_{metric}.png'))
        plt.close()
    
    # For hybrid cache, generate mode-specific hit chart
    if 'WT_HYB' in configs:
        plt.figure(figsize=(10, 6))
        
        # Extract mode-specific hit data (only for WT_HYB)
        hybrid_data = results.get('WT_HYB', {})
        set_hits = hybrid_data.get('set_assoc_hits', 0)
        full_hits = hybrid_data.get('full_assoc_hits', 0)
        
        labels = ['Set Associative Hits', 'Fully Associative Hits']
        values = [set_hits, full_hits]
        
        plt.pie(values, labels=labels, autopct='%1.1f%%', startangle=90)
        plt.axis('equal')  # Equal aspect ratio ensures that pie is drawn as a circle
        plt.title(f'{test_name} - WT_HYB Hit Distribution')
        
        # Save the chart
        plt.savefig(os.path.join(output_dir, 'charts', f'{test_name}_hybrid_hit_distribution.png'))
        plt.close()

def main():
    parser = argparse.ArgumentParser(description='Analyze hybrid cache performance')
    parser.add_argument('comparison_dir', help='Directory containing comparison results')
    parser.add_argument('--output', '-o', default='cache_analysis_report', help='Output directory for analysis')
    
    args = parser.parse_args()
    
    if not os.path.isdir(args.comparison_dir):
        print(f"Error: {args.comparison_dir} is not a directory")
        sys.exit(1)
    
    os.makedirs(args.output, exist_ok=True)
    
    # Find test results for each configuration
    tests = ['hello_world', 'cache_test', 'cache_thrash']
    configs = ['WT', 'WT_HYB', 'WT_HYB_FORCE_SET_ASS', 'WT_HYB_FORCE_FULL_ASS']
    
    # Collect results
    all_results = {}
    
    for test in tests:
        test_results = {}
        
        for config in configs:
            config_dir = os.path.join(args.comparison_dir, config)
            if not os.path.isdir(config_dir):
                print(f"Warning: Configuration directory {config_dir} not found")
                continue
            
            # Find the log file for this test and configuration
            log_files = glob.glob(f"{config_dir}/simulation_artifacts/out_*/veri-testharness_sim/{test}.cv32a60x.log.*")
            
            if not log_files:
                print(f"Warning: No log files found for {test} with configuration {config}")
                continue
            
            # Use the most recent log file
            log_file = sorted(log_files)[-1]
            
            # Extract cache statistics
            stats = parse_cache_stats(log_file)
            test_results[config] = stats
        
        all_results[test] = test_results
        
        # Generate comparison charts for this test
        if test_results:
            generate_comparison_chart(test_results, test, args.output)
    
    # Generate overall comparison report
    report_md = os.path.join(args.output, 'cache_analysis_report.md')
    
    with open(report_md, 'w') as f:
        f.write("# Hybrid Cache Analysis Report\n\n")
        
        f.write("## Performance Summary\n\n")
        
        for test in tests:
            f.write(f"### {test.replace('_', ' ').title()}\n\n")
            
            # Create table for this test
            f.write("| Configuration | Cycles | Hit Ratio (%) | Hits | Misses |\n")
            f.write("|---------------|--------|--------------|------|--------|\n")
            
            for config in configs:
                if config in all_results.get(test, {}):
                    stats = all_results[test][config]
                    f.write(f"| {config} | {stats.get('cycles', 'N/A')} | {stats.get('hit_ratio', 0):.2f} | "
                            f"{stats.get('hits', 0)} | {stats.get('misses', 0)} |\n")
                else:
                    f.write(f"| {config} | N/A | N/A | N/A | N/A |\n")
            
            f.write("\n")
            
            # Add chart reference
            f.write(f"![{test} Hit Ratio](charts/{test}_hit_ratio.png)\n\n")
            f.write(f"![{test} Cycles](charts/{test}_cycles.png)\n\n")
            
            # Add hybrid mode analysis if available
            if 'WT_HYB' in all_results.get(test, {}):
                hybrid_stats = all_results[test]['WT_HYB']
                
                if hybrid_stats.get('mode_switches', 0) > 0:
                    f.write("#### Hybrid Mode Analysis\n\n")
                    f.write(f"- Mode Switches: {hybrid_stats.get('mode_switches', 0)}\n")
                    f.write(f"- Set Associative Hits: {hybrid_stats.get('set_assoc_hits', 0)}\n")
                    f.write(f"- Fully Associative Hits: {hybrid_stats.get('full_assoc_hits', 0)}\n")
                    f.write(f"- Time in Set Associative Mode: {hybrid_stats.get('set_assoc_time', 0)} cycles\n")
                    f.write(f"- Time in Fully Associative Mode: {hybrid_stats.get('full_assoc_time', 0)} cycles\n\n")
                    
                    f.write(f"![{test} Hybrid Hit Distribution](charts/{test}_hybrid_hit_distribution.png)\n\n")
            
            f.write("---\n\n")
        
        f.write("## Findings and Conclusions\n\n")
        f.write("### Performance Comparison\n\n")
        f.write("The hybrid cache shows the following performance characteristics compared to standard WT cache:\n\n")
        f.write("- (Analyze and fill in based on actual results)\n\n")
        
        f.write("### Isolation Effectiveness\n\n")
        f.write("The hybrid cache's ability to isolate privilege levels shows:\n\n")
        f.write("- (Analyze and fill in based on actual results)\n\n")
        
        f.write("### Mode Switching Overhead\n\n")
        f.write("- (Analyze and fill in based on actual results)\n\n")
        
        f.write("### Recommendations\n\n")
        f.write("Based on this analysis, the recommended configuration for different scenarios is:\n\n")
        f.write("- Performance-critical systems: (Recommendation)\n")
        f.write("- Security-critical systems: (Recommendation)\n")
        f.write("- Balanced systems: (Recommendation)\n\n")
    
    print(f"Analysis report generated in {args.output}")

if __name__ == "__main__":
    main()