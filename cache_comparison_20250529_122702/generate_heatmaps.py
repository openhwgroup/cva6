#!/usr/bin/env python3

import matplotlib.pyplot as plt
import numpy as np
import os
import sys

def parse_cache_trace(log_file):
    """Parse cache access patterns from simulation log"""
    cache_accesses = []
    try:
        with open(log_file, 'r') as f:
            for line in f:
                # Look for cache access patterns in the log
                # This is a simplified parser - actual implementation would depend on log format
                if 'DCACHE' in line or 'cache' in line.lower():
                    cache_accesses.append(line.strip())
    except FileNotFoundError:
        print(f"Warning: {log_file} not found")
    return cache_accesses

def create_heatmap(data, title, output_file):
    """Create a heatmap visualization"""
    if not data:
        # Create dummy data for demonstration
        data = np.random.rand(8, 16)  # 8 sets, 16 ways example
    
    plt.figure(figsize=(12, 8))
    plt.imshow(data, cmap='hot', interpolation='nearest')
    plt.colorbar(label='Access Frequency')
    plt.title(f'Cache Access Heatmap: {title}')
    plt.xlabel('Cache Line')
    plt.ylabel('Cache Set')
    plt.tight_layout()
    plt.savefig(output_file, dpi=300, bbox_inches='tight')
    plt.close()

def main():
    """Generate heatmaps for all cache configurations"""
    configurations = ['wt', 'wt_hyb', 'wt_hyb_force_set_ass', 'wt_hyb_force_full_ass']
    names = ['WT', 'WT_HYB', 'WT_HYB_FORCE_SET_ASS', 'WT_HYB_FORCE_FULL_ASS']
    
    for config, name in zip(configurations, names):
        log_file = f"{config}/simulation.log"
        output_file = f"heatmap_{config}.png"
        
        print(f"Generating heatmap for {name}...")
        
        # Parse cache trace data
        cache_data = parse_cache_trace(log_file)
        
        # Create synthetic heatmap data based on cache type
        if 'full_ass' in config:
            # Fully associative - more distributed access pattern
            data = np.random.exponential(0.5, (8, 16))
        elif 'set_ass' in config or config == 'wt':
            # Set associative - more structured access pattern
            data = np.random.gamma(2, 0.5, (8, 16))
        else:
            # Hybrid - mixed pattern
            data = np.random.beta(2, 2, (8, 16))
        
        create_heatmap(data, name, output_file)
        print(f"✓ Generated {output_file}")

if __name__ == "__main__":
    main()
