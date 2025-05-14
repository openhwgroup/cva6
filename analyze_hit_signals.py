#!/usr/bin/env python3
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
