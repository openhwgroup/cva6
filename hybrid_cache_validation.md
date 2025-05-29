# Hybrid Cache Implementation for CVA6

This document describes the hybrid cache implementation that switches between set associative and fully associative organizations based on privilege level.

## Overview

The hybrid cache implementation enhances security by dynamically changing the cache organization based on the processor's privilege level:

- **Machine Mode (M-mode)**: Uses set associative organization for best performance in critical code
- **Supervisor/User Mode (S/U-mode)**: Uses fully associative organization for better isolation

This dynamic switching provides isolation between different privilege levels, potentially mitigating certain cache-based side-channel attacks while maintaining high performance when executing trusted code.

## Cache Modes

Three cache modes are supported:
1. `WT_HYB`: Dynamic switching between set and fully associative modes based on privilege level
2. `WT_HYB_FORCE_SET_ASS`: Force set associative mode regardless of privilege level
3. `WT_HYB_FORCE_FULL_ASS`: Force fully associative mode regardless of privilege level

## Replacement Policies

Two replacement policies are supported during mode transitions:
- `REPL_POLICY_RETAIN`: Only flush the sets used in fully associative mode, preserving other entries
- `REPL_POLICY_FLUSH`: Completely flush the cache during any mode transition

### Replacement Algorithms

The victim way selection strategy can also be configured:

- `REPL_ALGO_RR`: Round-robin pointer, evenly distributing replacements across ways
- `REPL_ALGO_RANDOM`: Pseudo-random victim selection using a small LFSR
- `REPL_ALGO_PLRU`: Tree-based pseudo-LRU replacement
- `HASH_SEED` parameter: seed value used by the fully associative hash function to randomize lookup indices

## Implementation Files

### Primary Components

1. **wt_hybrid_cache_pkg.sv**
   - Package with hybrid cache types, parameters, and utility functions
   - Defines force modes, replacement policies, and cache modes

2. **wt_hybche.sv**
   - Main hybrid cache module implementation
   - Manages privilege level switching and cache mode selection
   - Coordinates cache operation based on current mode

3. **wt_hybche_mem.sv**
   - Memory arrays and tag comparison for hybrid cache
   - Implements different indexing schemes for different modes
   - Manages cache way allocation and invalidation

### Supporting Components

- **wt_hybche_ctrl.sv**: Cache controller for hybrid cache
- **wt_hybche_missunit.sv**: Miss handling unit for hybrid cache
- **wt_hybche_wbuffer.sv**: Write buffer for hybrid cache
- **wt_axi_hybche_adapter.sv**: AXI adapter for hybrid cache
- **wt_axi_hybche_adapter2.sv**: Alternative AXI adapter implementation

## Cache Organizations

### Set Associative Mode

- Traditional set associative organization
- Cache lines are mapped to specific sets based on address bits
- Multiple ways per set enable limited associativity
- Provides good performance through spatial locality
- Used in Machine Mode for maximum performance

### Fully Associative Mode

- Any cache line can be stored in any cache entry
- Requires content-addressable memory (CAM) for tag comparison
- Potentially slower but eliminates set conflicts
- Provides better isolation between different memory access patterns
- Used in Supervisor/User Mode for security isolation

## Configuration

To use the hybrid cache, set the `DCacheType` parameter in the configuration package to one of the hybrid cache modes:

```systemverilog
DCacheType: config_pkg::WT_HYB,  // Dynamic switching
// OR
DCacheType: config_pkg::WT_HYB_FORCE_SET_ASS,  // Force set associative
// OR
DCacheType: config_pkg::WT_HYB_FORCE_FULL_ASS,  // Force fully associative
```

## Testing

The hybrid cache implementation has been validated with:
1. Standard hello world tests
2. Cache thrashing tests
3. Privilege switching tests
4. VM/PMP tests

The `compare_hybrid_cache_configs.sh` script automates running these tests across all configurations.

## Performance Metrics

The hybrid cache tracks several performance metrics to evaluate its effectiveness:

1. **Hit Rate**: Overall cache hit rate
2. **Mode-specific Hit Rates**: Hit rates in set associative and fully associative modes
3. **Mode Transition Count**: Number of switches between cache organizations
4. **Cycle Count**: Impact on overall execution time
5. **Isolation Effectiveness**: Resistance to cache-based side-channel attacks

The `analyze_hybrid_cache.py` script provides detailed analysis of cache performance:
- Parses simulation logs to extract performance metrics
- Generates comparative charts for different configurations
- Creates a comprehensive analysis report

## Security Implications

The hybrid cache design provides security benefits in multi-privilege systems:

1. **Isolation**: Reduces the ability of untrusted code to evict cache lines used by trusted code
2. **Side-channel Mitigation**: Makes certain cache timing attacks more difficult
3. **Performance Preservation**: Maintains high performance for trusted code

## Known Limitations

1. **Mode Transition Overhead**: Switching between modes may incur performance penalties
2. **Partial CAM Implementation**: The fully associative mode uses a hybrid approach that isn't a true CAM
3. **Area and Power**: May require more resources than a standard cache

## Usage Guidelines

To use the hybrid cache in your CVA6 configuration:

1. Set `DCacheType` to one of the hybrid cache options in your configuration package
2. Consider the performance/security tradeoffs for your application
3. For security-critical applications, use the dynamic mode or force fully associative mode
4. For performance-critical applications where all code is trusted, consider forcing set associative mode

Performance and security analysis shows that the hybrid cache provides better isolation in user/supervisor modes while maintaining high performance in machine mode.
