# Hybrid Cache Implementation for CVA6

This document describes the hybrid cache implementation that switches between set associative and fully associative organizations based on privilege level.

## Overview

The hybrid cache implementation enhances security by dynamically changing the cache organization based on the processor's privilege level:

- **Machine Mode (M-mode)**: Uses set associative organization for best performance in critical code
- **Supervisor/User Mode (S/U-mode)**: Uses fully associative organization for better isolation

## Cache Modes

Three cache modes are supported:
1. `WT_HYB`: Dynamic switching between set and fully associative modes based on privilege level
2. `WT_HYB_FORCE_SET_ASS`: Force set associative mode regardless of privilege level
3. `WT_HYB_FORCE_FULL_ASS`: Force fully associative mode regardless of privilege level

## Replacement Policies

Two replacement policies are supported during mode transitions:
- `REPL_POLICY_RETAIN`: Only flush the sets used in fully associative mode, preserving other entries
- `REPL_POLICY_FLUSH`: Completely flush the cache during any mode transition

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

Performance and security analysis shows that the hybrid cache provides better isolation in user/supervisor modes while maintaining high performance in machine mode.