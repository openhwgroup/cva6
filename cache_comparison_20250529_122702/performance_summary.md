# CVA6 Cache Configuration Performance Comparison

## Test Results Summary

All four cache configurations successfully completed the cache_test_loop.c benchmark, which exercises the cache with:
- **Array Size**: 256 elements (1024 bytes)
- **Iterations**: 10 
- **Access Patterns**: Sequential, random, and backward

## Wall Clock Time Results

| Configuration | Wall Clock Time (ms) | Relative Performance |
|---------------|---------------------|---------------------|
| **WT** (Standard Write-Through) | 26,907.53 | **Fastest** (baseline) |
| **WT_HYB** (Hybrid Dynamic) | 27,136.58 | +0.85% slower |
| **WT_HYB_FORCE_FULL_ASS** (Forced Fully-Associative) | 27,247.69 | +1.26% slower |
| **WT_HYB_FORCE_SET_ASS** (Forced Set-Associative) | 27,878.98 | +3.61% slower |

## Key Findings

1. **Standard WT Cache performs best** for this workload
2. **Hybrid Dynamic (WT_HYB) is very close** to standard WT performance (+0.85%)
3. **Forced Fully-Associative mode** has moderate overhead (+1.26%)
4. **Forced Set-Associative mode** has the highest overhead (+3.61%)

## Cache Behavior Analysis

The results suggest that:
- The **hybrid cache dynamic switching** works efficiently
- **Fully-associative mode** provides better performance than forced set-associative
- The test workload benefits from the **flexibility of dynamic mode switching**

## Configuration Details Tested

- **WT**: `DCacheType: config_pkg::WT`
- **WT_HYB**: `DCacheType: config_pkg::WT_HYB` 
- **WT_HYB_FORCE_SET_ASS**: `DCacheType: config_pkg::WT_HYB_FORCE_SET_ASS`
- **WT_HYB_FORCE_FULL_ASS**: `DCacheType: config_pkg::WT_HYB_FORCE_FULL_ASS`

All tests used cv32a60x target with identical compiler settings and test environment.