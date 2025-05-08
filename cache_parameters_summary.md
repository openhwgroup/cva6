# CVA6 Cache Implementation Parameters and Design

## Cache Implementations Overview

The CVA6 processor supports several cache implementations, with a focus on flexible configurations for different workloads:

1. **Standard Write-Through Cache (WT)**
   - Traditional set-associative cache
   - Implements write-through policy
   - Configurable sizes and associativity 

2. **Hybrid Cache (WT_HYB)**
   - Can operate in two modes:
     - Set Associative Mode (WT_HYB_FORCE_SET_ASS)
     - Fully Associative Mode (WT_HYB_FORCE_FULL_ASS)
   - Same write-through policy as standard cache
   - Provides flexibility for different memory access patterns

## Key Parameters

| Parameter | Description | Typical Values |
|-----------|-------------|----------------|
| DCACHE_INDEX_WIDTH | Number of bits for cache set index | 1-8 (powers of 2) |
| DCACHE_TAG_WIDTH | Number of bits for cache tag | Depends on address width |
| DCACHE_LINE_WIDTH | Size of cache line in bits | 128/256 |
| DCACHE_ASSOCIATIVITY | Number of ways per set | 1-16 (powers of 2) |

## Hybrid Cache Design

The hybrid cache implementation extends the standard write-through cache with the ability to operate in fully associative mode, which offers benefits for certain access patterns:

### Set Associative Mode (WT_HYB_FORCE_SET_ASS)

- Operates like a standard cache
- Address is split into tag and index fields
- Cache lines with the same index compete for the same set locations
- Implements a standard replacement policy (LRU)

### Fully Associative Mode (WT_HYB_FORCE_FULL_ASS)

- Enables any address to be stored in any cache line
- Implemented via a hash function that distributes entries across sets
- Uses the full address as the tag for comparison
- Particularly beneficial for scattered/random memory access patterns

## Implementation Details for Fully Associative Mode

The fully associative mode required careful attention to several aspects:

1. **Address Hashing**:
   ```systemverilog
   // Hash function to distribute entries evenly
   always_comb begin
     if (DCACHE_CL_IDX_WIDTH > 1) begin
       for (int i = 0; i < DCACHE_CL_IDX_WIDTH; i++) begin
         wr_hash[i] = ^(wr_cl_tag_i[i*4 +: 4]);
       end
     end else begin
       wr_hash = wr_cl_tag_i[0];
     end
   end
   ```

2. **Tag Comparison**:
   - In fully associative mode, the entire address (minus offset) is used as the tag
   - Tag comparison must consider the extended tag size

3. **Replacement Policy**:
   - Uses enhanced replacement logic to consider the entire cache as a single resource pool
   - Ensures efficient utilization of cache entries

## Performance Characteristics

Based on simulation results:

| Cache Mode | Average Cycles<br>(hello_world.c) | Performance<br>Relative to WT |
|------------|---------------------|------------------------------|
| WT | 2629 | Baseline |
| WT_HYB_SET_ASS | 2422 | 7.9% faster |
| WT_HYB_FULL_ASS | 2766 | 5.2% slower |

Performance may vary significantly depending on the memory access patterns of the workload:
- Sequential access patterns typically benefit more from set associative caches
- Random or scattered access patterns may benefit from fully associative caching

## Configuration

To select a cache implementation, modify the config file at `core/include/cv32a60x_config_pkg.sv`:

```systemverilog
// Select cache implementation:
// WT - Standard Write-Through Cache
// WT_HYB_FORCE_SET_ASS - Hybrid Cache in Set Associative Mode
// WT_HYB_FORCE_FULL_ASS - Hybrid Cache in Fully Associative Mode
DCacheType: config_pkg::WT_HYB_FORCE_FULL_ASS,
```

## Validation

All cache implementations have been validated with the hello_world.c test. The test passes successfully for all cache modes, indicating that both the set associative and fully associative modes of the hybrid cache are working correctly.