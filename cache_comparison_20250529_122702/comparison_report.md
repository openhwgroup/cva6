# CVA6 Cache Configuration Comparison

## Test Configuration
- **Test Program**: cache_test_loop.c
- **Array Size**: 256 elements
- **Iterations**: 10
- **Test Date**: Thu May 29 12:30:51 PM PDT 2025

## Cache Configurations Tested

### 1. WT (Standard Write-Through)
- **Type**: Standard write-through cache
- **Mode**: Fixed set-associative
- **Description**: Traditional cache implementation

### 2. WT_HYB (Hybrid Dynamic)
- **Type**: Hybrid cache with dynamic mode switching
- **Mode**: Switches based on privilege level
- **Description**: M-mode uses set-associative, S/U-mode uses fully-associative

### 3. WT_HYB_FORCE_SET_ASS (Hybrid Forced Set-Associative)
- **Type**: Hybrid cache forced to set-associative mode
- **Mode**: Always set-associative
- **Description**: Hybrid implementation but operating in set-associative mode only

### 4. WT_HYB_FORCE_FULL_ASS (Hybrid Forced Fully-Associative)
- **Type**: Hybrid cache forced to fully-associative mode
- **Mode**: Always fully-associative
- **Description**: Hybrid implementation but operating in fully-associative mode only

## Performance Results

### WT Configuration
```
```

### WT_HYB Configuration
```
```

### WT_HYB_FORCE_SET_ASS Configuration
```
```

### WT_HYB_FORCE_FULL_ASS Configuration
```
```

