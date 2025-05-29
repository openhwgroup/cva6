# Hybrid Cache Analysis Tools

This directory documents the analysis utilities used to evaluate the hybrid cache
implementation.

## Overview

The analysis flow is driven by `analyze_hybrid_cache.py` which parses simulation
results, computes cache statistics and generates a markdown report with charts.

## Usage

```bash
python3 analyze_hybrid_cache.py <comparison_dir> --config config/hybrid_cache_analysis.yml -o report
```

- `<comparison_dir>` is the directory produced by the comparison script.
- `--config` specifies a YAML file listing the workloads and cache
  configurations to analyse.
- `-o` selects the output directory for the generated report.

## Configuration File

The configuration file contains two lists:

```yaml
tests:
  - hello_world
  - cache_test
configs:
  - WT
  - WT_HYB
```

Modify these lists to add more workloads or cache modes.
