# Hybrid Cache Design

This document provides an overview of the hybrid cache architecture used in CVA6.
It complements `hybrid_cache_validation.md` with a concise design reference.

## Modes
- **Write Through (WT)** – standard set associative cache.
- **WT_HYB** – dynamically switches between set associative and fully associative
  organisations depending on the current privilege level.
- **WT_HYB_FORCE_SET_ASS** – hybrid cache forced into set associative mode.
- **WT_HYB_FORCE_FULL_ASS** – hybrid cache forced into fully associative mode.

## Replacement Policies
The cache supports retaining or flushing data when changing modes. Additional
algorithms such as round-robin or pseudo random victim selection are available.

## Usage
Set the `DCacheType` parameter in the configuration package to one of the modes
above. The analysis utilities found in this repository can be used to benchmark
different configurations and visualise their behaviour.
