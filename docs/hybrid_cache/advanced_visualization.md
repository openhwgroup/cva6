# Advanced Visualization

This short guide demonstrates how to generate timeline views and interactive charts.

1. Collect results as usual with `compare_hybrid_cache_configs.sh`.
2. Run `analyze_hybrid_cache.py` with the `--timeline-vcd` option to extract a signal from a VCD file.
3. Pass `--interactive` to also produce an HTML version of the timeline (requires `plotly`).

The resulting images can be found in the `charts/` subdirectory of the report output.
