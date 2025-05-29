# Hybrid Cache Tutorial

This short tutorial demonstrates how to compare cache configurations.

1. **Run comparisons**
   ```bash
   ./compare_hybrid_cache_configs.sh config/hybrid_cache_analysis.yml
   ```
   The script builds and runs the specified benchmarks for each cache mode.

2. **Analyse results**
   ```bash
   python3 analyze_hybrid_cache.py hybrid_cache_comparison_<timestamp> \
          --config config/hybrid_cache_analysis.yml -o report -j 4
   ```
   Replace `<timestamp>` with the directory printed at the end of the comparison
   script.

3. **View report**
   Open `report/cache_analysis_report.md` in a markdown viewer. Charts and summary
   tables help to understand performance and cache behaviour.
