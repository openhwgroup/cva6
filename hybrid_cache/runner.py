"""Parallel analysis utilities."""

from __future__ import annotations

from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
from typing import Dict, Iterable

from .parser import parse_cache_stats


def collect_stats(tests: Iterable[str], configs: Iterable[str], base_dir: str | Path) -> Dict[str, Dict[str, Dict[str, int | float]]]:
    """Collect cache statistics for *tests* and *configs* in *base_dir*.

    Each configuration is assumed to have its own directory under *base_dir*.
    """

    base_dir = Path(base_dir)
    results: Dict[str, Dict[str, Dict[str, int | float]]] = {}

    def _process(args: tuple[str, str]) -> tuple[str, str, Dict[str, int | float]]:
        test, cfg = args
        cfg_dir = base_dir / cfg
        log_glob = list(cfg_dir.glob(f"simulation_artifacts/out_*/veri-testharness_sim/{test}.cv32a60x.log.*"))
        if not log_glob:
            raise FileNotFoundError(f"No log file for {test} / {cfg}")
        log_file = sorted(log_glob)[-1]
        stats = parse_cache_stats(log_file)
        return test, cfg, stats

    with ThreadPoolExecutor() as exe:
        futures = [exe.submit(_process, (test, cfg)) for test in tests for cfg in configs]
        for fut in futures:
            try:
                test, cfg, stats = fut.result()
            except FileNotFoundError:
                continue
            results.setdefault(test, {})[cfg] = stats

    return results
