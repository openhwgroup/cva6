"""Parallel analysis utilities."""

from __future__ import annotations

from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
from typing import Dict, Iterable

from .parser import parse_cache_stats


def collect_stats(
    tests: Iterable[str],
    configs: Iterable[str],
    base_dir: str | Path,
    jobs: int | None = None,
    verbose: bool = False,
) -> Dict[str, Dict[str, Dict[str, int | float]]]:
    """Collect cache statistics for *tests* and *configs* in *base_dir*.

    Each configuration is assumed to have its own directory under *base_dir*.
    Set *verbose* to ``True`` to print progress information and warnings.
    """

    base_dir = Path(base_dir)
    if not base_dir.is_dir():
        raise FileNotFoundError(f"Base directory {base_dir} not found")
    results: Dict[str, Dict[str, Dict[str, int | float]]] = {}

    def _find_log_file(cfg_dir: Path, test: str) -> Path | None:
        patterns = [
            f"simulation_artifacts/out_*/veri-testharness_sim/{test}.cv32a60x.log.*",
            f"simulation_artifacts/*/{test}.cv32a60x.log.*",
        ]
        for pat in patterns:
            files = list(cfg_dir.glob(pat))
            if files:
                return sorted(files)[-1]
        return None

    def _process(args: tuple[str, str]) -> tuple[str, str, Dict[str, int | float]]:
        test, cfg = args
        cfg_dir = base_dir / cfg
        log_file = _find_log_file(cfg_dir, test)
        if log_file is None:
            if verbose:
                print(f"Warning: no log file found for {test} / {cfg}")
            raise FileNotFoundError(f"No log file for {test} / {cfg}")
        if verbose:
            print(f"Parsing log for {test} / {cfg}: {log_file}")
        stats = parse_cache_stats(log_file)
        return test, cfg, stats

    with ThreadPoolExecutor(max_workers=jobs) as exe:
        futures = [exe.submit(_process, (test, cfg)) for test in tests for cfg in configs]
        for fut in futures:
            try:
                test, cfg, stats = fut.result()
            except FileNotFoundError:
                continue
            except Exception as e:  # pragma: no cover - unexpected failures
                if verbose:
                    print(f"Error processing {fut}: {e}")
                continue
            results.setdefault(test, {})[cfg] = stats

    return results
