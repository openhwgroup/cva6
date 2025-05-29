"""Parsing utilities for hybrid cache logs and waveforms."""

from __future__ import annotations

import os
import re
from pathlib import Path
from typing import Dict, Iterable, Iterator


def parse_cache_stats(log_file: str | Path) -> Dict[str, int | float]:
    """Parse cache statistics from simulation log file.

    Missing values are returned as 0.
    """
    stats = {
        "hits": 0,
        "misses": 0,
        "hit_ratio": 0.0,
        "mode_switches": 0,
        "set_assoc_hits": 0,
        "full_assoc_hits": 0,
        "cycles": 0,
        "set_assoc_time": 0,
        "full_assoc_time": 0,
    }

    log_path = Path(log_file)
    if not log_path.exists():
        raise FileNotFoundError(f"Log file {log_file} not found")

    content = log_path.read_text(encoding="utf-8", errors="ignore")

    match = re.search(r"Finished after (\d+) cycles", content)
    if match:
        stats["cycles"] = int(match.group(1))

    hit_match = re.search(r"Cache hits: (\d+)", content)
    miss_match = re.search(r"Cache misses: (\d+)", content)
    if hit_match and miss_match:
        stats["hits"] = int(hit_match.group(1))
        stats["misses"] = int(miss_match.group(1))
        total = stats["hits"] + stats["misses"]
        if total:
            stats["hit_ratio"] = stats["hits"] / total * 100

    set_match = re.search(r"Set associative hits: (\d+)", content)
    if set_match:
        stats["set_assoc_hits"] = int(set_match.group(1))
    full_match = re.search(r"Fully associative hits: (\d+)", content)
    if full_match:
        stats["full_assoc_hits"] = int(full_match.group(1))

    switch_match = re.search(r"Mode switches: (\d+)", content)
    if switch_match:
        stats["mode_switches"] = int(switch_match.group(1))

    set_time_match = re.search(r"Time in set associative mode: (\d+) cycles", content)
    if set_time_match:
        stats["set_assoc_time"] = int(set_time_match.group(1))
    full_time_match = re.search(r"Time in fully associative mode: (\d+) cycles", content)
    if full_time_match:
        stats["full_assoc_time"] = int(full_time_match.group(1))

    return stats


def stream_vcd_signals(vcd_path: str | Path, signal: str) -> Iterator[int]:
    """Yield values of *signal* from VCD file line by line.

    This avoids loading the entire file into memory. It is a simple parser
    for integer-valued signals and assumes a two-state VCD for brevity.
    """
    vcd_path = Path(vcd_path)
    if not vcd_path.exists():
        raise FileNotFoundError(f"VCD file {vcd_path} not found")

    regex = re.compile(fr"^b([01]+)\s+{re.escape(signal)}$")
    with vcd_path.open("r", encoding="utf-8", errors="ignore") as fh:
        for line in fh:
            match = regex.search(line.strip())
            if match:
                yield int(match.group(1), 2)

def analyze_hit_signal(vcd_path: str | Path, signal: str = "hit") -> int:
    """Return the total number of asserted *signal* values in the VCD file."""
    count = 0
    for val in stream_vcd_signals(vcd_path, signal):
        if val:
            count += 1
    return count
