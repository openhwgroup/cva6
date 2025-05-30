#!/usr/bin/env python3
"""Generate a 2D heatmap of SRAM block accesses from a VCD file.

This tool parses a simulation VCD and counts read and write accesses for each
cache block (set/way pair).  When the VCD corresponds to one of the supported
cache configurations (WT, WT_HYB, WT_HYB_FORCE_FULL_ASS, WT_HYB_FORCE_SET_ASS)
it prints an ASCII 2D map showing how often each block was accessed.

Blank spaces denote blocks that were never accessed, lower case letters denote
low activity, upper case letters higher activity and the digits ``0``–``9``
mark the ten most accessed blocks (``0`` being the hottest).
"""

from __future__ import annotations

import argparse
import math
import os
import re
from collections import defaultdict
from typing import Dict, Tuple


# Characters used for the intensity map.  First 26 lower case, then 26 upper
# case, finally digits 0-9 for the ten hottest blocks.
INTENSITY_CHARS = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789"

# ----------------------------------------------------------------------------
# VCD parsing helpers
# ----------------------------------------------------------------------------

def parse_header(vcd_file: str) -> Tuple[Dict[str, dict], dict]:
    """Parse the VCD header and return the signal dictionary and metadata."""
    signals: Dict[str, dict] = {}
    meta: dict = {
        "sets": None,
        "ways": None,
        "mode": None,
    }

    with open(vcd_file, "r") as f:
        current_scope: list[str] = []
        for line in f:
            if line.startswith("$enddefinitions"):
                break

            if line.startswith("$scope"):
                current_scope.append(line.split()[2])
                continue
            if line.startswith("$upscope"):
                if current_scope:
                    current_scope.pop()
                continue
            if not line.startswith("$var"):
                # Detect mode and parameters in comments/defines
                if "WT_HYB_FORCE_FULL_ASS" in line:
                    meta["mode"] = "WT_HYB_FORCE_FULL_ASS"
                elif "WT_HYB_FORCE_SET_ASS" in line:
                    meta["mode"] = "WT_HYB_FORCE_SET_ASS"
                elif "WT_HYB" in line and meta.get("mode") is None:
                    meta["mode"] = "WT_HYB"
                elif "WT" in line and meta.get("mode") is None:
                    meta["mode"] = "WT"

                m = re.search(r"DCACHE_CL_IDX_WIDTH=(\d+)", line)
                if m:
                    meta["sets"] = 2 ** int(m.group(1))
                m = re.search(r"DCACHE_SET_ASSOC=(\d+)", line)
                if m:
                    meta["ways"] = int(m.group(1))
                continue

            parts = line.split()
            if len(parts) < 5:
                continue
            _var, sig_type, width, ident, name = parts[:5]
            full_name = ".".join(current_scope + [name])
            signals[ident] = {
                "name": name,
                "full": full_name,
                "width": int(width),
            }

            # Some heuristics to determine number of sets/ways in case it was
            # not encoded in the header comments.
            if meta["ways"] is None and re.search(r"hit_oh", full_name):
                meta["ways"] = int(width)
            if meta["sets"] is None and re.search(r"_idx", full_name):
                meta["sets"] = 2 ** int(width)

    return signals, meta


def parse_vcd(vcd_file: str, signals: Dict[str, dict]) -> Dict[Tuple[int, int], int]:
    """Return a dictionary mapping (set, way) to access count."""
    # Identify interesting signal ids by name patterns
    id_rd_idx = None
    id_wr_cl_idx = None
    id_wr_idx = None
    id_rd_hit_oh = None
    id_wr_cl_we = None
    id_wr_req = None
    id_wr_cl_vld = None

    for ident, info in signals.items():
        n = info["full"].lower()
        if id_rd_idx is None and re.search(r"rd_idx", n):
            id_rd_idx = ident
        if id_wr_cl_idx is None and re.search(r"wr_cl_idx", n):
            id_wr_cl_idx = ident
        if id_wr_idx is None and re.search(r"wr_idx", n) and "cl" not in n:
            id_wr_idx = ident
        if id_rd_hit_oh is None and re.search(r"rd_hit_oh", n):
            id_rd_hit_oh = ident
        if id_wr_cl_we is None and re.search(r"wr_cl_we", n):
            id_wr_cl_we = ident
        if id_wr_req is None and re.search(r"wr_req", n):
            id_wr_req = ident
        if id_wr_cl_vld is None and re.search(r"wr_cl_vld", n):
            id_wr_cl_vld = ident

    # Current values for signals
    cur: Dict[str, str] = defaultdict(str)

    counts: Dict[Tuple[int, int], int] = defaultdict(int)

    with open(vcd_file, "r") as f:
        in_data = False
        for line in f:
            if not in_data:
                if line.startswith("$enddefinitions"):
                    in_data = True
                continue

            if line.startswith("#"):
                # Time stamp, ignore
                continue
            if line[0] in "01" and len(line) > 1:
                val = line[0]
                ident = line[1:].strip()
            elif line.startswith("b"):
                val, ident = line[1:].split()
            else:
                continue

            if ident not in signals:
                continue
            cur[ident] = val

            if ident == id_rd_hit_oh and val.strip() != "0":
                # decode vector
                bits = int(val, 2) if val.startswith("b") else int(val)
                set_idx = int(cur.get(id_rd_idx, "0"), 2) if id_rd_idx else 0
                for way in range(signals[ident]["width"]):
                    if bits & (1 << way):
                        counts[(set_idx, way)] += 1
            elif ident in {id_wr_cl_we, id_wr_req} and val.strip() != "0":
                bits = int(val, 2) if val.startswith("b") else int(val)
                if ident == id_wr_cl_we:
                    set_idx = int(cur.get(id_wr_cl_idx, "0"), 2) if id_wr_cl_idx else 0
                    valid = cur.get(id_wr_cl_vld, "1") != "0"
                else:
                    set_idx = int(cur.get(id_wr_idx, "0"), 2) if id_wr_idx else 0
                    valid = True
                if not valid:
                    continue
                for way in range(signals[ident]["width"]):
                    if bits & (1 << way):
                        counts[(set_idx, way)] += 1

    return counts


# ----------------------------------------------------------------------------
# Heatmap generation
# ----------------------------------------------------------------------------

def build_heatmap(counts: Dict[Tuple[int, int], int], sets: int, ways: int) -> str:
    """Return ASCII heatmap string."""
    if not counts:
        return "No access data found"

    # Determine top ten blocks
    flat = [((s, w), c) for (s, w), c in counts.items() if c > 0]
    flat.sort(key=lambda x: x[1], reverse=True)
    top10 = {pos: str(i) for i, (pos, _) in enumerate(flat[:10])}
    max_other = flat[10][1] if len(flat) > 10 else (flat[0][1] if flat else 1)

    def char_for(set_idx: int, way_idx: int) -> str:
        c = counts.get((set_idx, way_idx), 0)
        if c == 0:
            return " "
        if (set_idx, way_idx) in top10:
            return top10[(set_idx, way_idx)]
        if max_other == 0:
            idx = 0
        else:
            idx = int((c / max_other) * 51)
        if idx < 26:
            return chr(ord("a") + idx)
        else:
            return chr(ord("A") + idx - 26)

    lines = []
    lines.append("+" + "-" * sets + "+")
    for way in range(ways):
        row = [char_for(s, way) for s in range(sets)]
        lines.append("|" + "".join(row) + "|")
    lines.append("+" + "-" * sets + "+")
    return "\n".join(lines)


def main() -> None:
    parser = argparse.ArgumentParser(description="Generate SRAM block access heatmap from VCD")
    parser.add_argument("vcd", type=str, help="Input VCD file")
    args = parser.parse_args()

    if not os.path.exists(args.vcd):
        raise SystemExit(f"VCD file {args.vcd} not found")

    signals, meta = parse_header(args.vcd)

    if meta["mode"] not in {"WT", "WT_HYB", "WT_HYB_FORCE_FULL_ASS", "WT_HYB_FORCE_SET_ASS"}:
        raise SystemExit("Unsupported or undetected cache configuration")

    counts = parse_vcd(args.vcd, signals)

    sets = meta.get("sets") or 16
    ways = meta.get("ways") or 8

    print(f"Cache mode: {meta['mode']}")
    print(f"Cache geometry: {ways} ways x {sets} sets")
    print()
    print(build_heatmap(counts, sets, ways))


if __name__ == "__main__":
    main()
