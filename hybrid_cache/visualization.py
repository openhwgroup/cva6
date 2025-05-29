"""Visualization utilities for cache analysis."""

from __future__ import annotations

import os
from pathlib import Path
from typing import Dict

import matplotlib.pyplot as plt


def generate_comparison_chart(results: Dict[str, Dict[str, int | float]], test_name: str, output_dir: str | Path) -> None:
    """Generate comparison charts for cache configurations."""
    output_dir = Path(output_dir)
    (output_dir / "charts").mkdir(parents=True, exist_ok=True)

    configs = list(results.keys())
    metrics = ["hit_ratio", "cycles"]

    for metric in metrics:
        values = [results[cfg].get(metric, 0) for cfg in configs]
        plt.figure(figsize=(10, 6))
        bars = plt.bar(configs, values)
        for bar in bars:
            height = bar.get_height()
            plt.text(
                bar.get_x() + bar.get_width() / 2.0,
                height,
                f"{height:.1f}" if metric == "hit_ratio" else f"{height}",
                ha="center",
                va="bottom",
            )
        plt.title(f"{test_name} - {metric.replace('_', ' ').title()}")
        plt.ylabel(
            f"{metric.replace('_', ' ').title()}" + (" (%)" if metric == "hit_ratio" else " (cycles)")
        )
        plt.tight_layout()
        plt.savefig(output_dir / "charts" / f"{test_name}_{metric}.png")
        plt.close()

    if "WT_HYB" in configs:
        plt.figure(figsize=(10, 6))
        hybrid = results.get("WT_HYB", {})
        labels = ["Set Associative Hits", "Fully Associative Hits"]
        values = [hybrid.get("set_assoc_hits", 0), hybrid.get("full_assoc_hits", 0)]
        plt.pie(values, labels=labels, autopct="%1.1f%%", startangle=90)
        plt.axis("equal")
        plt.title(f"{test_name} - WT_HYB Hit Distribution")
        plt.savefig(output_dir / "charts" / f"{test_name}_hybrid_hit_distribution.png")
        plt.close()
