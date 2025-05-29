"""Configuration utilities for hybrid cache analysis."""

import yaml
from pathlib import Path
from typing import Any, Dict

DEFAULT_CONFIG = {
    "tests": ["hello_world", "cache_test", "cache_thrash"],
    "configs": ["WT", "WT_HYB", "WT_HYB_FORCE_SET_ASS", "WT_HYB_FORCE_FULL_ASS"],
}


def load_config(path: str | Path | None) -> Dict[str, Any]:
    """Load YAML configuration from *path*.

    If *path* is None or the file does not exist, returns ``DEFAULT_CONFIG``.
    """
    if path is None:
        return DEFAULT_CONFIG

    path = Path(path)
    if not path.exists():
        raise FileNotFoundError(f"Config file {path} not found")

    with path.open("r", encoding="utf-8") as fh:
        data = yaml.safe_load(fh) or {}

    # merge with defaults
    cfg = DEFAULT_CONFIG.copy()
    cfg.update(data)
    return cfg
