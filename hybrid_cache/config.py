"""Configuration utilities for hybrid cache analysis."""

import yaml
from pathlib import Path
from typing import Any, Dict

DEFAULT_CONFIG = {
    "tests": ["hello_world", "cache_test", "cache_thrash"],
    "configs": ["WT", "WT_HYB", "WT_HYB_FORCE_SET_ASS", "WT_HYB_FORCE_FULL_ASS"],
}


def validate_config(cfg: Dict[str, Any]) -> None:
    """Validate configuration dictionary.

    Raises ``ValueError`` if required keys are missing or invalid.
    """
    if not cfg.get("tests"):
        raise ValueError("Configuration is missing 'tests' list")
    if not cfg.get("configs"):
        raise ValueError("Configuration is missing 'configs' list")
    if not isinstance(cfg["tests"], list) or not all(isinstance(t, str) for t in cfg["tests"]):
        raise ValueError("'tests' must be a list of strings")
    if not isinstance(cfg["configs"], list) or not all(isinstance(c, str) for c in cfg["configs"]):
        raise ValueError("'configs' must be a list of strings")


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
    validate_config(cfg)
    return cfg
