#!/usr/bin/env python3
# Copyright 2026 OpenHW Group
# SPDX-License-Identifier: Apache-2.0
"""Parse CI job names into structured data for the CVA6 tier dashboard."""

import re
from typing import Optional

# Utility/infrastructure jobs to skip (not actual test executions)
SKIP_JOBS = {
    "Setup Tools",
    "Test Summary",
    "Resolve Tier",
    "Prepare Matrix",
    "build-riscv-tests",
    "report-summary",
    "setup-tools",
    "resolve-tier",
    "prepare-matrix",
}

# All known CVA6 configs (longest first for greedy match)
KNOWN_CONFIGS = [
    "cv64a6_imafdc_sv39_hpdcache_wb",
    "cv32a60x",
    "cv32a65x",
]


def parse_job_name(job_name: str, workflow_name: str) -> Optional[dict]:
    """Parse a CI job name into structured fields.

    Returns:
        dict with keys: arch, config, testcase, simulator (optional)
        None if the job should be skipped (utility/infrastructure job)
    """
    name = job_name.strip()

    # Skip utility jobs
    if name in SKIP_JOBS:
        return None

    # --- tier workflows ---
    m = re.match(r"^(RV(?:32|64))\s+Tier[12]\s+(.+?)\s+/\s+(.+)$", name)
    if m:
        arch = m.group(1).lower()
        config = m.group(2).strip()
        testcase = m.group(3).strip()
        if "${{" in testcase or "${{" in config:
            return None
        return {
            "arch": arch,
            "config": config,
            "testcase": testcase,
        }

    # --- tier workflows and similar matrix-style workflows ---
    # Format: "RV64 {testcase} ({config})" or "RV32 {testcase} ({config})"
    m = re.match(r"^(RV(?:32|64))\s+(.+?)\s+\(([^)]+)\)$", name)
    if m:
        arch = m.group(1).lower()
        testcase = m.group(2).strip()
        config = m.group(3).strip()
        # Skip unresolved matrix placeholders from early-failed/skipped runs
        # (e.g. "RV64 ${{ matrix.testcase }} (${{ matrix.config }})")
        if "${{" in testcase or "${{" in config:
            return None
        return {
            "arch": arch,
            "config": config,
            "testcase": testcase,
        }

    # --- ci.yml ---
    # Format: "execute-riscv64-tests (config, simulator, testcase)"
    #      or "execute-riscv32-tests (testcase, config, simulator)"
    m = re.match(
        r"^execute-riscv(32|64)-tests\s+\(([^)]+)\)$", name
    )
    if m:
        arch = f"rv{m.group(1)}"
        params = [p.strip() for p in m.group(2).split(",")]

        if arch == "rv64" and len(params) == 3:
            # ci.yml rv64 matrix: (testcase, config, simulator)
            # Actually from the workflow: matrix keys are testcase, config, simulator
            # GitHub renders them in the order they appear in the matrix definition
            # For execute-riscv64-tests: testcase, config, simulator
            testcase, config, simulator = params
            return {
                "arch": arch,
                "config": config,
                "testcase": testcase,
                "simulator": simulator,
            }
        elif arch == "rv32" and len(params) == 3:
            # ci.yml rv32 matrix: (testcase, config, simulator)
            testcase, config, simulator = params
            return {
                "arch": arch,
                "config": config,
                "testcase": testcase,
                "simulator": simulator,
            }
        elif len(params) >= 2:
            # Fallback for unexpected param count
            return {
                "arch": arch,
                "config": params[1] if len(params) > 1 else "unknown",
                "testcase": params[0],
            }

    # Unrecognized job name - skip it
    return None


def arch_from_config(config: str) -> str:
    """Infer architecture from config name."""
    if config.startswith("cv64"):
        return "rv64"
    elif config.startswith("cv32"):
        return "rv32"
    return "unknown"


if __name__ == "__main__":
    # Quick self-test
    test_cases = [
        ("RV64 Tier2 cv64a6_imafdc_sv39_hpdcache_wb / dv-riscv-arch-test", "tier2"),
        ("RV32 Tier1 cv32a65x / smoke-tests-cv32a65x", "tier1"),
        ("RV64 Tier2 cv64a6_imafdc_sv39_hpdcache_wb / benchmark", "tier2"),
        (
            "execute-riscv64-tests (cv64a6_imafdc_tests, cv64a6_imafdc_sv39_hpdcache, veri-testharness)",
            "ci",
        ),
        (
            "execute-riscv32-tests (dv-riscv-arch-test, cv32a65x, veri-testharness)",
            "ci",
        ),
        ("Setup Tools", "tier2"),
        ("Test Summary", "tier1"),
    ]

    for job_name, wf in test_cases:
        result = parse_job_name(job_name, wf)
        print(f"  {job_name!r:80s} -> {result}")
