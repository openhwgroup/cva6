# Copyright 2026 Thales France
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
# You may obtain a copy of the License at https://solderpad.org/licenses/
#
# Original Author: Yannick Casamatta (yannick.casamatta@thalesgroup.com)

# Please refer to flows/README.md to add target

from pathlib import Path
import typer
import yaml

import flows.utils.report_builder as rb

from flows.utils.manifest import require_prerequisite
from flows.utils.utils import (
    CompMode,
    autocompletion_target,
    autocompletion_testname_compiled,
    print_error,
    print_info,
    print_recipe_title,
    print_success,
    print_param_table,
    print_recipe_end,
)

# Initialisation
app = typer.Typer()


@app.command()
def report_benchmark(
    target: str = typer.Option(
        ...,
        "--target",
        "-t",
        help="CVA6 user configuration",
        autocompletion=autocompletion_target,
    ),
    test_name: str = typer.Option(
        ...,
        "--testname",
        "-n",
        help="Test name (compiled from list or not)",
        autocompletion=autocompletion_testname_compiled,
    ),
    comp_mode: CompMode = typer.Option(CompMode.rtl, help="Hardware compilation mode"),
    quiet: bool = typer.Option(
        False, "--quiet", "-q", help="Suppress output (errors only)"
    ),
):
    """Analyze performance benchmark logs and validate cycles against expected values."""

    # Init code
    code = 0

    print_recipe_title("Check benchmark KPI", quiet=quiet)

    print_param_table(
        {
            "Target": target,
            "Test name": test_name,
            "Compilation mode": comp_mode.value,
        },
        "Options",
        quiet=quiet,
    )

    # Mode dir
    if comp_mode == CompMode.rtl:
        inout_dir = "sim_rtl"
    elif comp_mode == CompMode.coverage:
        inout_dir = "sim_cov"
    elif comp_mode == CompMode.gate_wc_timing:
        inout_dir = "sim_gate_wc_timing"
    elif comp_mode == CompMode.gate_wc_power:
        inout_dir = "sim_gate_wc_power"
    else:
        print_error("Unknown comp_mode", quiet=quiet)
        raise typer.Exit(code=1)

    # Create files and folder paths
    repo_dir = Path.cwd()
    expected_values_path = (
        repo_dir / "config" / "target" / target / "expected_values.yml"
    )
    build_root = repo_dir / "build" / target
    simulation_dir = build_root / "simulation" / inout_dir / test_name
    file_GLOBAL_PATTERN_start_cycle = (
        simulation_dir / "timing_GLOBAL_PATTERN_start_cycle"
    )
    file_GLOBAL_PATTERN_end_cycle = simulation_dir / "timing_GLOBAL_PATTERN_end_cycle"

    for cycle_file in [
        file_GLOBAL_PATTERN_start_cycle,
        file_GLOBAL_PATTERN_end_cycle,
    ]:
        require_prerequisite(
            cycle_file,
            f"simulation timing results for test '{test_name}' (comp mode '{comp_mode.value}')",
            f"./cook.py vcs-uvm-run -t {target} -n {test_name} --comp-mode {comp_mode.value}",
        )

    start_cycle = int(file_GLOBAL_PATTERN_start_cycle.read_text().strip())
    end_cycle = int(file_GLOBAL_PATTERN_end_cycle.read_text().strip())

    # Extract reference values
    with expected_values_path.open("r", encoding="utf-8") as f:
        expected = yaml.safe_load(f)

    cycle_key = f"{test_name}_cycle"
    iters_key = f"{test_name}_iters"

    try:
        valid_cycles = int(expected[cycle_key])
        iterations = int(expected[iters_key])
    except KeyError as e:
        print_error(
            f"Error: Keys '{cycle_key}' or '{iters_key}' missing in {expected_values_path}",
            quiet=quiet,
        )
        raise typer.Exit(code=1) from e

    print_info(
        f"Read expected from {expected_values_path}\n- {iterations} iterations\n- {valid_cycles} expected cycles.",
        quiet=quiet,
    )
    print_info(
        f"Read measured from\n- {file_GLOBAL_PATTERN_start_cycle}\n- {file_GLOBAL_PATTERN_end_cycle}",
        quiet=quiet,
    )

    cycles = end_cycle - start_cycle
    title_metric = f"{test_name} results"
    score_metric = rb.TableMetric(title_metric)
    score_metric.add_value("cycles", cycles)

    ipmhz = iterations * 1000000 / cycles

    if "dhrystone" in test_name:
        score_metric.add_value("Dhrystone/MHz", f"{ipmhz:.2f}")
        score_metric.add_value("DMIPS/MHz", f"{ipmhz / 1757:.2f}")
    elif "coremark" in test_name:
        score_metric.add_value("CoreMark/MHz", f"{ipmhz:.2f}")

    diff = cycles - valid_cycles

    print_param_table(
        {
            "Expected": f"{valid_cycles} cycles",
            "Observed": f"{cycles} cycles",
            "Diff": f"{diff} cycles",
            "Perf": f"{ipmhz:.2f} Iters/MHz",
        },
        "Results",
        quiet=quiet,
    )

    if diff != 0:
        score_metric.fail()
        score_metric.add_value("Cycles diff", diff)
        code = 1
        print_error("FAIL: Cycle count deviation detected!", quiet=quiet)
    else:
        print_success("PASS: Cycle count matchs!", quiet=quiet)

    report = rb.Report(f"{cycles / 1000:.2f} kCycles")
    report.add_metric(score_metric)
    report.dump()

    print_recipe_end("Completed", quiet=quiet)

    if code != 0:
        raise typer.Exit(code=1)
