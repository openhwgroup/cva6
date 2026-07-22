# Copyright 2022 Thales Silicon Security
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
# You may obtain a copy of the License at https://solderpad.org/licenses/
#
# Original Author: Guillaume Chauvon(guillaume.chauvon@thalesgroup.com)
# Contributors:   Théo Giovinazzi

import re
from pathlib import Path
from typing import Any, Dict, Optional

import typer
import yaml

import flows.utils.report_builder as rb

from flows.utils.utils import (
    autocompletion_target,
    print_error,
    print_info,
    print_recipe_title,
    print_step,
    print_success,
)

# Initialisation
app = typer.Typer(help="ASIC synthesis reporting and verification tool for area.")

DIFF_ENERGY = 0.5
DIFF_GATES = 250


# --- Functions ---
def load_yaml(file_path: Path) -> Dict[str, Any]:
    """Upload Yaml file"""
    if not file_path.exists():
        print_error(f"Error: YAML configuration file '{file_path}' not found.")
        raise typer.Exit(code=1)
    with open(file_path, "r", encoding="utf-8") as f:
        return yaml.safe_load(f)


def read_log(file_path: Path) -> str:
    """Read log file."""
    with open(file_path, "r", encoding="utf-8") as f:
        return f.read()


# --- Area ---
@app.command()
def report_dc_shell_check_area(
    target: str = typer.Option(
        ...,
        "--target",
        "-t",
        help="CVA6 user configuration",
        autocompletion=autocompletion_target,
    ),
    log: Path = typer.Option(None, help="Path to the area/summary log file."),
    synthesis_log: Path = typer.Option(None, help="Path to the full synthesis log."),
    config: Optional[Path] = typer.Option(
        None, "--config", help="Path to the YAML config file."
    ),
):
    """Analyze synthesis area (gate count) and parse logs for errors or warnings."""

    # Verif files
    if log is None:
        log = Path(f"build/{target}/synthesis/reports/synth_area.rpt")

    if synthesis_log is None:
        synthesis_log = Path(f"build/{target}/synthesis/synthesis.log")

    if config is None:
        config = Path(f"build/{target}/synthesis/build_config.yaml")

    if not log.exists() or not log.is_file():
        print_error(f"Error: Area log file not found at '{log}'")
        raise typer.Exit(code=1)

    if not synthesis_log.exists() or not synthesis_log.is_file():
        print_error(f"Error: Synthesis log file not found at '{synthesis_log}'")
        raise typer.Exit(code=1)

    # Report Path
    report_path = Path("build", f"{target}", "reports")
    if not report_path.exists():
        report_path.mkdir(parents=True, exist_ok=True)

    with open(config, "r", encoding="utf-8") as f:
        config_data = yaml.safe_load(f)

    # nand2area
    nand2area = float(config_data["NAND2_AREA"])
    if nand2area is None:
        print_error("Error: config file with NAND2_AREA must be provided via --config.")
        raise typer.Exit(code=1)

    # Expected Values Path
    path_expected_values = Path("config", "target", target, "expected_values.yml")

    print_recipe_title("Process Area Check")
    print_step("Used files")
    print_info(
        f"log :                     {log}\n"
        f"synthesis log :           {synthesis_log}\n"
        f"config file :             {config}\n"
        f"NAND2 Area ratio loaded:  {nand2area}"
    )

    # Upload files
    log_content = read_log(log)
    synthesis_log_content = read_log(synthesis_log)
    expected = load_yaml(Path(path_expected_values))

    ignored_warnings = {
        "RM-Error",
        "TFCHK-014",
        "TFCHK-012",
        "TFCHK-049",
        "MV-021",
        "MV-028",
        "TLUP-004",
        "TLUP-005",
        "TIM-164",
        "PWR-890",
        "PWR-80",
        "OPT-1413",
    }

    # Extract warning/error
    error_log, warning_log = [], []
    for line in synthesis_log_content.splitlines():
        if any(ignored in line for ignored in ignored_warnings):
            continue
        if "Error: " in line:
            error_log.append(line)
        elif "Warning: " in line:
            warning_log.append(line)

    # Define Metric
    log_metric = rb.LogMetric("Synthesis full log")
    log_metric.values = error_log + warning_log

    # Parsing
    area_pattern = re.compile(
        r"^(Combinational area|Buf/Inv area|Noncombinational area|Macro/Black Box area): +(\d*\.\d*)$",
        re.MULTILINE,
    )
    hier_pattern = re.compile(
        r"^(\w*(?::\/\/\w*){0,2}) +(\d*\.\d*) +(\d*\.\d*) +(\d*\.\d*) +(\d*\.\d*) +(\d*\.\d*) +(\w*)$",
        re.MULTILINE,
    )

    global_val = area_pattern.findall(log_content)
    hier = hier_pattern.findall(log_content)

    if not hier:
        print_error("Error: Hierarchical area data could not be parsed.")
        raise typer.Exit(code=1)

    # Define values
    total_area = float(hier[0][1])
    kgates = total_area / nand2area
    gates = int(kgates * 1000)

    result_metric = rb.TableMetric("Area results")
    result_metric.add_value("Total area", f"{gates} Gates")

    for name, area_str in global_val:
        rel_area = 0 if total_area == 0 else int(float(area_str) / total_area * 100)
        result_metric.add_value(name, f"{rel_area} %")

    # find target if no target
    if target is None:
        path_re = re.search(r"build/([^/]+)/synthesis", str(log))
        if path_re:
            target = path_re.group(1)
        else:
            print_error(f"Error: Target could not be inferred from path: {log}")
            raise typer.Exit(code=1)

    diff = gates - expected.get("gates", 0)
    if abs(diff) >= DIFF_GATES:
        result_metric.fail()

    hier_metric = rb.TableMetric("Hierarchies details")
    for item in hier:
        hier_metric.add_value(
            item[0],
            f"{float(item[1]) / nand2area:.2f} kGates",
            f"{float(item[2]):.2f} %",
        )

    report = rb.Report(f"{kgates:.2f} kGates")
    report.add_metric(result_metric, hier_metric, log_metric)

    # Exit file
    report.dump()

    print_step("Result")
    # Display Rich
    if report.failed:
        print_info(
            f"[red]Gate count deviation limit exceeded (>= {DIFF_GATES} gates)[/red]\n\n"
            f"Target:    {target}\n"
            f"Expected:  {expected.get('gates', 0)} gates\n"
            f"Observed:  {gates} gates\n"
            f"Delta:     {diff} gates"
        )

    else:
        print_success(
            f"Gate count validation passed successfully.\n\n"
            f"Target:    {target}\n"
            f"Total:     {gates} Gates ({kgates:.2f} kGates)"
        )
