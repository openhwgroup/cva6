# Copyright 2022 Thales Silicon Security
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
# You may obtain a copy of the License at https://solderpad.org/licenses/
#
# Original Author: Guillaume Chauvon(guillaume.chauvon@thalesgroup.com)
# Contributors:   Théo Giovinazzi

import csv
import re
from pathlib import Path
from typing import Dict, List, Optional

import plotly.graph_objects as go
import typer
import yaml

from flows.utils.utils import (
    autocompletion_target,
    print_error,
    print_info,
    print_recipe_title,
    print_step,
    print_success,
)

# --- Setup Typer & Rich ---
app = typer.Typer(help="CLI for ASIC Synthesis Area reporting.", add_completion=False)

# --- Shared Variables ---
CSV_COLUMNS_AREA = [
    "hier0",
    "hier1",
    "hier2",
    "hier3",
    "hier4",
    "hier5",
    "hier6",
    "hier7",
    "hier8",
    "areaTot",
    "P100Tot",
    "Combi",
    "NonCombi",
    "BlackBox",
    "InstanceName",
]

# ==========================================
# ============ AREA LOGIC ==================
# ==========================================


def parse_area_log(log_content: str) -> List[Dict[str, str]]:
    pattern = re.compile(
        r"(?P<hier0>[\w\d]+)(/(?P<hier1>[\w\d]+))?(/(?P<hier2>[\w\d]+))?"
        r"(/(?P<hier3>[\w\d]+))?(/(?P<hier4>[\w\d]+))?(/(?P<hier5>[\w\d]+))?"
        r"(/(?P<hier6>[\w\d]+))?(/(?P<hier7>[\w\d]+))?(/(?P<hier8>[\w\d]+))?"
        r"\s+(?P<areaTot>[\d.]+)\s+(?P<P100Tot>[\d.]+)\s+(?P<Combi>[\d.]+)"
        r"\s+(?P<NonCombi>[\d.]+)\s+(?P<BlackBox>[\d.]+)\s+(?P<InstanceName>[\w\d]+)"
    )
    dict_data = []
    for line in pattern.finditer(log_content):
        dict_data.append(line.groupdict())
    return dict_data


def generate_area_csv(dict_data: List[Dict], csv_name: str, quiet: bool = False):
    try:
        with open(csv_name, "w", newline="", encoding="utf-8") as csvfile:
            writer = csv.DictWriter(csvfile, fieldnames=CSV_COLUMNS_AREA)
            writer.writeheader()
            for data in dict_data:
                writer.writerow(data)
    except IOError as e:
        print_error(f"I/O error generating CSV: {e}", quiet=quiet)


# ==========================================
# ============== COMMANDS ==================
# ==========================================


@app.command()
def report_dc_shell_graph_area(
    target: str = typer.Option(
        ...,
        "--target",
        "-t",
        help="CVA6 user configuration",
        autocompletion=autocompletion_target,
    ),
    in_report: Optional[Path] = typer.Option(
        None, "--in-report", help="Input file to analyze"
    ),
    config: Optional[Path] = typer.Option(
        None, "--config", help="Path to the YAML config file."
    ),
    top: str = typer.Option("cva6_example_obi", "--top", help="Top module to analyze"),
    quiet: bool = typer.Option(
        False, "--quiet", "-q", help="Suppress output (errors only)"
    ),
):
    """Analyze synthesis area reports and generate Sunburst charts."""

    if in_report is None:
        in_report = Path(f"build/{target}/synthesis/reports/synth_area.rpt")

    if config is None:
        config = Path(f"build/{target}/synthesis/build_config.yaml")

    if not in_report.exists() or not in_report.is_file():
        print_error(f"Error: Area report file not found at '{in_report}'", quiet=quiet)
        raise typer.Exit(code=1)

    if not config.exists() or not config.is_file():
        print_error(f"Error: Area report file not found at '{config}'", quiet=quiet)
        raise typer.Exit(code=1)

    # Report Path
    report_path = Path("build", f"{target}", "reports")
    if not report_path.exists():
        report_path.mkdir(parents=True, exist_ok=True)

    with open(config, "r", encoding="utf-8") as f:
        config_data = yaml.safe_load(f)

    nand2area = float(config_data["NAND2_AREA"])

    print_recipe_title("Process Area Graph", quiet=quiet)

    # Print entry files
    print_step("Used files", quiet=quiet)
    print_info(
        f"report:                   {in_report}\n"
        f"config file:              {config}\n"
        f"NAND2 Area ratio loaded:  {nand2area}",
        quiet=quiet,
    )

    with open(in_report, "r", encoding="utf-8") as f:
        log_content = f.read()

    csv_name = report_path / f"{in_report.stem}.csv"
    dict_data = parse_area_log(log_content)
    generate_area_csv(dict_data, csv_name, quiet=quiet)

    labels, values, parents, ids = [], [], [], []

    # Build hierarchy tree
    for elm in dict_data:
        i = 0
        while i < 8 and elm.get(CSV_COLUMNS_AREA[i + 1]) is not None:
            i += 1

        if elm.get("areaTot") and float(elm["areaTot"]) / nand2area > 0.001:
            labels.append(elm[CSV_COLUMNS_AREA[i]])
            values.append(float(elm["areaTot"]) / nand2area)

            ids_name = ""
            parents_name = ""

            if i == 0:
                ids_name = labels[-1]
                parents_name = "" if elm[CSV_COLUMNS_AREA[i]] == top else top
            else:
                for j in range(i + 1):
                    ids_name += str(elm.get(CSV_COLUMNS_AREA[j], ""))
                for j in range(i):
                    parents_name += str(elm.get(CSV_COLUMNS_AREA[j], ""))

            parents.append(parents_name)
            ids.append(ids_name)

    # Plotly Generation
    fig = go.Figure(
        data=[
            go.Sunburst(
                ids=ids,
                labels=labels,
                parents=parents,
                values=values,
                branchvalues="total",
            )
        ]
    )

    html_name = report_path / f"{in_report.stem}.html"
    fig.write_html(html_name)
    # Print files
    print_step("Generated files", quiet=quiet)
    print_info(
        f"CSV file for {in_report.name}:    {csv_name}\n"
        f"HTML file for {in_report.name}:   {html_name}\n",
        quiet=quiet,
    )
    print_success("Success", quiet=quiet)
