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
import shutil
from enum import Enum
import typer
import yaml
from flows.utils.utils import (
    Cva6Hier,
    autocompletion_target,
    print_recipe_title,
    print_recipe_end,
    print_step,
    print_info,
    print_success,
    print_error,
    print_param_table,
    run_cmd,
    print_file_regex,
)

app = typer.Typer()


class RunType(str, Enum):
    run_cli = "run_cli"
    gui = "gui"
    show_goals = "show_goals"


# ==========================================================
# RECIPE
# ==========================================================


@app.command()
def spyglass_run(
    target: str = typer.Option(
        ...,
        "--target",
        "-t",
        help="CVA6 user configuration",
        autocompletion=autocompletion_target,
    ),
    run_type: RunType = typer.Option(RunType.run_cli, help="Run mode"),
    quiet: bool = typer.Option(
        False, "--quiet", "-q", help="Suppress output (errors only)"
    ),
):
    """
    Spyglass run
    """
    print_recipe_title("Spyglass run", quiet=quiet)

    # Get testbench config
    repo_dir = Path.cwd()
    testbench_cfg = None
    with (repo_dir / "config" / "target" / target / "testbench_cfg.yml").open(
        "r", encoding="utf-8"
    ) as f:
        testbench_cfg = yaml.safe_load(f)
    cva6_hier = Cva6Hier(testbench_cfg["hier"])

    print_param_table(
        {"Target": target, "Testbench hier": cva6_hier.value, "Run": run_type.value},
        "Options",
        quiet=quiet,
    )

    # Test tools in path
    aipk_run_path = shutil.which("aipk_run")
    if aipk_run_path is not None:
        print_success(f"aipk_run: {aipk_run_path}", quiet=quiet)
    else:
        print_error("aipk_run: Not found", quiet=quiet)
        raise typer.Exit(code=1)

    # Testbench selection
    if cva6_hier == Cva6Hier.obi:
        top_elaborate = "cva6_example_obi"
    elif cva6_hier == Cva6Hier.axi:
        top_elaborate = "cva6_example_axi"
    else:
        print_error("Unknown cva6_hier", quiet=quiet)
        raise typer.Exit(code=1)

    # Create files and folder paths
    build_root = repo_dir / "build" / target
    spyglass_dir = build_root / "spyglass"
    sg_setup_dir = spyglass_dir / "sg_setup" / f"{top_elaborate}"
    tmp_dir = spyglass_dir / "tmp"

    if sg_setup_dir.exists():
        print_info(f"sg_setup found: {spyglass_dir}", quiet=quiet)
    else:
        print_error(f"sg_setup not found: {spyglass_dir}", quiet=quiet)
        print_error("Run design read first", quiet=quiet)
        raise typer.Exit(code=1)

    # ==========================================================
    # CLEAN
    # ==========================================================
    print_step("Clean", quiet=quiet)
    print_info("None", quiet=quiet)

    # ==========================================================
    # ENV VARIABLES (passed to run_cmd only)
    # ==========================================================

    env_vars = {
        "CVA6_REPO_DIR": str(repo_dir),
        "TARGET_CFG": target,
        "HPDCACHE_DIR": str(repo_dir / "core/cache_subsystem/hpdcache"),
        "HPDCACHE_TARGET_CFG": str(
            repo_dir / "core/include/cva6_hpdcache_default_config_pkg.sv"
        ),
        "SPYGLASS_TMPDIR": str(tmp_dir),
    }

    # ==========================================================
    # BUILD SPYGLASS DESIGN READ COMMAND
    # ==========================================================
    sg_cmd = ["aipk_run"]
    sg_cmd += [f"-top={top_elaborate}"]

    if run_type == "run_cli":
        sg_cmd += ["-goals=lint_rtl"]
    elif run_type == "gui":
        sg_cmd += ["-gui"]
    elif run_type == "show_goals":
        sg_cmd += ["-showgoals"]

    # ==========================================================
    # LAUNCH SPYGLASS DESIGN READ COMMAND
    # ==========================================================
    print_step("LAUNCH SPYGLASS DESIGN READ", quiet=quiet)

    log_file = spyglass_dir / "run.log"

    run_cmd(
        cmd=sg_cmd,
        cwd=spyglass_dir,
        env=env_vars,
        error_patterns=["error:|^AIPK_ERROR :|^ERROR:"],
        warning_patterns=["warning:|^AIPK_WARNING :|^WARNING:"],
        highlight_patterns=["info:|Messages:|Total Messages|^AIPK_INFO :|^INFO:"],
        log_file=log_file,
        timeout=1800,
        check=False,
        capture_output=True,
        quiet=quiet,
    )

    # ==========================================================
    # Results processing
    # ==========================================================

    print_step("Results processing", quiet=quiet)

    print_file_regex(
        spyglass_dir
        / "sg_run_results"
        / f"{top_elaborate}"
        / f"{top_elaborate}"
        / "lint"
        / "lint_rtl"
        / "spyglass_reports"
        / "moresimple.rpt",
        None,
        None,
        ["Error|Fatal|Warning"],
        quiet=quiet,
    )

    # ==========================================================
    # List
    # ==========================================================
    print_step("Generated files", quiet=quiet)
    gen_files = [
        log_file,
        spyglass_dir
        / "sg_run_results"
        / f"{top_elaborate}"
        / f"{top_elaborate}"
        / "lint"
        / "design_audit"
        / "spyglass.log",
        spyglass_dir
        / "sg_run_results"
        / f"{top_elaborate}"
        / f"{top_elaborate}"
        / "lint"
        / "design_audit"
        / "spyglass_reports",
        spyglass_dir
        / "sg_run_results"
        / f"{top_elaborate}"
        / f"{top_elaborate}"
        / "cdc"
        / "cdc_setup_check"
        / "spyglass.log",
        spyglass_dir
        / "sg_run_results"
        / f"{top_elaborate}"
        / f"{top_elaborate}"
        / "cdc"
        / "cdc_setup_check"
        / "spyglass_reports",
        spyglass_dir
        / "sg_run_results"
        / f"{top_elaborate}_sg_reports"
        / "html_reports"
        / "goals_summary.html",
    ]

    for genfile in gen_files:
        if genfile.exists():
            print_info(f"> {genfile}", quiet=quiet)

    print_recipe_end("Completed", quiet=quiet)
