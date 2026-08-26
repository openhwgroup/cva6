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
import typer
from flows.utils.manifest import (
    read_manifest,
    require_prerequisite,
    require_manifest_option,
)
from flows.utils.utils import (
    CompMode,
    TraceMode,
    autocompletion_target,
    autocompletion_testname_compiled,
    print_recipe_title,
    print_recipe_end,
    print_step,
    print_success,
    print_error,
    print_param_table,
    run_cmd,
)

app = typer.Typer()


# ==========================================================
# RECIPE
# ==========================================================


@app.command()
def vcs_uvm_gui(
    target: str = typer.Option(
        ...,
        "--target",
        "-t",
        help="CVA6 user configuration",
        autocompletion=autocompletion_target,
    ),
    test_name: str = typer.Option(
        None,
        "--testname",
        "-n",
        help="Test name (compiled from list or not)",
        autocompletion=autocompletion_testname_compiled,
    ),
    comp_mode: CompMode = typer.Option(CompMode.rtl, help="Hardware compilation mode"),
    session: str = typer.Option(
        None,
        "--session",
        "-s",
        help="Verdi session file(saved by user)",
    ),
    quiet: bool = typer.Option(
        False, "--quiet", "-q", help="Suppress output (errors only)"
    ),
):
    """
    Verdi open simulation trace (fsdb only)
    """

    # Title
    print_recipe_title("VCS Simulation open trace", quiet=quiet)

    print_param_table(
        {"Target": target, "Test name": test_name, "Compilation mode": comp_mode.value},
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

    # Test tools in path
    verdi_path = shutil.which("verdi")
    if verdi_path is not None:
        print_success(f"verdi: {verdi_path}", quiet=quiet)
    else:
        print_error("VERDI: Not found", quiet=quiet)
        raise typer.Exit(code=1)

    # Create files and folder paths
    repo_dir = Path.cwd()
    build_root = repo_dir / "build" / target
    elab_dir = build_root / "elab" / inout_dir
    simulation_dir = build_root / "simulation" / inout_dir / test_name

    # ==========================================================
    # CHECK PREREQUISITES
    # ==========================================================
    print_step("Check prerequisites", quiet=quiet)

    require_prerequisite(
        simulation_dir / "trace.fsdb",
        f"FSDB trace for test '{test_name}' (comp mode '{comp_mode.value}')",
        f"./cook.py vcs-uvm-run -t {target} -n {test_name} --comp-mode {comp_mode.value} --trace-mode gui (design must be elaborated with --trace-mode gui too)",
    )

    sim_manifest = read_manifest(simulation_dir)
    require_manifest_option(
        sim_manifest,
        "trace_mode",
        [TraceMode.gui.value, TraceMode.fast.value],
        "Verdi needs an FSDB trace generated with --trace-mode gui or fast",
        f"./cook.py vcs-uvm-run -t {target} -n {test_name} --comp-mode {comp_mode.value} --trace-mode gui",
        manifest_dir=simulation_dir,
    )

    print_success("Prerequisites OK", quiet=quiet)

    # ==========================================================
    # BUILD VERDI COMMAND
    # ==========================================================
    print_step("Build verdi command", quiet=quiet)

    verdi_cmd = ["verdi"]
    verdi_cmd += ["-ssf", f"{simulation_dir / 'trace.fsdb'}"]
    verdi_cmd += ["-dbdir", f"{elab_dir / 'simv.daidir'}"]

    # ==========================================================
    # ADDITIONAL VERDI COMMAND ARGS: RESTORE SESSION
    # ==========================================================
    if session is not None:
        session_file = Path(session)
        if session_file.exists():
            print_step(
                "Saved session found, session restoring configuration", quiet=quiet
            )
            verdiRestoreTCL = Path("flows/utils/verdiRestore.tcl")
            verdi_cmd += ["-play", f"{verdiRestoreTCL}"]
            with verdiRestoreTCL.open("w", encoding="utf-8") as f:
                f.write(f"set session_file {session_file}\n")
                f.write("debRestoreSession $session_file\n")
        else:
            print_step("Session file is none, skipping session restoring", quiet=quiet)

    # ==========================================================
    # LAUNCH VERDI
    # ==========================================================
    print_step("Launch Verdi", quiet=quiet)

    log_file = simulation_dir / "verdi.log"

    run_cmd(
        cmd=verdi_cmd,
        cwd=None,
        env=None,
        error_patterns=None,
        warning_patterns=None,
        highlight_patterns=None,
        log_file=log_file,
        timeout=3600,
        check=False,
        capture_output=False,
        quiet=quiet,
    )

    print_recipe_end("Completed", quiet=quiet)
