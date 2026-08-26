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
import random
from enum import Enum
import yaml
import typer
from flows.recipes.vcs_uvm_run import vcs_uvm_run
from flows.recipes.xcelium_uvm_run import xcelium_uvm_run
from flows.recipes.questa_uvm_run import questa_uvm_run
from flows.utils.manifest import require_prerequisite
from flows.utils.utils import (
    CompMode,
    TraceMode,
    UvmVerbosity,
    autocompletion_target,
    autocompletion_testlist,
    autocompletion_testname_in_testlist,
    print_recipe_title,
    print_success,
    print_error,
)

app = typer.Typer()


# ==========================================================
# SIMULATOR ENUM
# ==========================================================


class Simulator(str, Enum):
    vcs = "vcs"
    xcelium = "xcelium"
    questa = "questa"


# ==========================================================
# RECIPE
# ==========================================================


@app.command()
def uvm_run_testlist(
    simulator: Simulator = typer.Option(
        ...,
        "--simulator",
        "-s",
        help="Simulator to use (vcs, xcelium, questa)",
    ),
    target: str = typer.Option(
        ...,
        "--target",
        "-t",
        help="CVA6 user configuration",
        autocompletion=autocompletion_target,
    ),
    testlist: str = typer.Option(
        None,
        "--testlist",
        "-l",
        help="Testlist (YML file) in verif/tests",
        autocompletion=autocompletion_testlist,
    ),
    test_name: list[str] = typer.Option(
        None,
        "--testname",
        "-n",
        help="Single test in the given testlist",
        autocompletion=autocompletion_testname_in_testlist,
    ),
    comp_mode: CompMode = typer.Option(CompMode.rtl, help="Hardware compilation mode"),
    trace_mode: TraceMode = typer.Option(TraceMode.notrace, help="Trace mode"),
    uvm_verbosity: UvmVerbosity = typer.Option(UvmVerbosity.none, help="UVM verbosity"),
    tandem_enabled: bool = typer.Option(False, help="Enable spike tandem"),
    tb_performance_mode: bool = typer.Option(False, help="Enable tb perf mode"),
    stats: bool = typer.Option(False, help="Enable RTL perf tracer"),
    sim_profile: bool = typer.Option(
        False, help="Enable simulation profiling (VCS only)"
    ),
    interactive_gui: bool = typer.Option(
        False, help="Launch GUI for interactive simulation"
    ),
    run_opts: list[str] = typer.Option([], "--run_opts", help="Simulation run options"),
    uvm_seed: str = typer.Option(
        str(random.getrandbits(31)), help="Randomize UVM seed"
    ),
    quiet: bool = typer.Option(
        False, "--quiet", "-q", help="Suppress output (errors only)"
    ),
):
    """
    UVM run testlist simulation flow (multi-simulator)
    """
    code = 0

    print_recipe_title(
        f"{simulator.value.upper()} DESIGN RUN SIMULATION TESTLIST", quiet=quiet
    )

    # Select the appropriate run function based on simulator
    if simulator == Simulator.vcs:
        run_function = vcs_uvm_run
    elif simulator == Simulator.xcelium:
        run_function = xcelium_uvm_run
    elif simulator == Simulator.questa:
        run_function = questa_uvm_run
    else:
        print_error(f"Unknown simulator: {simulator}", quiet=quiet)
        raise typer.Exit(code=1)

    repo_dir = Path.cwd()

    # ==========================================================
    # CHECK PREREQUISITES (fail fast before looping on testlist)
    # ==========================================================
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

    elab_dir = repo_dir / "build" / target / "elab" / inout_dir
    elab_artifact = {
        Simulator.vcs: elab_dir / "simv",
        Simulator.xcelium: elab_dir / "xcelium.d",
        Simulator.questa: elab_dir / "work",
    }[simulator]
    require_prerequisite(
        elab_artifact,
        f"{simulator.value} elaborated design (comp mode '{comp_mode.value}')",
        f"./cook.py {simulator.value}-uvm-comp -t {target} --comp-mode {comp_mode.value}",
    )

    data = {"testlist": []}

    # Special handling for cvxif testlist
    if testlist and "cvxif" in testlist:
        run_opts = list(run_opts) + ["+enabled_cvxif"]
        print("Detected cvxif testlist, adding run option: +enabled_cvxif")

    if testlist:
        testlist_file = repo_dir / testlist
        try:
            with testlist_file.open("r") as f:
                data = yaml.safe_load(f)
        except FileNotFoundError as e:
            print_error(f"testlist: File not found: {testlist_file}", quiet=quiet)
            raise typer.Exit(code=1) from e

        if "testlist" in data:
            print_success(f"testlist: Found in file {testlist}", quiet=quiet)
        else:
            print_error(f"testlist: Not found in file {testlist}", quiet=quiet)
            raise typer.Exit(code=1)
    elif test_name:
        data["testlist"] = [{"test": name, "iterations": 1} for name in test_name]
    else:
        print_error("Error: You must provide --testlist or --testname", quiet=quiet)
        raise typer.Exit(code=1)

    # Run tests
    for test in data["testlist"]:
        # Single test mode - skip tests not in test_name list
        if testlist and test_name:
            if test["test"] not in test_name:
                continue

        iterations = test.get("iterations", 1)
        # Skip disabled tests (iterations == 0)
        if iterations == 0:
            continue

        for i in range(iterations):
            iter_test_name = f"{test['test']}_{i}"
            try:
                # Call the appropriate simulator run function
                # Note: sim_profile only supported by VCS
                if simulator == Simulator.vcs:
                    run_function(
                        target=target,
                        test_name=iter_test_name,
                        comp_mode=comp_mode,
                        trace_mode=trace_mode,
                        uvm_verbosity=uvm_verbosity,
                        tandem_enabled=tandem_enabled,
                        tb_performance_mode=tb_performance_mode,
                        interactive_gui=interactive_gui,
                        stats=stats,
                        sim_profile=sim_profile,
                        run_opts=run_opts,
                        uvm_seed=uvm_seed,
                        quiet=quiet,
                    )
                else:
                    # Xcelium and Questa don't have sim_profile
                    run_function(
                        target=target,
                        test_name=iter_test_name,
                        comp_mode=comp_mode,
                        trace_mode=trace_mode,
                        uvm_verbosity=uvm_verbosity,
                        tandem_enabled=tandem_enabled,
                        tb_performance_mode=tb_performance_mode,
                        interactive_gui=interactive_gui,
                        stats=stats,
                        run_opts=run_opts,
                        uvm_seed=uvm_seed,
                        quiet=quiet,
                    )
            except typer.Exit:
                print_error(f"{test['test']}: Returned error", quiet=quiet)
                code = 1

    if code != 0:
        raise typer.Exit(code=1)
