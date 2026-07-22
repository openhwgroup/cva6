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
import yaml
import typer
from flows.recipes.vcs_uvm_run import vcs_uvm_run
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
# RECIPE
# ==========================================================


@app.command()
def vcs_uvm_run_testlist(
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
    sim_profile: bool = typer.Option(False, help="Enable simulation profiling"),
    interactive_gui: bool = typer.Option(
        False, help="Launch VERDI for interactive simulation"
    ),
    run_opts: list[str] = typer.Option([], "--run_opts", help="Simulation run options"),
    uvm_seed: str = typer.Option(
        str(random.getrandbits(31)), help="Randomize UVM seed"
    ),
):
    """
    VCS UVM run testlist simulation flow
    """
    code = 0

    print_recipe_title("VCS DESIGN RUN SIMULATION TESTLIST")

    repo_dir = Path.cwd()
    data = {"testlist": []}
    if "cvxif" in testlist:
        run_opts = ["+enabled_cvxif"]
    print(run_opts)

    if testlist:
        testlist_file = repo_dir / testlist
        try:
            with testlist_file.open("r") as f:
                data = yaml.safe_load(f)
        except FileNotFoundError as e:
            print_error(f"testlist: File Not found in file {testlist_file}")
            raise typer.Exit(code=1) from e

        if "testlist" in data:
            print_success(f"testlist: Found in file {testlist}")
        else:
            print_error(f"testlist: Not found in file {testlist}")
            raise typer.Exit(code=1)
    elif test_name:
        data["testlist"] = [{"test": name, "iterations": 1} for name in test_name]
    else:
        print_error("Error: You must provide --testlist or --testname")
        raise typer.Exit(code=1)

    for test in data["testlist"]:
        # Single test mode
        if testlist and test_name:
            if test["test"] not in test_name:
                continue

        iterations = test.get("iterations", 1)
        # Skip disables tests
        if iterations == 0:
            continue
        for i in range(iterations):
            iter_test_name = f"{test['test']}_{i}"
            try:
                vcs_uvm_run(
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
                )
            except typer.Exit:
                print_error(f"{test['test']}: Return Error")
                code = 1

    if code != 0:
        raise typer.Exit(code=1)
