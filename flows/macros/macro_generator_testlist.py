# Copyright 2026 Thales France
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
# You may obtain a copy of the License at https://solderpad.org/licenses/
#
# Original Author: Théo GIOVINAZZI

import random
import typer

from flows.recipes.sw_compile_testlist import sw_compile_testlist
from flows.recipes.vcs_generator_run_testlist import vcs_generator_run_testlist
from flows.recipes.uvm_run_testlist import uvm_run_testlist
from flows.utils.utils import (
    CompMode,
    ToolchainOption,
    TraceMode,
    UvmVerbosity,
    autocompletion_target,
    autocompletion_testlist,
    print_error,
    print_recipe_title,
    print_success,
    print_step,
)

app = typer.Typer()


# ==========================================================
# RECIPE
# ==========================================================


@app.command()
def macro_vcs_generator_testlist(
    # --- Arguments for generator ---
    target: str = typer.Option(
        ...,
        "--target",
        "-t",
        help="CVA6 user configuration",
        autocompletion=autocompletion_target,
    ),
    testlist: str = typer.Option(
        ...,
        "--testlist",
        "-l",
        help="Testlist (YML file) in verif/tests",
        autocompletion=autocompletion_testlist,
    ),
    test_name: list[str] = typer.Option(
        None, "--testname", "-n", help="Single test in the given testlist"
    ),
    # --- Arguments for compilation ---
    toolchain: ToolchainOption = typer.Option(
        ...,
        "--toolchain",
        "-c",
        help="Toolchain defined in $CONFIG_DIR/compiler.yml",
    ),
    march: str = typer.Option(
        None, help="march custom instead of default one from config/target"
    ),
    mabi: str = typer.Option(
        None, help="mabi custom instead of default one from config/target"
    ),
    # --- Arguments for simulation UVM ---
    comp_mode: CompMode = typer.Option(CompMode.rtl, help="Hardware compilation mode"),
    trace_mode: TraceMode = typer.Option(TraceMode.notrace, help="Trace mode"),
    uvm_verbosity: UvmVerbosity = typer.Option(UvmVerbosity.none, help="UVM verbosity"),
    tandem_enabled: bool = typer.Option(False, help="Enable spike tandem"),
    tb_performance_mode: bool = typer.Option(False, help="Enable tb perf mode"),
    stats: bool = typer.Option(False, help="Enable RTL perf tracer"),
    sim_profile: bool = typer.Option(False, help="Enable simulation profiling"),
    run_opts: list[str] = typer.Option([], "--run_opts", help="Simulation run options"),
    batch_size: int = typer.Option(1, help="Number of tests to generate per run batch"),
    seed: int = typer.Option(None, help="randomized if not provided"),
    uvm_seed: str = typer.Option(
        str(random.getrandbits(31)), help="Randomize UVM seed"
    ),
    quiet: bool = typer.Option(
        False, "--quiet", "-q", help="Suppress output (errors only)"
    ),
):
    """
    Macro : VCS Generator -> SW Compile -> UVM Run from a testlist
    """
    print_recipe_title("MACRO: VCS GENERATOR -> COMPILATION -> SIMULATION", quiet=quiet)

    # ==========================================
    # STEP 1 : GENERATOR
    # ==========================================
    try:
        print_step("\n=== STEP 1: RUN GENERATOR ===", quiet=quiet)
        vcs_generator_run_testlist(
            testlist=testlist,
            test_name=test_name,
            seed=seed,
            batch_size=batch_size,
            quiet=quiet,
        )
    except typer.Exit as e:
        print_error("Macro Error: Run Generator", quiet=quiet)
        raise e

    # ==========================================
    # STEP 2 : SOFTWARE COMPILE
    # ==========================================

    try:
        print_step("\n=== STEP 2: SW COMPILE ===", quiet=quiet)
        sw_compile_testlist(
            target=target,
            toolchain=toolchain,
            testlist=testlist,
            test_name=test_name,
            march=march,
            mabi=mabi,
            quiet=quiet,
        )
    except typer.Exit as e:
        print_error("Macro Error: Sw Compile", quiet=quiet)
        raise e

    # ==========================================
    # STEP 3 : UVM SIMULATION RUN
    # ==========================================
    try:
        print_step("\n=== STEP 3: UVM RUN ===", quiet=quiet)
        uvm_run_testlist(
            simulator="vcs",
            target=target,
            testlist=testlist,
            test_name=test_name,
            comp_mode=comp_mode,
            trace_mode=trace_mode,
            uvm_verbosity=uvm_verbosity,
            tandem_enabled=tandem_enabled,
            tb_performance_mode=tb_performance_mode,
            stats=stats,
            sim_profile=sim_profile,
            run_opts=run_opts,
            uvm_seed=uvm_seed,
            quiet=quiet,
        )
    except typer.Exit as e:
        print_error("Macro Error: UVM run", quiet=quiet)
        raise e

    print_success("\nSuccess Macro", quiet=quiet)
