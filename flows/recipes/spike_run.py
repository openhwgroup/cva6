# Copyright 2026 Thales France
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
# You may obtain a copy of the License at https://solderpad.org/licenses/
#
# Original Author: Guillaume Chauvon

# Please refer to flows/README.md to add target

from pathlib import Path
import shutil
import typer
from flows.utils.utils import (
    autocompletion_target,
    autocompletion_testname_compiled,
    print_recipe_title,
    print_recipe_end,
    print_step,
    print_info,
    print_success,
    print_error,
    print_param_table,
    tail_file,
    run_cmd,
)

app = typer.Typer()


# ==========================================================
# RECIPE - RUN SPIKE SIMULATION
# ==========================================================


@app.command()
def spike_run(
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
    quiet: bool = typer.Option(
        False, "--quiet", "-q", help="Suppress output (errors only)"
    ),
):
    """
    VCS UVM run simulation flow
    """
    # Init code
    code = 0

    print_recipe_title("SPIKE SIMULATION", quiet=quiet)

    print_param_table(
        {
            "Target": target,
            "Test name": test_name,
        },
        "Options",
        quiet=quiet,
    )

    # Mode dir
    inout_dir = "sim_spike"

    # Create files and folder paths
    repo_dir = Path.cwd()
    build_root = repo_dir / "build" / target
    compile_dir = build_root / "compile" / test_name
    simulation_dir = build_root / "simulation" / inout_dir / test_name

    spike_dir = repo_dir / "tools" / "spike"
    spike_bin = spike_dir / "bin" / "spike"
    spike_lib = spike_dir / "lib"

    # ==========================================================
    # CLEAN
    # ==========================================================
    print_step("Clean", quiet=quiet)
    try:
        if simulation_dir.exists():
            shutil.rmtree(simulation_dir)
            print_info(f"remove {simulation_dir}", quiet=quiet)
    except Exception as e:
        print_error(f"Clean error: {e}", quiet=quiet)
        raise typer.Exit(code=1)

    simulation_dir.mkdir(parents=True, exist_ok=True)
    print_info(f"create {simulation_dir}", quiet=quiet)

    # ==========================================================
    # OPTIONS
    # ==========================================================

    env_vars = {"LD_LIBRARY_PATH": f"{spike_lib}"}

    spike_param_file = repo_dir / "config" / "target" / target / "spike.yaml"
    elf = compile_dir / f"{test_name}.elf"

    options = [
        "--steps=2000000",
        "--log-commits",
        "--param-file",
        f"{spike_param_file}",
        "-l",
        f"{elf}",
    ]

    # ==========================================================
    # BUILD SPIKE COMMAND
    # ==========================================================

    spike_cmd = [str(spike_bin)]
    spike_cmd += options

    # ==========================================================
    # LAUNCH SIMV
    # ==========================================================
    print_step("Run SPIKE simulation", quiet=quiet)

    log_file = simulation_dir / "simulation.log"

    run_cmd(
        cmd=spike_cmd,
        cwd=simulation_dir,
        env=env_vars,
        error_patterns=["(ERROR|Error|No such file or directory)"],
        warning_patterns=["(WARNING|Warning)"],
        highlight_patterns=None,
        log_file=log_file,
        timeout=3000,
        check=False,
        capture_output=False,
        quiet=quiet,
    )

    # ==========================================================
    # POST PROCESS LOGS
    # ==========================================================

    # Tail log
    tail_file(log_file, n=20, quiet=quiet)

    file_add_tohost = compile_dir / f"{test_name}.add_tohost"
    found = 0
    if file_add_tohost.exists():
        add_tohost = file_add_tohost.read_text().strip()
        try:
            with log_file.open("r") as f_in:
                lines = f_in.readlines()
            last_line = lines[-1].strip()
            last_line_words = last_line.split()
            tohost = last_line_words[-2]
            return_val = last_line_words[-1]
            if tohost[2:] == add_tohost:
                if return_val[2:] == "00000001":
                    print_success(
                        f"Spike ended with value {return_val[2:]} in tohost ({add_tohost})",
                        quiet=quiet,
                    )
                    found = 1
                else:
                    print_error(
                        f"Spike ended with value {return_val[2:]} in tohost ({add_tohost})",
                        quiet=quiet,
                    )
                    found = 1
            else:
                print_error(
                    f"Spike did not end with write in tohost ({add_tohost}): {tohost[2:]}",
                    quiet=quiet,
                )
                found = 1
        except Exception as e:
            print_error(f"Error process log: {e}", quiet=quiet)
    else:
        print_error(f"Missing {file_add_tohost}", quiet=quiet)

    if found == 0:
        print_error("Simulation status unknown", quiet=quiet)
        code = 1

    # ==========================================================
    # List
    # ==========================================================
    print_step("Generated files", quiet=quiet)
    gen_files = [
        simulation_dir / "simulation.log",
    ]

    for genfile in gen_files:
        if genfile.exists():
            print_info(f"> {genfile}", quiet=quiet)

    print_recipe_end("Completed", quiet=quiet)

    if code != 0:
        raise typer.Exit(code=1)
