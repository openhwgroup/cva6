# Copyright 2026 Thales France
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
# You may obtain a copy of the License at https://solderpad.org/licenses/
#
# Original Author: Théo GIOVINAZZI

from pathlib import Path
import shutil
import typer
from flows.utils.utils import (
    print_recipe_title,
    print_recipe_end,
    print_step,
    print_info,
    print_success,
    print_error,
    run_cmd,
)

app = typer.Typer()


# ==========================================================
# RECIPE
# ==========================================================


@app.command()
def vcs_generator_comp():
    """
    VCS UVM compilation / elaboration flow
    """
    print_recipe_title("VCS DESIGN ELABORATION")

    # Test tools in path
    vcs_path = shutil.which("vcs")
    if vcs_path is not None:
        print_success(f"VCS: {vcs_path}")
    else:
        print_error("vcs: Not found")
        raise typer.Exit(code=1)

    # Create files and folder paths
    repo_dir = Path.cwd()
    build_root = repo_dir / "build"
    elab_dir = build_root / "dv"

    # ==========================================================
    # CLEAN
    # ==========================================================
    print_step("Clean")
    try:
        if elab_dir.exists():
            shutil.rmtree(elab_dir)
            print_info(f"remove {elab_dir}")
    except Exception as e:
        print_error(f"Clean error : {e}")
        raise typer.Exit(code=1)

    elab_dir.mkdir(parents=True, exist_ok=True)
    print_info(f"create {elab_dir}")

    # ==========================================================
    # ENV VARIABLES
    # ==========================================================

    env_vars = {
        "RISCV_DV_ROOT": str(repo_dir / "verif" / "sim" / "dv"),
        "CVA6_DV_ROOT": str(repo_dir / "verif" / "env" / "corev-dv"),
    }

    # ==========================================================
    # CUSTOMIZE WITH OPTIONS
    # ==========================================================

    # FILELIST
    flist = []

    incdirs = [
        str(repo_dir / "verif" / "env" / "corev-dv" / "target" / "cv32a65x"),
        str(repo_dir / "verif" / " sim" / "dv" / "user_extension"),
    ]

    flist += [
        str(repo_dir / "verif" / "sim" / "dv" / "cva6-files.f"),
    ]
    # DEFINES
    defines = [
        "UVM",
        "HPDCACHE_ASSERT_OFF=1",
    ]

    # VCS OPTIONS
    options = [
        "-lca",
        "-sverilog",
        "-ntb_opts",
        "uvm-1.2",
        "-timescale=1ns/1ps",
        "-assert",
        "svaext",
        "-full64",
        "-q",
    ]

    # ==========================================================
    # BUILD VCS COMMAND
    # ==========================================================

    vcs_cmd = ["vcs"]
    vcs_cmd += options

    for d in defines:
        vcs_cmd += [f"+define+{d}"]

    for f in flist:
        vcs_cmd += ["-f", str(f)]

    for d in incdirs:
        vcs_cmd += [f"+incdir+{d}"]

    vcs_cmd += [
        "-top",
        "cva6_instr_gen_tb_top",
    ]

    # ==============================================================================
    # COPY CUSTOM INSTRUCTIONS
    # ==============================================================================
    print_step("Copy custom instructions")
    try:
        src_file = (
            repo_dir
            / "verif"
            / "env"
            / "corev-dv"
            / "custom"
            / "riscv_custom_instr_enum.sv"
        )
        dest_dir = repo_dir / "verif" / "sim" / "dv" / "src" / "isa" / "custom"

        dest_dir.mkdir(parents=True, exist_ok=True)

        # cp verif/env/corev-dv/custom/riscv_custom_instr_enum.sv ./verif/sim/dv/src/isa/custom/ :
        shutil.copy2(src_file, dest_dir)
        print_info(f"copy {src_file.name} to {dest_dir}")

    except Exception as e:
        print_error(f"Copy error : {e}")
        raise typer.Exit(code=1)

    # ==========================================================
    # LAUNCH VCS COMMAND
    # ==========================================================
    print_step("LAUNCH VCS")

    log_file = elab_dir / "compilation.log"

    run_cmd(
        cmd=vcs_cmd,
        cwd=elab_dir,
        env=env_vars,
        error_patterns=["^Error-"],
        warning_patterns=["^Warning-"],
        highlight_patterns=["^../simv up to date"],
        log_file=log_file,
        timeout=1800,
        check=False,
        capture_output=True,
    )

    simv = elab_dir / "simv"

    if not simv.exists():
        print_error("SIMV not generated")
        raise typer.Exit(code=1)

    if not log_file.exists():
        print_error("Compilation log missing")

    # ==========================================================
    # List
    # ==========================================================
    print_step("Generated files")
    gen_files = [simv, log_file]

    for genfile in gen_files:
        if genfile.exists():
            print_info(f"> {genfile}")

    print_recipe_end("Completed")
