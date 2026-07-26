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
from flows.utils.utils import (
    autocompletion_target,
    print_recipe_title,
    print_recipe_end,
    print_step,
    print_error,
    print_success,
    print_info,
    run_cmd,
)

app = typer.Typer()


@app.command()
def verible_rtl_formating(
    target: str = typer.Option(
        ...,
        "--target",
        "-t",
        help="CVA6 user configuration",
        autocompletion=autocompletion_target,
    ),
    quiet: bool = typer.Option(
        False, "--quiet", "-q", help="Suppress output (errors only)"
    ),
):
    """
    Format CVA6 RTL files with Verible (mandatory for submit PR)
    """

    # Title
    print_recipe_title("Verible RTL formating", quiet=quiet)

    repo_dir = Path.cwd()

    verible_path = shutil.which("verible-verilog-format")
    if verible_path is not None:
        print_success(f"verible-verilog-format: {verible_path}", quiet=quiet)
    else:
        print_error("verible-verilog-format: Not found", quiet=quiet)
        raise typer.Exit(code=1)

    verible_dir = repo_dir / "build" / target / "verible"

    # ==========================================================
    # CLEAN
    # ==========================================================
    print_step("Clean", quiet=quiet)
    try:
        if verible_dir.exists():
            shutil.rmtree(verible_dir)
            print_info(f"remove {verible_dir}", quiet=quiet)
    except Exception as e:
        print_error(f"Clean error : {e}", quiet=quiet)
        raise typer.Exit(code=1)

    verible_dir.mkdir(parents=True, exist_ok=True)
    print_info(f"create {verible_dir}", quiet=quiet)

    # ==========================================================
    # GET FILE LIST TO FORMAT
    # ==========================================================

    def parse_flist(flist_path, patterns, collected=None):

        if collected is None:
            collected = []

        flist_path = Path(flist_path)
        if not flist_path.exists():
            raise FileNotFoundError(f"Flist not found: {flist_path}")

        with flist_path.open("r", encoding="utf-8") as f:
            text = f.read()
            # Expand environement variables to be able to follow include Flist
            for search, replace in patterns:
                text = text.replace(search, replace)
            lines = text.splitlines()

        for line in lines:
            l = line.strip()
            # Skip empty/comments/+incdir
            if not l or l.startswith("//") or l.startswith("+incdir+"):
                continue

            # Recursive include -F
            if l.startswith("-F"):
                flist_incl = l[2:].strip()
                parse_flist(flist_incl, patterns, collected)
                continue

            collected.append(l)

        return collected

    flist_envvar = [
        ("${TARGET_CFG}", target),
        ("${CVA6_REPO_DIR}", str(repo_dir)),
        ("${HPDCACHE_DIR}", str(repo_dir / "core" / "cache_subsystem" / "hpdcache")),
    ]

    analyse_files = parse_flist(
        repo_dir / "config" / "target" / target / "Flist.cva6", flist_envvar
    )

    # ==========================================================
    # BUILD VERIBLE COMMAND
    # ==========================================================

    verible_cmd = ["verible-verilog-format", "--inplace"]
    verible_cmd += analyse_files

    # ==========================================================
    # LAUNCH VERIBLE
    # ==========================================================
    print_step("Launch Verible", quiet=quiet)

    log_file = verible_dir / "verible-cmd.log"

    run_cmd(
        cmd=verible_cmd,
        cwd=None,
        env=None,
        error_patterns=None,
        warning_patterns=None,
        highlight_patterns=None,
        log_file=log_file,
        timeout=300,
        check=False,
        capture_output=False,
        quiet=quiet,
    )

    # ==========================================================
    # List
    # ==========================================================

    gen_files = [log_file]

    print_step("Generated files", quiet=quiet)
    for genfile in gen_files:
        if genfile.exists():
            print_info(f"> {genfile}", quiet=quiet)

    print_recipe_end("Completed", quiet=quiet)
