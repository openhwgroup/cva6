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
import typer
from flows.recipes.sw_compile import sw_compile
from flows.utils.utils import ToolchainOption, autocompletion_target

app = typer.Typer()


@app.command()
def hello_world(
    target: str = typer.Option(
        ...,
        "--target",
        "-t",
        help="CVA6 user configuration",
        autocompletion=autocompletion_target,
    ),
    toolchain: ToolchainOption = typer.Option(
        ..., "--toolchain", "-c", help="Toolchain defined in $CONFIG_DIR/compiler.yml"
    ),
    march: str = typer.Option(
        None, help="march custom instead of default one from config/target"
    ),
    mabi: str = typer.Option(
        None, help="mabi custom instead of default one from config/target"
    ),
    quiet: bool = typer.Option(
        False, "--quiet", "-q", help="Suppress output (errors only)"
    ),
):
    """
    Build Hello world pattern.
    """
    repo_dir = Path.cwd()

    src_files = [
        str(repo_dir / "verif" / "tests" / "custom" / "hello_world" / "hello_world.c"),
        str(repo_dir / "verif" / "tests" / "custom" / "common" / "syscalls.c"),
        str(repo_dir / "verif" / "tests" / "custom" / "common" / "crt.S"),
    ]

    inc_dirs = [
        str(repo_dir / "verif" / "sim" / "user_extension"),
        str(repo_dir / "verif" / "tests" / "custom" / "env"),
        str(repo_dir / "verif" / "tests" / "custom" / "common"),
    ]

    linker_file = str(repo_dir / "config" / "target" / target / "link.ld")

    options = [
        "g",
        "mcmodel=medany",
        "static",
        "fvisibility=hidden",
        "nostartfiles",
    ]

    preprocessor_directives = []

    test_name = "hello-world"

    sw_compile(
        target=target,
        toolchain=toolchain,
        src_files=src_files,
        inc_dirs=inc_dirs,
        linker_file=linker_file,
        options=options,
        march=march,
        mabi=mabi,
        preprocessor_directives=preprocessor_directives,
        test_name=test_name,
        quiet=quiet,
    )
