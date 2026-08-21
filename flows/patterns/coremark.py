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
def coremark(
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
    Build COREMARK pattern.
    """
    repo_dir = Path.cwd()

    src_files = [
        str(repo_dir / "verif" / "tests" / "custom" / "coremark" / "coremark_main.c"),
        str(repo_dir / "verif" / "tests" / "custom" / "coremark" / "uart.c"),
        str(repo_dir / "verif" / "tests" / "custom" / "coremark" / "core_list_join.c"),
        str(repo_dir / "verif" / "tests" / "custom" / "coremark" / "core_matrix.c"),
        str(repo_dir / "verif" / "tests" / "custom" / "coremark" / "core_portme.c"),
        str(repo_dir / "verif" / "tests" / "custom" / "coremark" / "core_state.c"),
        str(repo_dir / "verif" / "tests" / "custom" / "coremark" / "core_util.c"),
        str(repo_dir / "verif" / "tests" / "custom" / "common" / "syscalls.c"),
        str(repo_dir / "verif" / "tests" / "custom" / "common" / "crt.S"),
    ]

    inc_dirs = [
        str(repo_dir / "verif" / "tests" / "custom" / "env"),
        str(repo_dir / "verif" / "tests" / "custom" / "common"),
    ]

    linker_file = str(repo_dir / "config" / "target" / target / "link.ld")

    options = [
        "O3",
        "g",
        "static",
        "mcmodel=medany",
        "fvisibility=hidden",
        "nostartfiles",
        "funroll-all-loops",
        "ffunction-sections",
        "fdata-sections",
        "Wl,-gc-sections",
        "falign-functions=16",
        "Wno-implicit-function-declaration",
        "Wno-implicit-int",
        "fno-tree-loop-distribute-patterns"
    ]

    preprocessor_directives = [
        "_LITTLE_ENDIAN_",
        "NOPRINT",
        "HAS_PRINTF=0",
        "ITERATIONS=1",
        "PERFORMANCE_RUN",
        "SKIP_TIME_CHECK",
    ]

    test_name = "coremark"

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
