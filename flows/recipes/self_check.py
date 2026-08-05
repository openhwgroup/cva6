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
from flows.utils.config_loader import load_techno_config, load_compiler_config
from flows.utils.utils import (
    print_recipe_title,
    print_recipe_end,
    print_success,
    print_warning,
    print_error,
    print_param_table,
    print_step,
    run_cmd,
)

app = typer.Typer()


# ==========================================================
# RECIPE - Self check
# ==========================================================


@app.command()
def self_check(
    quiet: bool = typer.Option(
        False, "--quiet", "-q", help="Suppress output (errors only)"
    ),
):
    """
    Self check
    """

    TECHNO_DATA = load_techno_config()
    COMPILER_DATA = load_compiler_config()

    # Title
    print_recipe_title("Self check", quiet=quiet)

    print_step("Tools in path", quiet=quiet)

    tools = [
        ("vcs", "VCS - Synopsys simulator"),
        ("verdi", "Verdi - Synopsys debug"),
        ("xrun", "Xcelium - Cadence simulator"),
        ("vsim", "Questa/ModelSim - Siemens simulator"),
        ("vlog", "Questa/ModelSim - Verilog compiler"),
        ("vopt", "Questa/ModelSim - Optimizer"),
        ("dc_shell", "Design Compiler - Synopsys synthesis"),
        ("pt_shell", "PrimeTime - Synopsys STA"),
        ("aipk_read", "Spyglass - Synopsys static analysis"),
        ("aipk_run", "Spyglass - Synopsys static analysis"),
        ("verible-verilog-format", "Verible - RTL formatter"),
        ("black", "Black - Python formatter"),
        ("pylint", "Pylint - Python linter"),
    ]

    for tool_name, description in tools:
        tool_path = shutil.which(tool_name)
        if tool_path is not None:
            print_success(f"{tool_name} ({description}): {tool_path}", quiet=quiet)
        else:
            print_error(f"{tool_name} ({description}): Not found", quiet=quiet)

    print_step("Spike installation (mandatory for tandem verification)", quiet=quiet)

    path = [
        "./tools/spike/bin",
        "./tools/spike/lib",
    ]

    for p in path:
        if Path(p).exists():
            print_success(f"{p}: exist", quiet=quiet)
        else:
            print_error(
                f"{p}: Not found see verif/regress/install-spike (MANDATORY)",
                quiet=quiet,
            )

    # Submodules
    print_step("Submodules of CVA6 repositoy", quiet=quiet)

    result = run_cmd(
        cmd=["git", "submodule", "status", "--recursive"],
        cwd=None,
        env=None,
        error_patterns=None,
        warning_patterns=None,
        highlight_patterns=None,
        log_file=None,
        timeout=90,
        check=False,
        capture_output=True,
        quiet=quiet,
    )

    for line in result.split("\n"):
        if line.startswith("-"):
            print_error(f"{line}: Submodule not initialised", quiet=quiet)
        else:
            print_success(f"{line}: Submodule initialised", quiet=quiet)

    # riscv-tests
    print_step("riscv-tests installation", quiet=quiet)

    path = [
        "./verif/tests/riscv-tests",
    ]

    for p in path:
        if Path(p).exists():
            print_success(f"{p}: exist", quiet=quiet)
        else:
            print_error(
                f"{p}: Not found, see verif/regress/install-riscv-tests (MANDATORY)",
                quiet=quiet,
            )

    # riscv-compliance
    print_step("riscv-compliance installation", quiet=quiet)

    path = [
        "./verif/tests/riscv-compliance",
    ]

    for p in path:
        if Path(p).exists():
            print_success(f"{p}: exist", quiet=quiet)
        else:
            print_warning(
                f"{p}: Not found, see verif/regress/install-compliance", quiet=quiet
            )

    print_step("riscv-arch-test installation", quiet=quiet)

    # riscv-arch-test
    path = [
        "./verif/tests/riscv-arch-test",
    ]

    for p in path:
        if Path(p).exists():
            print_success(f"{p}: exist", quiet=quiet)
        else:
            print_warning(
                f"{p}: Not found, see verif/regress/install-arch-test", quiet=quiet
            )

    print_step("Specific organisation configuration files", quiet=quiet)

    # Get organisation techno config (asic)
    techno_data = TECHNO_DATA

    print_param_table(
        techno_data,
        "Techno parameters",
        quiet=quiet,
    )

    # Get organisation compiler config
    compiler_data = COMPILER_DATA

    print_param_table(
        compiler_data,
        "Compiler parameters",
        quiet=quiet,
    )

    print_recipe_end("Completed", quiet=quiet)
