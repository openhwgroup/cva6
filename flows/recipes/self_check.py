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
from flows.utils.config_loader import TECHNO_DATA, COMPILER_DATA
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
def self_check():
    """
    Self check
    """

    # Title
    print_recipe_title("Self check")

    print_step("Tools in path")

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
            print_success(f"{tool_name} ({description}): {tool_path}")
        else:
            print_error(f"{tool_name} ({description}): Not found")

    print_step("Spike installation (mandatory for tandem verification)")

    path = [
        "./tools/spike/bin",
        "./tools/spike/lib",
    ]

    for p in path:
        if Path(p).exists():
            print_success(f"{p}: exist")
        else:
            print_error(f"{p}: Not found see verif/regress/install-spike (MANDATORY)")

    # Submodules
    print_step("Submodules of CVA6 repositoy")

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
    )

    for line in result.split("\n"):
        if line.startswith("-"):
            print_error(f"{line}: Submodule not initialised")
        else:
            print_success(f"{line}: Submodule initialised")

    # riscv-tests
    print_step("riscv-tests installation")

    path = [
        "./verif/tests/riscv-tests",
    ]

    for p in path:
        if Path(p).exists():
            print_success(f"{p}: exist")
        else:
            print_error(
                f"{p}: Not found, see verif/regress/install-riscv-tests (MANDATORY)"
            )

    # riscv-compliance
    print_step("riscv-compliance installation")

    path = [
        "./verif/tests/riscv-compliance",
    ]

    for p in path:
        if Path(p).exists():
            print_success(f"{p}: exist")
        else:
            print_warning(f"{p}: Not found, see verif/regress/install-compliance")

    print_step("riscv-arch-test installation")

    # riscv-arch-test
    path = [
        "./verif/tests/riscv-arch-test",
    ]

    for p in path:
        if Path(p).exists():
            print_success(f"{p}: exist")
        else:
            print_warning(f"{p}: Not found, see verif/regress/install-arch-test")

    print_step("Specific organisation configuration files")

    # Get organisation techno config (asic)
    techno_data = TECHNO_DATA

    print_param_table(
        techno_data,
        "Techno parameters",
    )

    # Get organisation compiler config
    compiler_data = COMPILER_DATA

    print_param_table(
        compiler_data,
        "Compiler parameters",
    )

    print_recipe_end("Completed")
