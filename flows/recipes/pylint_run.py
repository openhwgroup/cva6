# Copyright 2026 Thales France
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
# You may obtain a copy of the License at https://solderpad.org/licenses/
#
# Original Author: André Sintzoff (andre.sintzoff@thalesgroup.com)

# Please refer to flows/README.md to add target

import typer
from flows.utils.utils import (
    print_recipe_title,
    print_recipe_end,
    print_step,
    run_cmd,
)

app = typer.Typer()


@app.command()
def pylint_run():
    """
    Pylint static code analyzer
    """
    print_recipe_title("Pylint")
    print_step("Launch Pylint")
    dir_list = [".gitlab-ci", "flows"]
    get_files_cmd = [
        "git",
        "ls-tree",
        "-r",
        "HEAD",
        "--name-only",
    ] + dir_list
    files = run_cmd(
        cmd=get_files_cmd,
        cwd=None,
        env=None,
        error_patterns=None,
        warning_patterns=None,
        highlight_patterns=[".*"],
        log_file=None,
        timeout=300,
        check=False,
        capture_output=True,
    )
    pylint_options = [
        "-d=duplicate-code",
        "-d=fixme",
        "-d=broad-exception-caught",
        "-d=broad-exception-raised",
        "-d=invalid-name",
        "-d=missing-module-docstring",
        "-d=missing-class-docstring",
        "-d=missing-function-docstring",
        "-d=line-too-long",
        "-d=too-few-public-methods",
        "-d=too-many-branches",
        "-d=too-many-arguments",
        "-d=too-many-locals",
        "-d=too-many-statements",
        "-d=too-many-positional-arguments",
        "-d=too-many-nested-blocks",
        "-d=consider-using-with",
        "-d=c-extension-no-member",
    ]
    pylint_cmd = ["pylint"] + pylint_options
    py_files = ["cook.py"]
    for f in files.split():
        if f.endswith(".py"):
            py_files.append(f)
    pylint_cmd += py_files
    result = run_cmd(
        cmd=pylint_cmd,
        cwd=None,
        env=None,
        error_patterns=None,
        warning_patterns=None,
        highlight_patterns=[".*"],
        log_file=None,
        timeout=300,
        check=False,
        capture_output=True,
    )
    if (
        "************* Module" in result
        or "Your code has been rated at 10.00/10" not in result
    ):
        raise typer.Exit("Pylint failed")

    print_recipe_end("Completed")
