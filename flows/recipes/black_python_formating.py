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
def black_python_formating():
    """
    Format Python files with black
    """
    print_recipe_title("Black Python formating")
    print_step("Launch Black")
    dir_list = [".gitlab-ci", "docs/scripts", "flows", "pd", "perf-model"]
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
    py_files = ["cook.py"]
    for f in files.split():
        if f.endswith(".py"):
            py_files.append(f)
    black_cmd = ["black", "--diff", "--check"]
    black_cmd += py_files
    run_cmd(
        cmd=black_cmd,
        cwd=None,
        env=None,
        error_patterns=None,
        warning_patterns=None,
        highlight_patterns=[".*"],
        log_file=None,
        timeout=300,
        check=True,
        capture_output=False,
    )

    print_recipe_end("Completed")
