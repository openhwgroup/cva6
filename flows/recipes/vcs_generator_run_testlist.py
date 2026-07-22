# Copyright 2026 Thales France
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
# You may obtain a copy of the License at https://solderpad.org/licenses/
#
# Original Author: Théo GIOVINAZZI

import shlex
from pathlib import Path

import typer
import yaml

from flows.recipes.vcs_generator_run import vcs_generator_run
from flows.utils.utils import (
    autocompletion_testlist,
    print_error,
    print_recipe_title,
    print_success,
)

app = typer.Typer()


# ==========================================================
# RECIPE
# ==========================================================


@app.command()
def vcs_generator_run_testlist(
    testlist: str = typer.Option(
        ...,
        "--testlist",
        "-l",
        help="Testlist (YML file) in verif/tests",
        autocompletion=autocompletion_testlist,
    ),
    test_name: list[str] = typer.Option(
        None,
        "--testname",
        "-n",
        help="Single test in the given testlist",
    ),
    seed: int = typer.Option(None, help="randomized if not provided"),
    batch_size: int = typer.Option(1, help="Number of tests to generate per run batch"),
):
    """
    VCS UVM generator run testlist simulation flow
    """
    code = 0

    print_recipe_title("VCS DESIGN RUN GENERATOR TESTLIST")

    repo_dir = Path.cwd()
    data = {"testlist": []}

    testlist_file = repo_dir / testlist

    try:
        with testlist_file.open("r") as f:
            raw = yaml.safe_load(f)
            if isinstance(raw, list):
                data = {"testlist": raw}
            elif isinstance(raw, dict) and "testlist" in raw:
                data = raw
            else:
                print_error(f"YAML format error in {testlist_file}")
                raise typer.Exit(code=1)

    except FileNotFoundError as e:
        print_error(f"File Not found in file {testlist_file}")
        raise typer.Exit(code=1) from e

    for test in data["testlist"]:
        # Single test mode
        if testlist and test_name:
            if test["test"] not in test_name:
                continue

        # Skip disabled tests
        if "iterations" not in test:
            print_error("Iterations not found in the TestList")
            raise typer.Exit(code=1)

        iterations = test["iterations"]

        if iterations == 0:
            continue

        try:
            # ==========================================================
            # RUN GENERATOR
            # ==========================================================

            gen_test = test.get("gen_test", "cva6_instr_base_test_c")

            gen_opts_str = test.get("gen_opts", "")
            opts = shlex.split(gen_opts_str)

            vcs_generator_run(
                test_name=test["test"],
                gen_test=gen_test,
                iterations=iterations,
                batch_size=batch_size,
                extensions=[],
                directed_instrs=[],
                type_instr="",
                seed=seed,
                verbose=False,
                tvec_alignment=8,
                num_of_sub_program=0,
                illegal_instr_ratio=0,
                instr_cnt=300,
                opts=opts,
            )

        except typer.Exit:
            print_error(f"{test['test']}: Return Error")
            code = 1

    if code != 0:
        raise typer.Exit(code=1)

    print_success("Sucess")
