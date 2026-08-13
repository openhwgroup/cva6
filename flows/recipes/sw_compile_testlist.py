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
import yaml
import typer
from flows.recipes.sw_compile import sw_compile
from flows.utils.utils import (
    ToolchainOption,
    autocompletion_target,
    autocompletion_testlist,
    autocompletion_testname_in_testlist,
    print_recipe_title,
    print_recipe_end,
    print_success,
    print_error,
    print_warning,
    print_param_table,
)

app = typer.Typer()


# ==========================================================
# RECIPE - COMPILATION OF TESTLIST
# ==========================================================


@app.command()
def sw_compile_testlist(
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
        autocompletion=autocompletion_testname_in_testlist,
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
    Build Test lists.
    """
    print_recipe_title("Software compilation of testlist", quiet=quiet)

    code = 0

    repo_dir = Path.cwd()

    testlist_file = repo_dir / testlist

    try:
        with testlist_file.open("r") as f:
            data = yaml.safe_load(f)
    except FileNotFoundError as e:
        print_error(f"testlist: File Not found in file {testlist_file}", quiet=quiet)
        raise typer.Exit(code=1) from e

    if "testlist" in data:
        print_success(f"testlist: Found in file {testlist}", quiet=quiet)
    else:
        print_error(f"testlist: Not found in file {testlist}", quiet=quiet)
        raise typer.Exit(code=1)

    for test in data["testlist"]:
        # Single test mode
        if test_name:
            if test["test"] not in test_name:
                continue
        iterations = test.get("iterations", 1)
        # Skip disables tests
        if iterations == 0:
            continue

        if "path_var" in test:
            if test["path_var"] == "TESTS_PATH":
                test["path_var"] = "verif/tests"
            elif test["path_var"] == "TESTS_GEN_PATH":
                test["path_var"] = f"build/{target}/dv_generated"
            else:
                print_warning(f"Check {test['path_var']} is a valid path", quiet=quiet)
            test["asm_tests"] = test["asm_tests"].replace(
                "<path_var>", test["path_var"]
            )
            test["gcc_opts"] = test["gcc_opts"].replace("<path_var>", test["path_var"])

        # Case where mabi or march is specified in <testlist>.yml
        if "mabi" not in test:
            test["mabi"] = mabi
        if "march" not in test:
            test["march"] = march

        test["gcc_opts"] = test["gcc_opts"].split()
        test["asm_tests"] = test["asm_tests"].split()

        print_param_table(
            {
                "Test": test["test"],
                "gcc_opts": test["gcc_opts"],
                "Iterations": test["iterations"],
                "Test path": test["asm_tests"],
                "march": test["march"],
                "mabi": test["mabi"],
            },
            "Test parameters",
            quiet=quiet,
        )
        linker_file = None
        inc_dirs = []
        options = []
        preprocessor_directives = []

        for item in test["gcc_opts"]:
            if item.startswith("-I"):
                inc_dirs += [item[2:]]
            elif item.startswith("-T"):
                linker_file = item[2:]
            elif item.startswith("-D"):
                preprocessor_directives += [item[2:]]
            elif item.startswith("-"):
                options += [item[1:]]
            else:
                test["asm_tests"] += [item]

        for i in range(iterations):
            src_file_name = [
                src.replace("<iterations>", str(i)) for src in test["asm_tests"]
            ]
            test_file_name = f"{test['test']}_{i}"
            try:
                sw_compile(
                    target=target,
                    toolchain=toolchain,
                    src_files=src_file_name,
                    inc_dirs=inc_dirs,
                    linker_file=linker_file,
                    options=options,
                    march=test["march"],
                    mabi=test["mabi"],
                    preprocessor_directives=preprocessor_directives,
                    test_name=test_file_name,
                    quiet=quiet,
                )
            except typer.Exit:
                print_error(f"{test['test']}: Return Error", quiet=quiet)
                code = 1

    print_recipe_end("Completed", quiet=quiet)

    if code != 0:
        raise typer.Exit(code=1)
