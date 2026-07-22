# Copyright 2026 Thales France
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
# You may obtain a copy of the License at https://solderpad.org/licenses/
#
# Original Author: Mounsaf YOUSFI/Yannick Casamatta (yannick.casamatta@thalesgroup.com)

# Please refer to flows/README.md to add target

from pathlib import Path
import shutil
import re
from datetime import datetime
import typer
from flows.utils.utils import (
    autocompletion_target,
    autocompletion_param_config,
    print_recipe_title,
    print_recipe_end,
    print_step,
    print_info,
    print_error,
    print_param_table,
    print_table,
)


app = typer.Typer()


@app.command()
def hwconfig_forge(
    new_target_name: str = typer.Option(
        ...,
        "--target_forged",
        "-f",
        help="Name of forged CVA6 user configuration",
    ),
    target: str = typer.Option(
        ...,
        "--target_ref",
        "-t",
        help="Reference CVA6 user configuration",
        autocompletion=autocompletion_target,
    ),
    arg_replace: list[str] = typer.Option(
        ...,
        "--param",
        "-p",
        help="Individual parameters to override with value <parameter=newvalue>",
        autocompletion=autocompletion_param_config,
    ),
):
    """
    Hardware config modify/overwrite
    """
    print_recipe_title("HWCONFIG : Forging new config")

    # ==========================================================
    # GENERATE MODIFICATIONS DICTIONARY
    # ==========================================================

    try:
        arg_replace_dict = dict(item.split("=") for item in arg_replace)
        arg_replace_str = ""
        for key, value in arg_replace_dict.items():
            arg_replace_str += f"{key}: {value}\n"
    except Exception as e:
        print_error(
            f'\033[1mThe list of arguments to overwrite is incorrect, please use ./cook.py hwconfig-forge TARGET "PARAMETER=VALUE" "PARAMETER=VALUE"...\033[0m{e}'
        )
        raise typer.Exit(code=1)

    print_param_table(
        {
            "New target config": new_target_name,
            "Original target config": target,
            "Values to overwrite": arg_replace_str,
        },
        "Options",
    )

    # ==========================================================
    # FETCH TEMPLATE (ORIGINAL TARGET CONFIG PKG)
    # ==========================================================

    print_step("Target config package fetch")
    repo_dir = Path.cwd()
    config_pkg_dir = repo_dir / "core" / "include"
    config_pkg = config_pkg_dir / f"{target}_config_pkg.sv"
    forged_config_pkg = config_pkg_dir / f"{new_target_name}_config_pkg.sv"
    config_linker = repo_dir / "config" / "target" / target / "link.ld"
    forged_config_linker = (
        repo_dir
        / "config"
        / "gen_from_riscv_config"
        / new_target_name
        / "linker"
        / "link.ld"
    )
    config_spike_file = repo_dir / "config" / "target" / target / "spike.yaml"
    forged_config_spike_file = (
        repo_dir
        / "config"
        / "gen_from_riscv_config"
        / new_target_name
        / "spike"
        / "spike.yaml"
    )
    if config_pkg.exists():
        print_info(f"{config_pkg_dir}/{target}_config_pkg.sv exists and found")
        config_pkg = config_pkg.open()
    else:
        print_error(f"{config_pkg_dir}/{target}_config_pkg.sv does not exist")
        raise typer.Exit(code=1)

    print_step("Target config package forge")

    # ==========================================================
    # FORGE MODIFIED CONFIG PKG
    # ==========================================================

    forged_config_content = []

    param_table = {}
    titles_l = ["Parameter", "Old value", "New value"]
    style_l = ["cyan", "red", "green"]
    compare_forge_str = "// Generated using cook.py hwconfig-forge recipe"
    cTime = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    forge_str = f"{compare_forge_str} at {cTime}"
    forged_config_content = []
    config_pkg_1st_line = str(config_pkg.readline()).strip()
    forged_config_content.append(forge_str)
    if compare_forge_str not in config_pkg_1st_line:
        forged_config_content.append(config_pkg_1st_line)
    for line in config_pkg.read().splitlines():
        if not line or line.startswith("//"):
            forged_config_content.append(line)
            continue

        for rkey, rval in arg_replace_dict.items():
            if rkey in line:
                if re.search(rf"\({rkey}\)", line):
                    continue
                if re.search(rf"\b{rkey}\b", line):
                    val_l = []
                    val_l += [line.strip().strip(",")]  # old value
                    if ": " in line:
                        if re.search(r"\(.+?\)", line):
                            line = re.sub(r"\(.+?\)", f"({rval})", line)
                        else:
                            line = re.sub(r":.*", f": {rval},", line)
                    else:
                        line = re.sub(r"=.*", f"= {rval};", line)
                    val_l += [line.strip().strip(",")]  # new value

                    param_table[rkey] = val_l
                else:
                    continue

        forged_config_content.append(line)

    print_table(
        params=param_table,
        title="Updated config values",
        column_name=titles_l,
        style=style_l,
    )

    print_step(f"New target '{new_target_name}' generation")

    with forged_config_pkg.open("w") as f:
        for line in forged_config_content:
            f.write(f"{line}\n")
        print_info(f"create {new_target_name}_config_pkg.sv")

    # Create parents dir and do not raise error if directories already exists
    if not forged_config_linker.exists():
        forged_config_linker.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy(config_linker, forged_config_linker)
        print_info(f"Copy {config_linker} -> {forged_config_linker}")
    if not forged_config_spike_file.exists():
        forged_config_spike_file.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy(config_spike_file, forged_config_spike_file)
        print_info(f"Copy {config_spike_file} -> {forged_config_spike_file}")

    # ==========================================================
    # List
    # ==========================================================

    gen_files = [
        forged_config_pkg,
        forged_config_linker,
        forged_config_spike_file,
    ]

    print_step("Generated files")
    for genfile in gen_files:
        if genfile.exists():
            print_info(f"> {genfile}")
        else:
            print_error(f"> Missing: {genfile}")

    print_recipe_end("Completed")
