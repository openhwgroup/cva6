#!/usr/bin/env python3
# Copyright 2026 Thales France
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
# You may obtain a copy of the License at https://solderpad.org/licenses/
#
# Original Author: Yannick Casamatta (yannick.casamatta@thalesgroup.com)

# Please refer to flows/README.md to add target

import importlib
import pkgutil
import typer

app = typer.Typer()


def load_commands(folder: str):
    # folder to look for typer commands
    package = f"flows.{folder}"
    pkg = importlib.import_module(package)

    for _, module_name, _ in pkgutil.iter_modules(pkg.__path__):
        full_module_name = f"{package}.{module_name}"
        module = importlib.import_module(full_module_name)
        if hasattr(module, "app"):
            # app.add_typer(module.app, name=module_name)
            app.add_typer(module.app)


# Load all command in commands and patterns folders
load_commands("recipes")
load_commands("patterns")
load_commands("report_scripts")
load_commands("macros")

if __name__ == "__main__":
    app()
