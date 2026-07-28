# Copyright 2022 Thales Silicon Security
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
# You may obtain a copy of the License at https://solderpad.org/licenses/
#
# Original Author: Théo Giovinazzi
# Contributors:   Théo Giovinazzi

import sys
from pathlib import Path

import yaml


def main():
    report_paths = sys.argv[1:]

    if not report_paths:
        print("Error: No report file provided.")
        sys.exit(1)

    failed_reports = []

    for path_str in report_paths:
        path = Path(path_str)
        if not path.exists():
            print(f"Warning: File {path} not found.")
            continue

        with open(path, "r", encoding="utf-8") as f:
            try:
                data = yaml.safe_load(f)
            except yaml.YAMLError as e:
                print(f"YAML reading error for {path}: {e}")
                sys.exit(1)

        if data and data.get("status") == "fail":
            failed_reports.append(path.name)

    if failed_reports:
        print("\nPIPELINE FAILURE: The following reports contain errors:")
        for rep in failed_reports:
            print(f"  - {rep}")
        sys.exit(1)
    else:
        print("\nSUCCESS: All analyzed reports are clear.")
        sys.exit(0)


if __name__ == "__main__":
    main()
