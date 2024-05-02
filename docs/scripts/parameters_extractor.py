# Copyright 2024 Thales DIS France SAS
#
# Licensed under the Solderpad Hardware License, Version 2.1 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
# You may obtain a copy of the License at https://solderpad.org/licenses/
#
# Original Author: Jean-Roch COULON - Thales

#!/usr/bin/python3

import sys
import os

import re

from classes import Parameter

sys.path.append(os.getcwd() + "/../util")
from user_config import get_config

def parameters_extractor(spec_number, target):

    parameters = {}
    file_in = "../core/include/config_pkg.sv"

    print("Input file " + file_in)
    with open(file_in, "r", encoding="utf-8") as fin:
        print_enable = 0
        descript = "TO_BE_COMPLETED"
        for line in fin:
            if "typedef struct packed" in line:
                print_enable = 1
            if "cva6_user_cfg_t" in line:
                print_enable = 0
                break
            d = re.match(r"^ *(.*) ([\S]*);\n", line)
            h = re.match(r"^ *\/\/ (.*)\n", line)
            if h and print_enable:
                descript = h.group(1)
            if d and print_enable:
                parameters[d.group(2)] = Parameter(
                    d.group(1), descript, "TO_BE_COMPLETED"
                )
                descript = "TO_BE_COMPLETED"

    config = get_config(f"../core/include/{target}_config_pkg.sv")
    for name, parameter in parameters.items():
        parameter.value = config[name]

    return parameters


def writeout_parameter_table(fileout, parameters, module):

    with open(fileout, "w") as fout:
        fout.write("..\n")
        fout.write("   Copyright 2024 Thales DIS France SAS\n")
        fout.write(
            '   Licensed under the Solderpad Hardware License, Version 2.1 (the "License");\n'
        )
        fout.write(
            "   you may not use this file except in compliance with the License.\n"
        )
        fout.write("   SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1\n")
        fout.write(
            "   You may obtain a copy of the License at https://solderpad.org/licenses/\n\n"
        )
        fout.write("   Original Author: Jean-Roch COULON - Thales\n\n")
        fout.write(f".. _{module}_PARAMETERS:\n\n")
        fout.write(f".. list-table:: {module} parameter configuration\n")
        fout.write("   :header-rows: 1\n")
        fout.write("\n")
        fout.write("   * - Name\n")
        fout.write("     - description\n")
        fout.write("     - Value\n")
        for name in parameters:
            fout.write("\n")
            fout.write(f"   * - {name}\n")
            fout.write(f"     - {parameters[name].description}\n")
            fout.write(f"     - {parameters[name].value}\n")
