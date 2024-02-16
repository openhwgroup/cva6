# Copyright 2024 Thales DIS France SAS
#
# Licensed under the Solderpad Hardware License, Version 2.1 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
# You may obtain a copy of the License at https://solderpad.org/licenses/
#
# Original Author: Jean-Roch COULON - Thales

#!/usr/bin/python3

import re

from classes import Parameter
from classes import PortIO


def parameters_extractor(spec_number, target):

    parameters = {}
    FILE_IN = "../core/include/config_pkg.sv"

    print("Input file " + FILE_IN)
    with open(FILE_IN, "r", encoding="utf-8") as fin:
        PRINT_ENABLE = 0
        DESCRIPT = "TO_BE_COMPLETED"
        for line in fin:
            if "typedef struct packed" in line:
                PRINT_ENABLE = 1
            if "cva6_cfg_t" in line:
                PRINT_ENABLE = 0
            d = re.match(r"^ *(.*) ([\S]*);\n", line)
            h = re.match(r"^ *\/\/ (.*)\n", line)
            if h and PRINT_ENABLE:
                DESCRIPT = h.group(1)
            if d and PRINT_ENABLE:
                parameters[d.group(2)] = Parameter(
                    d.group(1), DESCRIPT, "TO_BE_COMPLETED"
                )
                DESCRIPT = "TO_BE_COMPLETED"

    FILE_IN = f"../core/include/{target}_config_pkg.sv"
    a = re.match(r".*\/(.*)_config_pkg.sv", FILE_IN)
    toto = a.group(1)
    fileout = f"./{spec_number}_{target}_design/source/parameters_{toto}.rst"
    print("Input file " + FILE_IN)
    print("Output file " + fileout)

    with open(FILE_IN, "r", encoding="utf-8") as fin:
        for line in fin:
            e = re.match(r"^ +([\S]*): (.*)(?:,|)\n", line)
            if e:
                parameters[e.group(1)].value = e.group(2)

    with open(FILE_IN, "r", encoding="utf-8") as fin:
        for line in fin:
            c = re.match(r"^ +localparam ([\S]*) = (.*);\n", line)
            if c:
                for name in parameters:
                    if c.group(1) in parameters[name].value:
                        parameters[name].value = c.group(2)
                        break

    for name in parameters:
        variable = parameters[name].value
        variable = variable.replace("1024'(", "")
        variable = variable.replace("bit'(", "")
        variable = variable.replace("unsigned'(", "")
        variable = variable.replace(")", "")
        variable = variable.replace(",", "")
        parameters[name].value = variable

    return parameters


def writeout_parameter_table(fileout, parameters, toto):

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
        fout.write(f".. _{toto}_PARAMETERS:\n\n")
        fout.write(f".. list-table:: {toto} parameter configuration\n")
        fout.write("   :header-rows: 1\n")
        fout.write("\n")
        fout.write("   * - Name\n")
        fout.write("     - Description\n")
        fout.write("     - Value\n")
        for name in parameters:
            fout.write("\n")
            fout.write(f"   * - {name}\n")
            fout.write(f"     - {parameters[name].description}\n")
            fout.write(f"     - {parameters[name].value}\n")
