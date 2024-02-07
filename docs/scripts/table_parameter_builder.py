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


class Parameter:
    def __init__(
        self,
        datatype,
        description,
        value,
    ):
        self.datatype = datatype
        self.description = description
        self.value = value


if __name__ == "__main__":

    parameters = {}
    filein = "../core/include/config_pkg.sv"

    with open(filein, "r", encoding="utf-8") as fin:
        print_enable = 0
        description = "TO_BE_COMPLETED"
        for line in fin:
            if "typedef struct packed" in line:
                print_enable = 1
            if "cva6_cfg_t" in line:
                print_enable = 0
            d = re.match("^ *(.*) ([\S]*);\n", line)
            h = re.match("^ *\/\/ (.*)\n", line)
            if h and print_enable:
                description = h.group(1)
            if d and print_enable:
                parameters[d.group(2)] = Parameter(
                    d.group(1), description, "TO_BE_COMPLETED"
                )
                description = "TO_BE_COMPLETED"
    fin.close()

    filein = "../core/include/cv32a65x_config_pkg.sv"
    a = re.match(r".*\/(.*)_config_pkg.sv", filein)
    module = a.group(1)
    fileout = "./04_cv32a65x_design/source/parameters_" + module + ".rst"
    print("Input file " + filein)
    print("Output file " + fileout)

    with open(filein, "r", encoding="utf-8") as fin:
        for line in fin:
            e = re.match("^ +([\S]*): (.*)(?:,|)\n", line)
            if e:
                parameters[e.group(1)].value = e.group(2)
    fin.close()

    with open(filein, "r", encoding="utf-8") as fin:
        for line in fin:
            c = re.match("^ +localparam ([\S]*) = (.*);\n", line)
            if c:
                for name in parameters:
                    if c.group(1) in parameters[name].value:
                        parameters[name].value = c.group(2)
                        break
    fin.close()

    for name in parameters:
        variable = parameters[name].value
        variable = variable.replace("1024'(", "")
        variable = variable.replace("bit'(", "")
        variable = variable.replace("unsigned'(", "")
        variable = variable.replace(")", "")
        variable = variable.replace(",", "")
        parameters[name].value = variable
        print(name, parameters[name].value, parameters[name].description)

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
