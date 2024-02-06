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


class PortIO:
    def __init__(
        self,
        name,
        direction,
        data_type,
        description,
        connection,
    ):
        self.name = name
        self.direction = direction
        self.data_type = data_type
        self.description = description
        self.connection = connection


if __name__ == "__main__":
    file = []
    file.append("../core/cva6.sv")
    file.append("../core/frontend/frontend.sv")
    file.append("../core/frontend/bht.sv")
    file.append("../core/frontend/btb.sv")
    file.append("../core/frontend/ras.sv")
    file.append("../core/frontend/instr_queue.sv")
    file.append("../core/frontend/instr_scan.sv")
    file.append("../core/instr_realign.sv")
    file.append("../core/id_stage.sv")
    file.append("../core/issue_stage.sv")
    file.append("../core/ex_stage.sv")
    file.append("../core/commit_stage.sv")

    for filein in file:
        a = re.match(r".*\/(.*).sv", filein)
        module = a.group(1)
        fileout = "./04_cv32a65x_design/source/port_" + module + ".rst"
        print("Input file " + filein)
        print("Output file " + fileout)
        ports = []
        with open(filein, "r", encoding="utf-8") as fin:
            description = "none"
            connection = "none"
            for line in fin:
                e = re.match(r"^ +(?:(in|out))put ([\S]*(?: [\S]*|)) ([\S]*)\n", line)
                d = re.match(r"^ +\/\/ (.*) - ([\S]*)\n", line)
                if d:
                    description = d.group(1)
                    connection = d.group(2)
                if e:
                    name = e.group(3)
                    name = name.split(",")
                    ports.append(
                        PortIO(name[0], e.group(1), e.group(2), description, connection)
                    )
                    description = "none"
                    connection = "none"

        with open(fileout, "w", encoding="utf-8") as fout:
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
            fout.write(f".. _CVA6_{module}_ports:\n\n")
            fout.write(f".. list-table:: {module} module IO ports\n")
            fout.write("   :header-rows: 1\n")
            fout.write("\n")
            fout.write("   * - Signal\n")
            fout.write("     - IO\n")
            fout.write("     - Connection\n")
            fout.write("     - Type\n")
            fout.write("     - Description\n")
            for i, port in enumerate(ports):
                fout.write("\n")
                fout.write(f"   * - ``{port.name}``\n")
                fout.write(f"     - {port.direction}\n")
                fout.write(f"     - {port.connection}\n")
                fout.write(f"     - {port.data_type}\n")
                fout.write(f"     - {port.description}\n")
