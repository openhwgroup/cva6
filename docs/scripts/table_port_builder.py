# Copyright 2024 Thales DIS France SAS
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
# You may obtain a copy of the License at https://solderpad.org/licenses/
#
# Original Author: Jean-Roch COULON - Thales

#!/usr/bin/python3

import re


class portIO:
    def __init__(
        self,
        name,
        direction,
        type,
        description,
        connection,
    ):
        self.name = name
        self.direction = direction
        self.type = type
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

    for filein in file:
        a = re.match(".*\/(.*).sv", filein)
        module = a.group(1)
        fileout = "./04_cv32a65x_design/source/port_" + module + ".rst"
        print("Input file " + filein)
        print("Output file " + fileout)
        port = []
        with open(filein, "r") as fin:
            description = "none"
            connection = "none"
            for l1 in fin:
                e = re.match("^ +(?:(in|out))put ([\S]*(?: [\S]*|)) ([\S]*)\n", l1)
                d = re.match("^ +\/\/ (.*) - ([\S]*)\n", l1)
                if d:
                    description = d.group(1)
                    connection = d.group(2)
                if e:
                    name = e.group(3)
                    name = name.split(",")
                    port.append(
                        portIO(name[0], e.group(1), e.group(2), description, connection)
                    )
                    description = "none"
                    connection = "none"

        with open(fileout, "w") as fout:
            fout.write("..\n")
            fout.write("   Copyright 2024 Thales DIS France SAS\n")
            fout.write(
                '   Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");\n'
            )
            fout.write(
                "   you may not use this file except in compliance with the License.\n"
            )
            fout.write("   SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0\n")
            fout.write(
                "   You may obtain a copy of the License at https://solderpad.org/licenses/\n\n"
            )
            fout.write("   Original Author: Jean-Roch COULON - Thales\n\n")
            fout.write(".. _CVA6_%s:\n\n" % (module))
            fout.write(".. list-table:: %s module IO ports\n" % (module))
            fout.write("   :header-rows: 1\n")
            fout.write("\n")
            fout.write("   * - Signal\n")
            fout.write("     - IO\n")
            fout.write("     - connection\n")
            fout.write("     - Type\n")
            fout.write("     - Description\n")
            for i in range(len(port)):
                fout.write("\n")
                fout.write("   * - ``%s``\n" % (port[i].name))
                fout.write("     - %s\n" % (port[i].direction))
                fout.write("     - %s\n" % (port[i].connection))
                fout.write("     - %s\n" % (port[i].type))
                fout.write("     - %s\n" % (port[i].description))
