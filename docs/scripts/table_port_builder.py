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
        name0,
        direction0,
        type0,
        comment0,
        connection0,
    ):
        self.name0 = name0
        self.direction0 = direction0
        self.type0 = type0
        self.comment0 = comment0
        self.connection0 = connection0


if __name__ == "__main__":

    file0 = []
    file0.append("../core/cva6.sv")
    file0.append("../core/frontend/frontend.sv")
    file0.append("../core/frontend/bht.sv")
    file0.append("../core/frontend/btb.sv")
    file0.append("../core/frontend/ras.sv")
    file0.append("../core/frontend/instr_queue.sv")
    file0.append("../core/frontend/instr_scan.sv")
    file0.append("../core/instr_realign.sv")

    for filein in file0:
        a = re.match(".*\/(.*).sv", filein)
        module = a.group(1)
        fileout = "./04_cv32a6_design/source/port_" + module + ".rst"
        print("Input file " + filein)
        print("Output file " + fileout)
        port = []
        with open(filein, "r") as fin:
            comment0 = "none"
            connection0 = "none"
            for l1 in fin:
                e = re.match("^ +(?:(in|out))put ([\S]*(?: [\S]*|)) ([\S]*)\n", l1)
                d = re.match("^ +\/\/ (.*) - ([\S]*)\n", l1)
                if d:
                    comment0 = d.group(1)
                    connection0 = d.group(2)
                if e:
                    name = e.group(3)
                    name = name.split(",")
                    port.append(
                        portIO(name[0], e.group(1), e.group(2), comment0, connection0)
                    )
                    comment0 = "none"
                    connection0 = "none"

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
            fout.write(".. _CV32A6_%s:\n\n" % (module))
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
                fout.write("   * - ``%s``\n" % (port[i].name0))
                fout.write("     - %s\n" % (port[i].direction0))
                fout.write("     - %s\n" % (port[i].connection0))
                fout.write("     - %s\n" % (port[i].type0))
                fout.write("     - %s\n" % (port[i].comment0))
