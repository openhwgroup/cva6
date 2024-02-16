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
from define_blacklist import define_blacklist
from parameters_extractor import parameters_extractor
from parameters_extractor import writeout_parameter_table


if __name__ == "__main__":

    path = "04_cv32a65x"
    [spec_number, target] = path.split("_")

    print(spec_number, target)
    parameters = parameters_extractor(spec_number, target)

    fileout = f"./{spec_number}_{target}_design/source/parameters_{target}.rst"
    writeout_parameter_table(fileout, parameters, target)

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
    file.append("../core/controller.sv")
    file.append("../core/csr_regfile.sv")
    file.append("../core/decoder.sv")
    file.append("../core/compressed_decoder.sv")
    file.append("../core/scoreboard.sv")
    file.append("../core/issue_read_operands.sv")

    black_list = define_blacklist(parameters)

    for filein in file:
        comments = []
        a = re.match(r".*\/(.*).sv", filein)
        toto = a.group(1)
        fileout = "./04_cv32a65x_design/source/port_" + toto + ".rst"
        print("Input file " + filein)
        print("Output file " + fileout)
        ports = []
        with open(filein, "r", encoding="utf-8") as fin:
            description = "none"
            connexion = "none"
            for line in fin:
                e = re.match(r"^ +(?:(in|out))put +([\S]*(?: +.* *|)) ([\S]*)\n", line)
                d = re.match(r"^ +\/\/ (.*) - ([\S]*)\n", line)
                if d:
                    description = d.group(1)
                    connexion = d.group(2)
                if e:
                    name = e.group(3)
                    name = name.replace(",", "")
                    data_type = e.group(2)
                    data_type = data_type.replace(" ", "")
                    if connexion in black_list:
                        for i, comment in enumerate(comments):
                            if black_list[connexion][0] == comment[0]:
                                comment[1] = (
                                    comment[1]
                                    + f"\n|   ``{name}`` {e.group(1)}put is tied to {black_list[connexion][1]}"
                                )
                                break
                        else:
                            comments.append(
                                [
                                    black_list[connexion][0],
                                    f"``{name}`` {e.group(1)}put is tied to {black_list[connexion][1]}",
                                ]
                            )
                    else:
                        if name in black_list:
                            for i, comment in enumerate(comments):
                                if black_list[name][0] == comment[0]:
                                    comment[1] = (
                                        comment[1]
                                        + f"\n|   ``{name}`` {e.group(1)}put is tied to {black_list[name][1]}"
                                    )
                                    break
                            else:
                                comments.append(
                                    [
                                        black_list[name][0],
                                        f"``{name}`` {e.group(1)}put is tied to {black_list[name][1]}",
                                    ]
                                )
                        else:
                            ports.append(
                                PortIO(
                                    name, e.group(1), data_type, description, connexion
                                )
                            )
                    description = "none"
                    connexion = "none"

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
            fout.write(f".. _CVA6_{toto}_ports:\n\n")
            fout.write(f".. list-table:: {toto} module IO ports\n")
            fout.write("   :header-rows: 1\n")
            fout.write("\n")
            fout.write("   * - Signal\n")
            fout.write("     - IO\n")
            fout.write("     - Description\n")
            fout.write("     - connexion\n")
            fout.write("     - Type\n")
            for i, port in enumerate(ports):
                fout.write("\n")
                fout.write(f"   * - ``{port.name}``\n")
                fout.write(f"     - {port.direction}\n")
                fout.write(f"     - {port.description}\n")
                fout.write(f"     - {port.connexion}\n")
                fout.write(f"     - {port.data_type}\n")
            fout.write(f"\n")
            fout.write(
                f"Due to {target} configuration, some ports are tied to a static value. These ports do not appear in the above table, they are listed below\n"
            )
            fout.write(f"\n")
            for comment in comments:
                fout.write(f"| {comment[0]},\n|   {comment[1]}\n")
            if len(comments) == 0:
                fout.write(f"none\n")
