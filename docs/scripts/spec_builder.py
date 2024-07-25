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
import sys

from classes import Parameter
from classes import PortIO
from define_blacklist import define_blacklist
from parameters_extractor import parameters_extractor
from parameters_extractor import writeout_parameter_table
from parameters_extractor import writeout_parameter_table_adoc

HEADER_RST = """\
..
   Copyright 2024 Thales DIS France SAS
   Licensed under the Solderpad Hardware License, Version 2.1 (the "License");
   you may not use this file except in compliance with the License.
   SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
   You may obtain a copy of the License at https://solderpad.org/licenses/

   Original Author: Jean-Roch COULON - Thales

"""

HEADER_ADOC = """\
////
   Copyright 2024 Thales DIS France SAS
   Licensed under the Solderpad Hardware License, Version 2.1 (the "License");
   you may not use this file except in compliance with the License.
   SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
   You may obtain a copy of the License at https://solderpad.org/licenses/

   Original Author: Jean-Roch COULON - Thales
////

"""

def print_to_rst(pathout, target, module, ports, comments):
    fileout = f"{pathout}/port_{module}.rst"
    print("Output file " + fileout)

    with open(fileout, "w", encoding="utf-8") as fout:
        fout.write(HEADER_RST)
        fout.write(f".. _CVA6_{module}_ports:\n\n")
        fout.write(f".. list-table:: **{module} module** IO ports\n")
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
        fout.write("\n")
        if len(comments) != 0:
            fout.write(
                f"Due to {target} configuration, some ports are tied to a static value. These ports do not appear in the above table, they are listed below\n"
            )
            fout.write("\n")
            for comment in comments:
                fout.write(f"| {comment[0]},\n|   {comment[1]}\n")
        fout.write("\n")

def print_to_adoc(pathout, target, module, ports, comments):
    fileout = f"{pathout}/port_{module}.adoc"
    print("Output file " + fileout)

    # format comments
    for comment in comments:
        for i in range(len(comment)):
            comment[i] = comment[i].replace('``', '`')
            comment[i] = comment[i].replace('|', '*')

    with open(fileout, "w", encoding="utf-8") as fout:
        fout.write(HEADER_ADOC)

        fout.write(f"[[_CVA6_{module}_ports]]\n\n")

        fout.write(f".*{module} module* IO ports\n")
        fout.write("|===\n")
        fout.write("|Signal | IO | Description | connexion | Type\n\n")

        for port in ports:
            fout.write(f"|`{port.name}` | {port.direction} | {port.description} | {port.connexion} | {port.data_type}\n\n")
        fout.write("|===\n")

        if len(comments) != 0:
            fout.write(
                f"Due to {target} configuration, some ports are tied to a static value. These ports do not appear in the above table, they are listed below\n\n"
            )
            for comment in comments:
                fout.write(f"{comment[0]},::\n*   {comment[1]}\n")
        fout.write("\n")

def main():
    PATH = "04_cv32a65x"
    generate_file_type = "adoc"
    [spec_number, target] = PATH.split("_")

    print(spec_number, target)

    # Parameters
    parameters = parameters_extractor(spec_number, target)

    pathout = f"./{spec_number}_{target}/design/source"
    if generate_file_type in ['rst']:
        fileout = f"{pathout}/parameters_{target}.rst"
        writeout_parameter_table(fileout, parameters, target)
    elif generate_file_type in ['adoc']:
        pathout = f"./{spec_number}_{target}/design/source"
        fileout = f"{pathout}/parameters.adoc"
        writeout_parameter_table_adoc(fileout, parameters, target)
    else:
        raise Exception("Format de sortie %s non pris en charge"%generate_file_type)

    # User_cfg
    export_user_cfg_doc("01_cva6_user/user_cfg_doc.rst", parameters)

    # Ports
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
    file.append("../core/alu.sv")
    file.append("../core/branch_unit.sv")
    file.append("../core/csr_buffer.sv")
    file.append("../core/mult.sv")
    file.append("../core/multiplier.sv")
    file.append("../core/serdiv.sv")
    file.append("../core/load_store_unit.sv")
    file.append("../core/load_unit.sv")
    file.append("../core/store_unit.sv")
    file.append("../core/lsu_bypass.sv")
    file.append("../core/cvxif_fu.sv")
    file.append("../core/cache_subsystem/cva6_hpdcache_subsystem.sv")

    black_list = define_blacklist(parameters)

    for filein in file:
        comments = []
        a = re.match(r".*\/(.*).sv", filein)
        module = a.group(1)
        print("Input file " + filein)
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

        if generate_file_type in ['rst']:
            print_to_rst(pathout, target, module, ports, comments)
        elif generate_file_type in ['adoc']:
            print_to_adoc(pathout, target, module, ports, comments)
        else:
            raise Exception("Format de sortie %s non pris en charge"%generate_file_type)

def export_user_cfg_doc(out_path, params):
    with open(out_path, "w", encoding="utf-8") as f:
        f.write(HEADER_RST)
        f.write("""\
.. _cva6_user_cfg_doc:

.. list-table:: ``cva6_user_cfg_t`` parameters
   :header-rows: 1

   * - Name
     - Type
     - Description
""")
        for name, param in params.items():
            f.write("\n")
            f.write(f"   * - ``{name}``\n")
            f.write(f"     - ``{param.datatype.strip()}``\n")
            f.write(f"     - {param.description}\n")

if __name__ == "__main__":
    main()
