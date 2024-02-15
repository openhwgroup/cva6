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

class PortIO:
    def __init__(
        self,
        name,
        direction,
        data_type,
        description,
        connexion,
    ):
        self.name = name
        self.direction = direction
        self.data_type = data_type
        self.description = description
        self.connexion = connexion


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
    module = a.group(1)
    fileout = f"./{spec_number}_{target}_design/source/parameters_{module}.rst"
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
        fout.write("     - Description\n")
        fout.write("     - Value\n")
        for name in parameters:
            fout.write("\n")
            fout.write(f"   * - {name}\n")
            fout.write(f"     - {parameters[name].description}\n")
            fout.write(f"     - {parameters[name].value}\n")

    return parameters


if __name__ == "__main__":

    path = "04_cv32a65x"
    [spec_number, target] = path.split("_")

    parameters = parameters_extractor(spec_number, target)

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

    black_list = {}
    black_list["flush_bp_i"] = ["For any HW configuration", "zero"]

    param = "IsRVFI"
    paramvalue = "0"
    if paramvalue == "0":
        black_list["RVFI"] = [f"As {param} = {paramvalue}", "0"]

    param = "DebugEn"
    paramvalue = parameters[param].value
    if paramvalue == "0":
        black_list["set_debug_pc_i"] = [f"As {param} = {paramvalue}", "0"]
        black_list["debug_mode_i"] = [f"As {param} = {paramvalue}", "0"]
        black_list["debug_req_i"] = [f"As {param} = {paramvalue}", "0"]

    param = "RVV"
    paramvalue = parameters[param].value
    if paramvalue == "0":
        black_list["vs_i"] = [f"As {param} = {paramvalue}", "0"]

    param = "EnableAccelerator"
    paramvalue = parameters[param].value
    if paramvalue == "0":
        black_list["ACC_DISPATCHER"] = [f"As {param} = {paramvalue}", "0"]

    param = "RVF"
    paramvalue = parameters[param].value
    if paramvalue == "0":
        black_list["fs_i"] = [f"As {param} = {paramvalue}", "0"]
        black_list["frm_i"] = [f"As {param} = {paramvalue}", "0"]
        black_list["fpu_valid_o"] = [f"As {param} = {paramvalue}", "0"]
        black_list["fpu_ready_o"] = [f"As {param} = {paramvalue}", "0"]
        black_list["fpu_fmt_o"] = [f"As {param} = {paramvalue}", "0"]
        black_list["fpu_rm_o"] = [f"As {param} = {paramvalue}", "0"]
        black_list["fpu_valid_i"] = [f"As {param} = {paramvalue}", "0"]
        black_list["fpu_fmt_i"] = [f"As {param} = {paramvalue}", "0"]
        black_list["fpu_rm_i"] = [f"As {param} = {paramvalue}", "0"]
        black_list["fpu_frm_i"] = [f"As {param} = {paramvalue}", "0"]
        black_list["fpu_prec_i"] = [f"As {param} = {paramvalue}", "0"]
        black_list["fpu_trans_id_o"] = [f"As {param} = {paramvalue}", "0"]
        black_list["fpu_result_o"] = [f"As {param} = {paramvalue}", "0"]
        black_list["fpu_exception_o"] = [f"As {param} = {paramvalue}", "0"]

    param = "RVA"
    paramvalue = parameters[param].value
    if paramvalue == "0":
        black_list["amo_req_o"] = [f"As {param} = {paramvalue}", "0"]
        black_list["amo_resp_i"] = [f"As {param} = {paramvalue}", "0"]
        black_list["amo_valid_commit_i"] = [f"As {param} = {paramvalue}", "0"]

    param = "PRIV"
    paramvalue = "MachineOnly"
    if paramvalue == "MachineOnly": # TODO PRIV to be added to RTL parameters
        black_list["ld_st_priv_lvl_i"] = [f"As {param} = {paramvalue}", "MAchineMode"]
        black_list["priv_lvl_i"] = [f"As {param} = {paramvalue}", "MachineMode"]
        # black_list["tvm_i"] = [f"As {param} = {paramvalue}", "0"]
        # black_list["tw_i"] = [f"As {param} = {paramvalue}", "0"]
        # black_list["tsr_i"] = [f"As {param} = {paramvalue}", "0"]

    param = "PerfCounterEn"
    paramvalue = "0"
    if paramvalue == "0": # TODO PerfCounterEn to be added to RTL parameters
        black_list["PERF_COUNTERS"] = [f"As {param} = {paramvalue}", "0"]

    param = "MMUPresent"
    paramvalue = "0"
    if paramvalue == "0": # TODO the MMUPresent to be added to RTL parameters
        black_list["flush_tlb_i"] = [f"As {param} = {paramvalue}", "0"]


    for filein in file:
        comments = []
        a = re.match(r".*\/(.*).sv", filein)
        module = a.group(1)
        fileout = "./04_cv32a65x_design/source/port_" + module + ".rst"
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
                                comment[1] = comment[1]+f"\n|   ``{name}`` {e.group(1)}put is tied to {black_list[connexion][1]}"
                                break
                        else:
                            comments.append([black_list[connexion][0], f"``{name}`` {e.group(1)}put is tied to {black_list[connexion][1]}"])
                    else:
                        if name in black_list:
                            for i, comment in enumerate(comments):
                                if black_list[name][0] == comment[0]:
                                    comment[1] = comment[1]+f"\n|   ``{name}`` {e.group(1)}put is tied to {black_list[name][1]}"
                                    break
                            else:
                                comments.append([black_list[name][0], f"``{name}`` {e.group(1)}put is tied to {black_list[name][1]}"])
                        else:
                            ports.append(
                                PortIO(name, e.group(1), data_type, description, connexion)
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
            fout.write(f".. _CVA6_{module}_ports:\n\n")
            fout.write(f".. list-table:: {module} module IO ports\n")
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
            fout.write(f"Due to {target} configuration, some ports are tied to a static value. These ports do not appear in the above table, they are listed below\n")
            fout.write(f"\n")
            for comment in comments:
                fout.write(f"| {comment[0]},\n|   {comment[1]}\n")
            else:
                fout.write(f"none\n")
                
