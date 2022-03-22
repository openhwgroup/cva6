# Copyright 2021 Thales DIS design services SAS
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
# You may obtain a copy of the License at https://solderpad.org/licenses/
#
# Original Author: Jean-Roch COULON (jean-roch.coulon@thalesgroup.com)
#

import sys


def process_elf(FILE, GATESIZE):
    print(FILE)
    flag = 0
    block = {}
    with open(FILE, "r") as fin:
        for l in fin:
            if "Hierarchical cell" in l:
                flag = 1
            if flag == 1:
                tmp = l.split(" ")
                ipname = tmp[0]
                if (
                    ipname.count("/") == 0
                    or (ipname.count("/") == 1 and "ex_stage_i" in ipname)
                    or (
                        ipname.count("/") == 1
                        and "i_cache_subsystem" in ipname
                        and "stream" not in ipname
                    )
                    or (ipname.count("/") == 1 and "issue_stage_i" in ipname)
                    or (ipname.count("/") == 2 and "ex_stage_i" in ipname)
                    or ("i_issue_read_operands" in ipname)
                ):
                    for i in range(1, len(tmp)):
                        if tmp[i] != "":
                            ipgate = tmp[i]
                            if "." in ipgate and "Total" not in ipname:
                                ipgate = ipgate.split(".")
                                print(
                                    "{:50} {:.0f} kg".format(
                                        ipname, int(ipgate[0]) / GATESIZE
                                    )
                                )
                                block[ipname] = int(int(ipgate[0]) / GATESIZE)
                            break
    fin.close()


if __name__ == "__main__":
    print(sys.argv)
    process_elf(FILE=sys.argv[1], GATESIZE=int(sys.argv[2], 10))
