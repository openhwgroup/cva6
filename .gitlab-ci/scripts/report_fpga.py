# Copyright 2022 Thales Silicon Security
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
# You may obtain a copy of the License at https://solderpad.org/licenses/
#
# Original Author: Guillaume Chauvon(guillaume.chauvon@thalesgroup.com)

import re
import sys

import report_builder as rb

with open(str(sys.argv[1]), "r") as f:
    log = f.read()

with open(str(sys.argv[2]), "r") as f:
    outputlog = f.read()

pattern = re.compile(
    "\|(?P<ind> +)(?P<Instance>[\w()\[\].]+) +\| +(?P<Module>[\w()\[\].]+) \| +(?P<TotalLUTs>\d+) \| +(?P<LogicLUTs>\d+) \| +(?P<LUTRAMs>\d+) \| +(?P<SRLs>\d+) \| +(?P<FFs>\d+) \| +(?P<RAMB36>\d+) \| +(?P<RAMB18>\d+) \| +(?P<DSP48Blocks>\d+) \|"
)

data = []
for line in pattern.finditer(log):
    l = line.groupdict()
    if l["Instance"] == "i_ariane_peripherals":
        break
    data.append(l)

report = rb.Report()
metric = rb.TableMetric('Utilization Results')

for i in data:
    if (i["ind"]).count(" ") < 10:
        if i["Instance"] == "ariane_xilinx":
            total = int(i["TotalLUTs"]) // 1000
            report.label = f"{total} kLUTs"
        metric.add_value(
            i["Instance"],
            i["Module"],
            i["TotalLUTs"] + " TotalLUTs",
            i["LogicLUTs"] + " LogicLUTs",
            i["LUTRAMs"] + " LUTRAMs",
            i["SRLs"] + " SRLs",
            i["FFs"] + " FFs",
            i["RAMB36"] + " RAMB36",
            i["RAMB18"] + " RAMB18",
            i["DSP48Blocks"] + " DSP48Blocks",
        )

log_metric = rb.LogMetric("Last lines of logfile")
log_metric.values = outputlog.splitlines()

report.add_metric(metric, log_metric)
report.dump()
