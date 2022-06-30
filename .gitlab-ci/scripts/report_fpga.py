# Copyright 2022 Thales Silicon Security
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
# You may obtain a copy of the License at https://solderpad.org/licenses/
#
# Original Author: Guillaume Chauvon(guillaume.chauvon@thalesgroup.com)

import re
from pprint import pprint
import yaml
import datetime
import sys
import os

with open(str(sys.argv[1]), "r") as f:
    log = f.read()

global_pass = "pass"

report = {
    'title': os.environ["DASHBOARD_JOB_TITLE"],
    'description': os.environ["DASHBOARD_JOB_DESCRIPTION"],
    'category': os.environ["DASHBOARD_JOB_CATEGORY"],
    'sort_index': os.environ["DASHBOARD_SORT_INDEX"],
    'job_id': os.environ["CI_JOB_ID"],
    'job_url': os.environ["CI_JOB_URL"],
    'job_stage_name': os.environ["CI_JOB_STAGE"],
    'job_started_at': int(datetime.datetime.strptime(os.environ['CI_JOB_STARTED_AT'], '%Y-%m-%dT%H:%M:%S%z').timestamp()),
    'job_end_at': int(datetime.datetime.now().timestamp()),
    'token': 'YC' + str(datetime.datetime.now().timestamp()).replace('.', ''),
    'status': "pass",
    'metrics': []
}

pattern = re.compile(
    "\|(?P<ind> +)(?P<Instance>[\w()\[\].]+) +\| +(?P<Module>[\w()\[\].]+) \| +(?P<TotalLUTs>\d+) \| +(?P<LogicLUTs>\d+) \| +(?P<LUTRAMs>\d+) \| +(?P<SRLs>\d+) \| +(?P<FFs>\d+) \| +(?P<RAMB36>\d+) \| +(?P<RAMB18>\d+) \| +(?P<DSP48Blocks>\d+) \|"
)

data = []
for line in pattern.finditer(log):
    l = line.groupdict()
    if l["Instance"] == "i_ariane_peripherals":
        break
    data.append(l)


metric = {
    'display_name': 'Utilization Results',
    'sort_index': 1,
    'type': 'table',
    'status': 'pass',
    'value': [],
}

for i in data:
    value = {"col": []}
    if (i["ind"]).count(" ") < 10:
        value["col"].append(i["Instance"])
        if i["Instance"] == "ariane_xilinx":
            report["label"] = i["TotalLUTs"] + " TotalLUTs"
        value["col"].append(i["Module"])
        value["col"].append(i["TotalLUTs"] + " TotalLUTs")
        value["col"].append(i["LogicLUTs"] + " LogicLUTs")
        value["col"].append(i["LUTRAMs"] + " LUTRAMs")
        value["col"].append(i["SRLs"] + " SRLs")
        value["col"].append(i["FFs"] + " FFs")
        value["col"].append(i["RAMB36"] + " RAMB36")
        value["col"].append(i["RAMB18"] + " RAMB18")
        value["col"].append(i["DSP48Blocks"] + " DSP48Blocks")
        metric["value"].append(value)

report["metrics"].append(metric)

filename = re.sub("[^\w\.\\\/]", "_", os.environ["CI_JOB_NAME"])
print(filename)

with open('artifacts/reports/'+filename+'.yml', 'w+') as f:
    yaml.dump(report, f)
