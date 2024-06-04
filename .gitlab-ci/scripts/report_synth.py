# Copyright 2022 Thales Silicon Security
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
# You may obtain a copy of the License at https://solderpad.org/licenses/
#
# Original Author: Yannick Casamatta (yannick.casamatta@thalesgroup.com)

import re
import sys
import os
import yaml
import report_builder as rb

log_path = str(sys.argv[1])
with open(log_path, 'r') as f:
    log = f.read()

with open(str(sys.argv[2]), 'r') as f:
    synthesis_log = f.read()

ignored_warning = ["RM-Error", "TFCHK-014", "TFCHK-012", "TFCHK-049",
                    "MV-021", "MV-028", "TLUP-004", "TLUP-005",
                    "TIM-164", "PWR-890", "PWR-80", "OPT-1413"]
kgate_ratio = int(os.environ["NAND2_AREA"])
path_re = r'^pd/synth/cva6_([^/]+)'
with open(".gitlab-ci/expected_synth.yml", "r") as f:
    expected = yaml.safe_load(f)

#Compile & elaborate log:
log_metric = rb.LogMetric('Synthesis full log')
error_log = []
warning_log = []
for line in synthesis_log.splitlines():
    if any (el in line for el in ignored_warning):
        continue
    if os.environ['FOUNDRY_PATH'] in line:
        continue
    if os.environ['TECH_NAME'] in line:
        continue
    if 'Error: ' in line:
        error_log.append(line)
    if 'Warning: ' in line:
        warning_log.append(line)
log_metric.values = error_log + warning_log

# Area repport:
pattern = re.compile(
    "^(Combinational area|Buf/Inv area|Noncombinational area|Macro/Black Box area):\ *(\d*\.\d*)$",
    re.MULTILINE)
global_val = pattern.findall(log)

pattern = re.compile(
    "^(\w*(?:\/\w*){0,2})\ *(\d*\.\d*)\ *(\d*\.\d*)\ *(\d*\.\d*)\ *(\d*\.\d*)\ *(\d*\.\d*)\ *(\w*)$",
    re.MULTILINE)
hier = pattern.findall(log)

total_area = float(hier[0][1])

result_metric = rb.TableMetric('Global results')
kgates = total_area / kgate_ratio
gates = int(kgates * 1000)
result_metric.add_value("Total area", f'{gates} Gates')
for i in global_val:
    rel_area = 0 if total_area == 0 else int(float(i[1]) / total_area * 100)
    result_metric.add_value(i[0], f'{rel_area} %')
match = re.match(path_re, log_path)
if match:
    target = match.group(1)
    if target in expected:
        diff = gates - expected[target]['gates']
        if abs(diff) >= 500:
            result_metric.fail()
    else:
        raise Exception(f"unexpected target: {target}")
else:
    raise Exception(f"unexpected file name: {log_path}")


hier_metric = rb.TableMetric('Hierarchies details')
for i in hier:
    hier_metric.add_value(
        i[0],  # hier
        f"{int(float(i[1])/kgate_ratio)} kGates",  # area
        f"{int(float(i[2]))} %",  # %
        #int(float(i[3]))/int(float(i[1])*100),  # % combi
        #int(float(i[4]))/int(float(i[1])*100),  # % reg
        #int(float(i[5]))/int(float(i[1])*100),  # % black box
    )

report = rb.Report(f'{int(kgates)} kGates')
report.add_metric(result_metric, hier_metric, log_metric)

report.dump()
