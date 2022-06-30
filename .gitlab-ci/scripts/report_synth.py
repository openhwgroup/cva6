# Copyright 2022 Thales Silicon Security
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
# You may obtain a copy of the License at https://solderpad.org/licenses/
#
# Original Author: Yannick Casamatta (yannick.casamatta@thalesgroup.com)

import re
from pprint import pprint
import yaml
import datetime
import sys
import os

with open(str(sys.argv[1]), 'r') as f:
    log = f.read()

with open(str(sys.argv[2]), 'r') as f:
    synthesis_log = f.read()

kgate_ratio = int(os.environ["NAND2_AREA"])

global_pass = "pass"

report = {'title': os.environ["DASHBOARD_JOB_TITLE"],
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

#Compile & elaborate log:

metric = {'display_name': 'Synthesis full log',
          'sort_index': 3,
          'type': 'log',
          'status': "pass",
          'value': []
         }

error_log = []
warning_log = []
for line in synthesis_log.splitlines():
    if os.environ['FOUNDRY_PATH'] in line:
        continue
    if os.environ['TECH_NAME'] in line:
        continue
    if 'Error: ' in line:
        error_log.append(line)
    if 'Warning: ' in line:
        warning_log.append(line)

metric['value'] = error_log + warning_log

report['metrics'].append(metric)


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


metric = {'display_name': 'Global results',
          'sort_index': 1,
          'type': 'table',
          'status': "pass",
          'value': []
         }

value = {'col': []}
value['col'].append("Total area")  # Name
value['col'].append(f'{int(total_area/kgate_ratio)} kGates')  # value
metric['value'].append(value)

for i in global_val:
    value = {'col': []}
    value['col'].append(i[0])  # Name
    if total_area == 0: 
        value['col'].append('0 %')
    else:
        value['col'].append(f'{int(float((i[1]))/total_area*100)} %')  # value
        
    metric['value'].append(value)

report['metrics'].append(metric)

metric = {'display_name': 'Hierarchies details',
          'sort_index': 2,
          'type': 'table',
          'status': "pass",
          'value': []
         }

for i in hier:
    value = {}
    value['col'] = []
    value['col'].append(i[0])  # hier
    value['col'].append(f"{int(float(i[1])/kgate_ratio)} kGates")  # area
    value['col'].append(f"{int(float(i[2]))} %")  # %
    #value['col'].append(int(float(i[3]))/int(float(i[1])*100))  # % combi
    #value['col'].append(int(float(i[4]))/int(float(i[1])*100))  # % reg
    #value['col'].append(int(float(i[5]))/int(float(i[1])*100))  # % black box
    metric['value'].append(value)

report['metrics'].append(metric)

report['label'] = f'{int(total_area/kgate_ratio)} kGates'

pprint(report)

filename = re.sub('[^\w\.\\\/]', '_', os.environ["CI_JOB_NAME"])
print(filename)

with open('artifacts/reports/'+filename+'.yml', 'w+') as f:
    yaml.dump(report, f)
