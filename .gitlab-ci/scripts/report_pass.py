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
import os

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
          'label': "PASS",
          'metrics': [{'display_name': '',
              'sort_index': 1,
              'type': 'table_status',
              'status': "fail",
              'value': [{
                  'status': 'pass',
                  'label': 'PASS',
                  'col': ['Job completed without error. No metric extraction is configured'],
              }],
          }],
         }

pprint(report)

filename = re.sub('[^\w\.\\\/]', '_', os.environ["CI_JOB_NAME"])
print(filename)

with open('artifacts/reports/'+filename+'.yml', 'w+') as f:
    yaml.dump(report, f)

