# Copyright 2022 Thales DIS design services SAS
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

global_pass = "pass"

report = {'title': sys.argv[1],
          'description': sys.argv[2],
          'token': 'YC' + str(datetime.datetime.now().timestamp()).replace('.', ''),
          'status': "pass",
          'label': "PASS",
          'metrics': [{'display_name': '',
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

filename = re.sub('[^\w\.\\\/]', '_', sys.argv[3])
print(filename)

with open(filename, 'w+') as f:
    yaml.dump(report, f)

