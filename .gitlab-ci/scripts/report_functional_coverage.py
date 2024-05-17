# Copyright 2024 Thales Silicon Security
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
# You may obtain a copy of the License at https://solderpad.org/licenses/
#
# Original Author: Ayoub JALALI (ayoub.jalali@external.thalesgroup.com)

import re
import sys
import yaml
import report_builder as rb
from pprint import pprint

log_path = str(sys.argv[1])
with open(log_path, 'r') as f:
    log = f.read()

pattern = re.compile(r'\S{2,}')

def get_scores(component):
	for l in log.splitlines():
		if re.search(r'\b'+component+r'\b', l):
			line = l
	scores = pattern.findall(line)
	return [float(scores[0])]

components = [
	"ISA",
	"CSR access",
	"TRAPs",
]

score_metric = rb.TableMetric('Coverage results')
score_metric.add_value("FEATURE", "SCORE")
for component in components:
	scores = get_scores(component)
	score_metric.add_value(component, *scores)

report = rb.Report("Functional coverage")
report.add_metric(score_metric)

report.dump()

for i in range(0, 4):
	pprint(score_metric.values[i])
