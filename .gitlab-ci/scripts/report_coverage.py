# Copyright 2023 Thales Silicon Security
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
# You may obtain a copy of the License at https://solderpad.org/licenses/
#
# Original Author: Alae Eddine EZ ZEJJARI (alae-eddine.ez-zejjari@external.thalesgroup.com) – sub-contractor MU-Electronics for Thales group

import re
import sys
import yaml
import report_builder as rb
from pprint import pprint

log_cc_path = str(sys.argv[1])
with open(log_cc_path, 'r') as f:
    cc_log = f.read()

log_fc_path = str(sys.argv[2])
with open(log_fc_path, 'r') as f:
    fc_log = f.read()

pattern = re.compile(r'\S{2,}')

def get_cc_scores(component):
	for l in cc_log.splitlines():
		if re.search(r'\b'+component+r'\b', l):
			line = l
	scores = pattern.findall(line)
	return [float(score) for score in scores[0:4]]

def get_fc_scores(component):
	for l in fc_log.splitlines():
		if re.search(r'\b'+component+r'\b', l):
			line = l
	scores = pattern.findall(line)
	return [float(scores[0])]

cc_components = [
	"i_cva6",
	"commit_stage_i",
	"controller_i",
	"csr_regfile_i",
	"ex_stage_i",
	"i_frontend",
	"id_stage_i",
	"issue_stage_i",
]

fc_components = [
	"ISA",
	"CSR access",
	"TRAPs",
]

cc_score_metric = rb.TableMetric('Coverage results')
cc_score_metric.add_value("COMPONENT", "SCORE", "LINE", "COND", "TOGGLE")
for component in cc_components:
	cc_scores = get_cc_scores(component)
	cc_score_metric.add_value(component, *cc_scores)

fc_score_metric = rb.TableMetric('Functional results')
fc_score_metric.add_value("FEATURE", "SCORE")
for component in fc_components:
	fc_scores = get_fc_scores(component)
	fc_score_metric.add_value(component, *fc_scores)

coverage_score = int(get_cc_scores("i_cva6")[0])
report = rb.Report(f'{coverage_score}%')
report.add_metric(cc_score_metric)
report.add_metric(fc_score_metric)

report.dump()

print("Code Coverage Results :\n")
pprint(cc_score_metric.values)
print("\nFunctional Coverage Results :\n")
for i in range(0, 4):
	pprint(fc_score_metric.values[i])
