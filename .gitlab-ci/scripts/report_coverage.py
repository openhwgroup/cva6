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

log_path = str(sys.argv[1])
with open(log_path, 'r') as f:
    log = f.read()

pattern = re.compile(r'\S{2,}')

def get_scores(component):
	for l in log.splitlines():
		if re.search(r'\b'+component+r'\b', l):
			line = l
	scores = pattern.findall(line)
	return [float(score) for score in scores[0:4]]

components = [
	"i_cva6",
	"commit_stage_i",
	"controller_i",
	"csr_regfile_i",
	"ex_stage_i",
	"gen_cache_wt.i_cache_subsystem",
	"i_frontend",
	"id_stage_i",
	"issue_stage_i",
]

score_metric = rb.TableMetric('Coverage results')
score_metric.add_value("COMPONENT", "SCORE", "LINE", "COND", "TOGGLE")
for component in components:
	scores = get_scores(component)
	score_metric.add_value(component, *scores)

coverage_score = int(get_scores("i_cva6")[0])
report = rb.Report(f'{coverage_score}%')
report.add_metric(score_metric)

report.dump()

pprint(score_metric.values)
