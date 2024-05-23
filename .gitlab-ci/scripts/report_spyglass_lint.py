# Copyright 2024 Thales DIS France SAS
# Licensed under the Solderpad Hardware Licence, Version 2.1 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
# You may obtain a copy of the License at https://solderpad.org/licenses/
#
# python script for Spyglass lint report
#
# Original Author: Asmaa Kassimi (asmaa.kassimi@external.thalesgroup.com) - Thales
#

import os
import re
import sys
import yaml

import report_builder as rb
from pprint import pprint

def extract_info (summary_rpt_ref):
	pattern = re.compile(r'(WARNING|ERROR|INFO)\s+(\S+)\s+(\d+)\s+(.+)$')
	info_list = []

	with open(summary_rpt_ref, "r") as f:
		lines = f.readlines()

	for line in lines:
		match = pattern.match(line)
		if match:
			severity = match.group(1)
			rule_name = match.group(2)
			count = match.group(3)
			short_help = match.group(4)

			info_list.append((severity, rule_name, count, short_help))

	return info_list

def compare_summaries(baseline_info, new_info):
	baseline_dict={(severity, rule_name):(count,short_help) for severity, rule_name, count, short_help in baseline_info}
	new_dict={(severity, rule_name):(count,short_help) for severity, rule_name, count, short_help in new_info}

	comparison_results = []

	for key in baseline_dict.keys():
		if key not in new_dict:
			comparison_results.append((*key, baseline_dict[key][0], baseline_dict[key][1], "PASS", "Deleted"))

	for key in new_dict.keys():
		if key not in baseline_dict:
			comparison_results.append((*key, new_dict[key][0], new_dict[key][1], "FAIL", "NEW"))

	for key in new_dict.keys():
		if key in baseline_dict:
			if new_dict[key][0] == baseline_dict[key][0]:
				comparison_results.append((*key, new_dict[key][0], new_dict[key][1], "PASS", "SAME"))
			else:
				comparison_results.append((*key, new_dict[key][0], new_dict[key][1], "FAIL", f"Count changed from {baseline_dict[key][0]} to {new_dict[key][0]}"))
	return  comparison_results

def print_comparison_table(comparison_results):
	print("{:<10} {:<25} {:<10} {:<50} {:<5} {:<10}".format('Severity','Rule Name', 'Count', 'Short Help', 'Check', 'Status'))
	print("=" * 135)

	for result in comparison_results:
		print("{:<10} {:<25} {:<10} {:<50} {:<5} {:<10} ".format(*result))


if __name__ == "__main__":
	if len(sys.argv) != 3:
		print("Usage: python script.py <summary_ref_file> <summary_file_path>")
		sys.exit(1)
	summary_rpt_ref = sys.argv[1]
	summary_rpt = sys.argv[2]

	baseline_info = extract_info(summary_rpt_ref)

	new_info = extract_info(summary_rpt)

	comparison_results = compare_summaries(baseline_info, new_info)

	print_comparison_table(comparison_results)
