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

def extract_info (summary_rpt):
	pattern = re.compile(r'(WARNING|ERROR|INFO)\s+([\w.-]+)\s+(\d+)\s+(.+)$')
	info_list = []

	with open(str(sys.argv[1]), "r") as f:
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

def print_table(info_list):
	print("{:<10} {:<20} {:<10} {:<50}".format('Severity','Rule Name', 'Count', 'Short Help'))
	print("=" * 81)

	for info in info_list:
		if info[0] in ['WARNING', 'ERROR','INFO']:
			print("{:<10} {:<20} {:<10} {:<50}".format(*info))

def check_spyglass(spyglass_log_path):
	# Read the spyglass log files
	with open(str(sys.argv[2]), "r") as f:
		log = f.read()

	# Define patterns to search for in the logs
	success_pattern = r'SpyGlass Rule Checking Complete'
	failure_pattern = r'SpyGlass Rule Checking ABORTED'

	# Check if Spyglass lint check was successful
	if re.search(success_pattern, log):
		print("Spyglass lint check completed successfully.")
	else:
		print("Spyglass lint check failed")


if __name__ == "__main__":
	if len(sys.argv) != 3:
		print("Usage: python script.py <summary_file_path>  <spyglass_log_file>")
		sys.exit(1)
	summary_rpt = sys.argv[1]
	spyglass_log_path = sys.argv[2]

	if not os.path.exists(summary_rpt):
		print("Summary file does not exist.")
		sys.exit(1)

	if not os.path.exists(spyglass_log_path):
		print("Spyglass log file does not exist.")
		sys.exit(1)

	check_spyglass(spyglass_log_path)

	info_list = extract_info(summary_rpt)

	print_table(info_list)
