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


log_path = str(sys.argv[1])
with open(log_path, 'r') as f:
    log = f.read()

def check_spyglass(spyglass_log_path):
	# Read the spyglass log files
	with open(str(sys.argv[1]), "r") as f:
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
	if len(sys.argv) != 2:
		prinf("Usage: python script <spyglass log file>")
		sys.exit(1)
	log_path = sys.argv[1]

	if not os.path.exists(log_path):
		print("Spyglass log file does not exist.")
		sys.exit(1)

	check_spyglass(log_path)
