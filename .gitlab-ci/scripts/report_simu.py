# Copyright 2022 Thales Silicon Security
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
# You may obtain a copy of the License at https://solderpad.org/licenses/
#
# Original Author: Yannick Casamatta (yannick.casamatta@thalesgroup.com)

import sys
import re
import report_builder as rb

with open(str(sys.argv[1]), 'r') as f:
    log = f.read()

pattern = re.compile(
    "^(?:\w{3}, \d{2} \w{3} \d{4} \d{2}:\d{2}:\d{2} INFO     )?Compiling (.*) : .*(tests\S*)$[\s\S]*?^(?:\w{3}, \d{2} \w{3} \d{4} \d{2}:\d{2}:\d{2} INFO     )?Found matching ISS: (\S*)$[\s\S]*?^(?:\w{3}, \d{2} \w{3} \d{4} \d{2}:\d{2}:\d{2} INFO     )?ISA (\S*)$[\s\S]*?^(?:\w{3}, \d{2} \w{3} \d{4} \d{2}:\d{2}:\d{2} INFO     )?\[(\w*)\]: (\d*) matched(?:, (\d*) mismatch)?$",
    re.MULTILINE)
list_of_tests = pattern.findall(log)

metric = rb.TableStatusMetric('')

job_test_pass = 0
job_test_total = 0
for i in list_of_tests:
    job_test_total += 1
    col = [i[3], i[2], i[0], i[1]] # isa testbench testsuite test
    if i[4] == "PASSED":
        metric.add_pass(*col)
        job_test_pass += 1
    else:
        metric.add_fail(*col)

if job_test_total == 0:
    metric.fail()

report = rb.Report(f'{job_test_pass}/{job_test_total}')
report.add_metric(metric)
report.dump()
