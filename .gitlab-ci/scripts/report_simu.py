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
import os

with open(str(sys.argv[1]), 'r') as f:
    log = f.read()

with_logs = os.environ.get("COLLECT_SIMU_LOGS") != None

pattern = re.compile(
    r'(?:.*Compiling test: (.*))$[\s\S]*?(?:^.*Target: (.*)$)$[\s\S]*?(?:^.*ISA (.*)$)[\s\S]*?(?:^.*Found matching ISS: (.*)$)[\s\S]*?(?:^.*\[(PASSED|FAILED)\].*$)',
    re.MULTILINE)
list_of_tests = pattern.findall(log)

metric = rb.TableStatusMetric('')

metric.add_column("TARGET", "text")
metric.add_column("ISA", "text")
metric.add_column("TEST", "text")

if with_logs:
    metric.add_column("OUTPUT", "log")
    metric.add_column("TB LOGS", "log")
    metric.add_column("DISASSEMBLY", "log")

job_test_pass = 0
job_test_total = 0

for i in list_of_tests:
    job_test_total += 1

    target = i[1]
    isa = i[2]
    test = i[0] 

    if with_logs:
        logsPath = "logs/" + os.environ.get("CI_JOB_ID") + "/artifacts/logs/"
        output_log = logsPath + 'logfile.log'
        tb_log = logsPath + test + "." + target + '.log.iss'
        disassembly = logsPath + test + "." + target + '.csv'
        col = [target, isa, test, output_log, tb_log, disassembly]
    else:
        col = [target, isa, test]

    if i[4] == "PASSED":
        metric.add_pass(*col)
        job_test_pass += 1
    else:
        metric.add_fail(*col)

if re.search("ERROR", log) != None or job_test_total == 0:
    metric.fail()

report = rb.Report(f'{job_test_pass}/{job_test_total}')
report.add_metric(metric)
report.dump()

if report.failed:
    sys.exit(1)
