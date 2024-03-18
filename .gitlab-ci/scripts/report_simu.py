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

pattern = re.compile(
    r'(?:\w{3}, \d{2} \w{3} \d{4} \d{2}:\d{2}:\d{2} INFO     )Compiling (.*): .*(tests\S*)$[\s\S]*?^(?:\w{3}, \d{2} \w{3} \d{4} \d{2}:\d{2}:\d{2} INFO     )Found matching ISS: (\S*)$[\s\S]*?^(?:\w{3}, \d{2} \w{3} \d{4} \d{2}:\d{2}:\d{2} INFO     )Target: (\S*)$[\s\S]*?^(?:\w{3}, \d{2} \w{3} \d{4} \d{2}:\d{2}:\d{2}(?: INFO     ))ISA (\S*)$[\s\S]*?^(?:\w{3}, \d{2} \w{3} \d{4} \d{2}:\d{2}:\d{2} (?:(?:INFO     )\[(\w*)\]: (\d*) matched(?:, (\d*) mismatch)?)|(?:^(?:\w{3}, \d{2} \w{3} \d{4} \d{2}:\d{2}:\d{2})(?: ERROR    )(\D{5})(?:.*)$))',
    re.MULTILINE)
list_of_tests = pattern.findall(log)

metric = rb.TableStatusMetric('')

metric.add_column("TARGET", "text")
metric.add_column("ISA", "text")
metric.add_column("TEST_TYPE", "text")
metric.add_column("TEST", "text")
metric.add_column("OUTPUT", "log")
metric.add_column("TB_LOGS", "log")
metric.add_column("DISASSEMBLY", "log")

job_test_pass = 0
job_test_total = 0

logsPath = "logs/" + os.environ.get("CI_JOB_ID") + "/artifacts/logs/"

for i in list_of_tests:
    job_test_total += 1

    target = i[3]
    isa = i[4]
    testsuite = i[0]
    test = i[1].split("/")[-1].split(".")[0]

    output_log = logsPath + 'logfile.log.head'
    tb_log = logsPath + test + "." + target + '.log.iss.head'
    disassembly = logsPath + test + "." + target + '.csv.head'

    col = [target, isa, testsuite, test, output_log, tb_log, disassembly]

    if i[5] == "PASSED":
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
