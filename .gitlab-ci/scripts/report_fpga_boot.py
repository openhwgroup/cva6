# Copyright 2022 Thales Silicon Security
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
# You may obtain a copy of the License at https://solderpad.org/licenses/
#
# Original Author: Guillaume Chauvon(guillaume.chauvon@thalesgroup.com)

import sys
import report_builder as rb

with open(str(sys.argv[1]), "r") as f:
    lastline = f.readlines()[-1]

with open(str(sys.argv[1]), "r") as f:
    log = f.read()

metric = rb.TableStatusMetric('Linux boot log')
if not ("Linux buildroot" in lastline and "riscv" in lastline):
    metric.add_fail(lastline)
else:
    metric.add_pass(lastline)

report = rb.Report()
report.add_metric(metric)
report.dump()
