# Copyright 2022 Thales Silicon Security
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
# You may obtain a copy of the License at https://solderpad.org/licenses/
#
# Original Author: Côme Allart

import sys
import report_builder as rb

path = None
mode = None
iterations = None

for arg in sys.argv[1:]:
    if arg == '--dhrystone':
        mode = 'dhrystone'
        iterations = 500
    else:
        path = arg

with open(path, 'r') as f:
    log = [l.strip() for l in f.readlines()]

stopwatch = []
for index, line in enumerate(log):
    if line.split()[-1] == 'mcycle':
        stopwatch.append(int(log[index + 1].split()[-1], 16))
# There might be > 2 matches, we use the two at the center
N = len(stopwatch)
assert N % 2 == 0
cycles = stopwatch[N//2] - stopwatch[N//2-1]

score_metric = rb.TableMetric('Performance results')
score_metric.add_value('cycles', cycles)

if mode is not None:
    ipmhz = iterations * 1000000 / cycles
    if mode == 'dhrystone':
        score_metric.add_value('Dhrystone/MHz', ipmhz)
        score_metric.add_value('DMIPS/MHz', ipmhz / 1757)

report = rb.Report(f'{cycles//1000} kCycles')
report.add_metric(score_metric)
report.dump()
