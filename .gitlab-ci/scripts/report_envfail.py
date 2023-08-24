# Copyright 2023 Thales Silicon Security
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
# You may obtain a copy of the License at https://solderpad.org/licenses/
#
# Original Author: Côme ALLART - Thales

import report_builder as rb

metric = rb.TableStatusMetric('')
metric.add_fail('Environment failure detected. Some reports might be missing')

report = rb.Report()
report.add_metric(metric)
report.dump()
