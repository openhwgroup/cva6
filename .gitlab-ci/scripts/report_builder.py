# Copyright 2022 Thales Silicon Security
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
# You may obtain a copy of the License at https://solderpad.org/licenses/
#
# Original Author: Côme Allart

"""
Helpers to build CI reports
"""

import os
import re
from datetime import datetime as dt
import yaml

class Metric:
    "A metric is a part of the body of the report"

    def __init__(self, name):
        self.name = name
        self.sort_index = None
        self.failed = False
        self.values = []

    def to_doc(self):
        "Transform to a dictionary"
        return {
            'display_name': self.name,
            'sort_index': self.sort_index,
            'type': self._t(),
            'status': "fail" if self.failed else "pass",
            'value': self._values_to_doc(),
        }

    def fail(self):
        "Mark metric as failed"
        self.failed = True

    def _values_to_doc(self):
        raise NotImplementedError()

    def _t(self):
        raise NotImplementedError()

class LogMetric(Metric):
    "Log lines"

    def add_value(self, line):
        "Insert a line in the log"
        self.values.append(line)

    def _values_to_doc(self):
        return self.values

    def _t(self):
        return 'log'

class TableMetric(Metric):
    "Table"

    def add_value(self, *col):
        "Insert a line in the table"
        self.values.append(list(col))

    def _values_to_doc(self):
        return [{'col': v} for v in self.values]

    def _t(self):
        return 'table'

class TableStatusMetric(Metric):
    "Table with status label for each line"

    class _TableStatusMetricColumn():
        def __init__(self, title, col_type):
            self.title = title
            self.col_type = col_type

        def to_doc(self):
            return { "title": self.title, "col_type": self.col_type }

    def __init__(self, name):
        super().__init__(name)
        self.columns = []

    def add_column(self, title, col_type):
        "Set the table columns titles"
        self.columns.append(TableStatusMetric._TableStatusMetricColumn(title, col_type))

    def add_pass_label(self, label, *col):
        "Insert a 'pass' line with given label in the table"
        self._add_value('pass', label, *col)

    def add_fail_label(self, label, *col):
        "Insert a 'fail' line with given label in the table"
        self._add_value('fail', label, *col)
        self.fail()

    def add_pass(self, *col):
        "Insert a 'pass' line in the table"
        self.add_pass_label("PASS", *col)

    def add_fail(self, *col):
        "Insert a 'fail' line in the table"
        self.add_fail_label("FAIL", *col)

    def to_doc(self):
        doc = super().to_doc()
        if len(self.columns) > 0:
            doc['columns'] = list(map(lambda col: col.to_doc(), self.columns))
        return doc

    def _add_value(self, status, label, *col):
        self.values.append((status, label, list(col)))

    def _values_to_doc(self):
        return [{'status': s, 'label': l, 'col': c} for (s,l,c) in self.values]

    def _t(self):
        return 'table_status'

class Report:
    "A report is the top level entity of the document"

    def __init__(self, label=None):
        self.label = label
        self.failed = False
        self.metrics = []

    def add_metric(self, *metric):
        "Add one or more metric(s) to the report body"
        for m in metric:
            if m.sort_index is None:
                if len(self.metrics) > 0:
                    m.sort_index = self.metrics[-1].sort_index + 1
                else:
                    m.sort_index = 1
            self.metrics.append(m)
            if m.failed:
                self.fail()

    def fail(self):
        "Mark report as failed"
        self.failed = True

    def to_doc(self):
        "Transform to a dictionary"
        assert len(self.metrics) > 0, "A report must have at least one metric"
        start = os.environ['CI_JOB_STARTED_AT']
        start_fmt = '%Y-%m-%dT%H:%M:%S%z'
        start = dt.strptime(start, start_fmt).timestamp()
        pass_label = "FAIL" if self.failed else "PASS"
        label = pass_label if self.label is None else self.label
        return {
            'title': os.environ["DASHBOARD_JOB_TITLE"],
            'description': os.environ["DASHBOARD_JOB_DESCRIPTION"],
            'category': os.environ["DASHBOARD_JOB_CATEGORY"],
            'sort_index': os.environ["DASHBOARD_SORT_INDEX"],
            'job_id': os.environ["CI_JOB_ID"],
            'job_url': os.environ["CI_JOB_URL"],
            'job_stage_name': os.environ["CI_JOB_STAGE"],
            'job_started_at': int(start),
            'job_end_at': int(dt.now().timestamp()),
            'token': 'YC' + str(dt.now().timestamp()).replace('.', ''),
            'status': "fail" if self.failed else "pass",
            'metrics': [m.to_doc() for m in self.metrics],
            'label': label,
        }

    def dump(self, path=None):
        """
        Create report file

        By default the output path is build from $CI_JOB_NAME
        """
        if path is None:
            filename = re.sub(r'[^\w\.\\\/]', '_', os.environ["CI_JOB_NAME"])
            path = 'artifacts/reports/'+filename+'.yml'
        with open(path, 'w') as f:
            yaml.dump(self.to_doc(), f)
