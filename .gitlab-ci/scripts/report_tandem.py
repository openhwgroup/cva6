# Copyright 2024 Thales DIS France SAS
#
# Licensed under the Solderpad Hardware Licence, Version 0.51 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
# You may obtain a copy of the License at https://solderpad.org/licenses/
#
# Original Author: Valentin Thomazic (valentin.thomazic@thalesgroup.com)

import sys
import report_builder
import os
import glob
import yaml


def main():
    with_logs = os.environ.get("COLLECT_SIMU_LOGS") != None
    metrics_table = report_builder.TableStatusMetric('')

    check_provided_args()
    add_table_legend(metrics_table, with_logs)
    passed_tests_count, total_tests_count = fill_table(sys.argv[1], metrics_table, with_logs)

    if not report(metrics_table, passed_tests_count, total_tests_count):
        sys.exit(1)


def check_provided_args():
    if sys.argv[1] is None or not isinstance(sys.argv[1], str):
        print("Usage : python report_tandem.py path/to/log/dir", file=sys.stderr)
        sys.exit("No log directory provided !")


def add_table_legend(metrics_table, with_logs):
    metrics_table.add_column("TARGET", "text")
    metrics_table.add_column("ISA", "text")
    metrics_table.add_column("TEST", "text")
    metrics_table.add_column("TEST LIST", "text")
    metrics_table.add_column("SIMULATOR", "text")
    metrics_table.add_column("MISMATCHES", "text")

    if with_logs:
        metrics_table.add_column("OUTPUT", "log")
        metrics_table.add_column("TB LOGS", "log")
        metrics_table.add_column("DISASSEMBLY", "log")


def fill_table(reports_dir, metrics_table, with_logs):
    simulation_reports = glob.iglob(reports_dir + "/*.yaml")
    test_passed = 0
    test_count = 0

    for report in simulation_reports:
        test_passed += add_test_row(report, metrics_table, with_logs)
        test_count += 1
    if test_passed != test_count:
        metrics_table.fail()
    return test_passed, test_count


def add_test_row(report_file, metrics_table, with_logs):
    with open(report_file) as f:
        report = yaml.safe_load(f)
    mismatches_count = str(report["mismatches_count"]) if "mismatches_count" in report else "Not found"

    row = [report["target"], report["isa"], report["test"], report["testlist"], report["simulator"], mismatches_count]

    if with_logs:
        logs_path = "logs/" + os.environ.get("CI_JOB_ID") + "/artifacts/logs/"
        output_log = logs_path + "logfile.log.head"
        log_prefix = logs_path + report['test'] + "_" + str(report["iteration"]) + "." + report["target"] \
            if "iteration" in report else logs_path + report['test'] + "." + report["target"]
        tb_log = log_prefix + '.log.iss.head'
        disassembly = log_prefix + '.log.csv.head'

        row.append(output_log)
        row.append(tb_log)
        row.append(disassembly)

    if report["exit_cause"] == "SUCCESS" and report["exit_code"] == 0:
        metrics_table.add_pass(*row)
        return 1

    metrics_table.add_fail(*row)
    return 0


def report(metrics_table, passed_test_count, total_test_count):
    report = report_builder.Report(f'{passed_test_count}/{total_test_count}')
    report.add_metric(metrics_table)
    report.dump()
    return not report.failed


if __name__ == "__main__":
    main()
