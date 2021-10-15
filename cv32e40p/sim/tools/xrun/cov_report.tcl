# Copyright 2021 OpenHW Group
# Copyright 2021 Silicon Labs, Inc.
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     https://solderpad.org/licenses/
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
#
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
#

# OpenHW Coverage Report script for use with Cadence Integrated Metrics Center (IMC)

# Assumed environment variables set by Makefile/environment
# CORE_V_VERIF : Root directory of the core-v-verif checkout
# CV_CORE : Core-V core being tested (e.g. CV32E40X, CV32E40S, CV32E40P)

load -refinement $::env(CORE_V_VERIF)/$::env(CV_CORE)/sim/tools/xrun/$::env(CV_CORE)_no_pulp.hierarchy.vRefine
load -refinement $::env(CORE_V_VERIF)/$::env(CV_CORE)/sim/tools/xrun/$::env(CV_CORE)_no_pulp.auto.vRefine
load -refinement $::env(CORE_V_VERIF)/$::env(CV_CORE)/sim/tools/xrun/$::env(CV_CORE)_no_pulp.manual.vRefine

report_metrics \
    -detail \
    -view CV32E40P(openhw) \
    -block_view Uncovered \
    -expression_view Uncovered \
    -inst \
    -overwrite \
    -out cov_report
