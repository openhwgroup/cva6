# Copyright 2022 Thales DIS France
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
# Original Author: Zbigniew CHAMSKI (zbigniew.chamski@thalesgroup.com)

dump -file "novas.vpd" -type VPD
dump -add "uvmt_cva6_tb" -depth 0
run

