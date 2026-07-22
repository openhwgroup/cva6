#!/bin/bash
# Copyright 2021 Thales DIS design services SAS
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
# You may obtain a copy of the License at https://solderpad.org/licenses/
#
# Description: Combined smoke tests for all cv32a6x targets

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

echo "=============================================="
echo "Running combined pmp tests for all targets"
echo "=============================================="

echo ""
echo "----------------------------------------------"
echo "Running pmp_cv32a60x-tests.sh"
echo "----------------------------------------------"
source "$SCRIPT_DIR/pmp_cv32a60x_tests.sh"

echo ""
echo "----------------------------------------------"
echo "Running pmp_cv32a65x-tests.sh"
echo "----------------------------------------------"
source "$SCRIPT_DIR/pmp_cv32a65x_tests.sh"

echo ""
echo "----------------------------------------------"
echo "Running pmp_cv32a65x_sv32_tests.sh"
echo "----------------------------------------------"
source "$SCRIPT_DIR/pmp_cv32a65x_sv32_tests.sh"

echo ""
echo "----------------------------------------------"
echo "Running pmp_cv32a_imac_sv32_tests.sh"
echo "----------------------------------------------"
source "$SCRIPT_DIR/pmp_cv32a_imac_sv32_tests.sh"