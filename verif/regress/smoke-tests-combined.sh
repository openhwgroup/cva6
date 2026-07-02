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
echo "Running combined smoke tests for all targets"
echo "=============================================="

echo ""
echo "----------------------------------------------"
echo "Running smoke-tests-cv32a60x.sh"
echo "----------------------------------------------"
source "$SCRIPT_DIR/smoke-tests-cv32a60x.sh"

echo ""
echo "----------------------------------------------"
echo "Running smoke-tests-cv32a60x_axi.sh"
echo "----------------------------------------------"
source "$SCRIPT_DIR/smoke-tests-cv32a60x_axi.sh"

echo ""
echo "----------------------------------------------"
echo "Running smoke-tests-cv32a65x.sh"
echo "----------------------------------------------"
source "$SCRIPT_DIR/smoke-tests-cv32a65x.sh"

echo ""
echo "----------------------------------------------"
echo "Running smoke-tests-cv32a65x_axi.sh"
echo "----------------------------------------------"
source "$SCRIPT_DIR/smoke-tests-cv32a65x_axi.sh"

echo ""
echo "----------------------------------------------"
echo "Running smoke-tests-cv32a65x_noPMP.sh"
echo "----------------------------------------------"
source "$SCRIPT_DIR/smoke-tests-cv32a65x_noPMP.sh"

echo ""
echo "----------------------------------------------"
echo "Running smoke-tests-cv32a65x_noPMP_axi.sh"
echo "----------------------------------------------"
source "$SCRIPT_DIR/smoke-tests-cv32a65x_noPMP_axi.sh"

echo ""
echo "----------------------------------------------"
echo "Running smoke-tests-cv32a65x_noPMP_noSuperScalar.sh"
echo "----------------------------------------------"
source "$SCRIPT_DIR/smoke-tests-cv32a65x_noPMP_noSuperScalar.sh"

echo ""
echo "----------------------------------------------"
echo "Running smoke-tests-cv32a65x_noPMP_noSuperScalar_axi.sh"
echo "----------------------------------------------"
source "$SCRIPT_DIR/smoke-tests-cv32a65x_noPMP_noSuperScalar_axi.sh"

echo ""
echo "----------------------------------------------"
echo "Running smoke-tests-cv32a60x_zcmt_pmp.sh"
echo "----------------------------------------------"
source "$SCRIPT_DIR/smoke-tests-cv32a60x_zcmt_pmp.sh"

echo ""
echo "----------------------------------------------"
echo "Running smoke-tests-cv32a60x_zcmt_pmp_axi.sh"
echo "----------------------------------------------"
source "$SCRIPT_DIR/smoke-tests-cv32a60x_zcmt_pmp_axi.sh"

echo ""
echo "----------------------------------------------"
echo "Running smoke-tests-cv32a6_imac_sv32.sh"
echo "----------------------------------------------"
source "$SCRIPT_DIR/smoke-tests-cv32a6_imac_sv32.sh"

echo ""
echo "----------------------------------------------"
echo "Running smoke-tests-cv32a6_imac_sv32_obi.sh"
echo "----------------------------------------------"
source "$SCRIPT_DIR/smoke-tests-cv32a6_imac_sv32_obi.sh"

echo ""
echo "----------------------------------------------"
echo "Running smoke-tests-cv32a65x_sv32.sh"
echo "----------------------------------------------"
source "$SCRIPT_DIR/smoke-tests-cv32a65x_sv32.sh"

echo ""
echo "----------------------------------------------"
echo "Running smoke-tests-cv32a65x_sv32_axi.sh"
echo "----------------------------------------------"
source "$SCRIPT_DIR/smoke-tests-cv32a65x_sv32_axi.sh"

echo ""
echo "=============================================="
echo "All smoke tests completed!"
echo "=============================================="