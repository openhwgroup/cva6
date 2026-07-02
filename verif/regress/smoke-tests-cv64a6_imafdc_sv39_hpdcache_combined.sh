#!/bin/bash
# Copyright 2021 Thales DIS design services SAS
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
# You may obtain a copy of the License at https://solderpad.org/licenses/
#
# Description: Combined smoke tests for all cv64a6_imafdc_sv39_hpdcache_ targets

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
SELF="$(basename "${BASH_SOURCE[0]}")"

echo "=============================================="
echo "Running combined smoke tests for all cv64a6_imafdc_sv39_hpdcache_ targets"
echo "=============================================="

for script in "$SCRIPT_DIR"/smoke-tests-cv64a6_imafdc_sv39_hpdcache_*.sh; do
  # Skip this combined script itself
  [ "$(basename "$script")" = "$SELF" ] && continue

  echo ""
  echo "----------------------------------------------"
  echo "Running $(basename "$script")"
  echo "----------------------------------------------"
  source "$script"
done

echo ""
echo "=============================================="
echo "All smoke tests completed!"
echo "=============================================="
