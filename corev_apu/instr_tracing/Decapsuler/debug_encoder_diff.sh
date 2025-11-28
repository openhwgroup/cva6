#!/bin/bash
# Copyright 2025 Thales DIS design services SAS
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
# You may obtain a copy of the License at https://solderpad.org/licenses/
#
# Author: Maxime Colson - Thales

exit_error() {
    echo "$1" >&2
    exit ${2:-1}
}

if [ "$#" -ne 1 ]; then
    exit_error "Usage: $0 <executable>" 2
fi

exe="$1"
base=$(basename "$exe" .o)

#TODO 