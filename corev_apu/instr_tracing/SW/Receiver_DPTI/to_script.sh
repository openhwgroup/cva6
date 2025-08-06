#!/usr/bin/env bash
# Copyright 2025 Thales DIS design services SAS
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
# You may obtain a copy of the License at https://solderpad.org/licenses/
#
# Author: Maxime Colson - Thales
capture_fct() {
  ./Receiver_DPTI &
  PID=$!
  sleep 5
  kill -SIGINT "$PID"
  sleep 2 
}

NR_PKTS=(10 20 50 100 200)

for i in "${NR_PKTS[@]}"; do
  echo "=== $i ==="

  sed -i "s/const int NR_PKT = [0-9]\+;/const int NR_PKT = $i;/" Receiver_DPTI.cpp
  make -s 
  capture_fct >> log2.txt

done
