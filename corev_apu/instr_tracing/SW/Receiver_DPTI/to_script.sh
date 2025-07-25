#!/usr/bin/env bash

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
