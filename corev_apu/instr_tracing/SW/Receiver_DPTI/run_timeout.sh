#!/usr/bin/env bash

NR_PKTS=(1 2 10 20 50 100 200)
DURATION=5

LOG_FILE="log_$(date +'%Y%m%d_%H%M%S').txt"
echo "Fichier de log : $LOG_FILE"

echo -e "NR_PKT\tThroughput (Mb/s)" > "$LOG_FILE"

capture_fct() {
    ./Receiver_DPTI &
    PID=$!
    sleep "$DURATION"
    kill -SIGINT "$PID"
    sleep 2
}

for i in "${NR_PKTS[@]}"; do
    echo "=== NR_PKT = $i ==="
    sed -i "s/const int NR_PKT = [0-9]\+;/const int NR_PKT = $i;/" Receiver_DPTI.cpp
    make > /dev/null || { echo "Compilation échouée à $i"; exit 1; }

    OUTPUT=$(capture_fct | grep -oP 'Throughput\s*:\s*\K[0-9.]+' )
    echo "$i : $OUTPUT" | tee -a "$LOG_FILE"

done

python3 script.py "$LOG_FILE"

