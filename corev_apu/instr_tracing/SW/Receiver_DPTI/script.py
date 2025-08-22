# Copyright 2025 Thales DIS design services SAS
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
# You may obtain a copy of the License at https://solderpad.org/licenses/
#
# Author: Maxime Colson - Thales

#Script to plot data from run_timeout.sh aquisition with receiver

import sys
import matplotlib.pyplot as plt

def parse_log(file_path):
    nr_pkts = []
    throughputs = []
    with open(file_path) as f:
        for line in f:
            line = line.strip()
            if not line or ':' not in line or line.startswith('NR_PKT'):
                continue
            try:
                pkt_str, tp_str = line.split(':')
                pkt = int(pkt_str.strip())
                tp = float(tp_str.strip())
                nr_pkts.append(pkt)
                throughputs.append(tp)
            except ValueError:
                continue
    return nr_pkts, throughputs

def main():
    if len(sys.argv) != 2:
        print(f"Usage: {sys.argv[0]} <log_file>")
        sys.exit(1)

    log_file = sys.argv[1]
    nr_pkts, throughputs = parse_log(log_file)

    if not nr_pkts:
        print("Aucune donnée valide trouvée dans le fichier.")
        sys.exit(1)

    print("\nNR_PKT\tThroughput (Mb/s)")
    for pkt, tp in zip(nr_pkts, throughputs):
        print(f"{pkt}\t{tp}")

    plt.figure()
    plt.plot(nr_pkts, throughputs, marker='o')
    plt.xlabel("Nombre de paquets (NR_PKT)")
    plt.ylabel("Throughput (Mb/s)")
    plt.title("NR_PKT vs Throughput")
    plt.grid(True)
    plt.tight_layout()
    plt.show()

if __name__ == "__main__":
    main()
