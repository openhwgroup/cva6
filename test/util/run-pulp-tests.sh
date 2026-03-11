#!/bin/bash
# Runs programs from sw/out on an already built model, one after the other, and
# reports which passed. Every test runs even after one fails. The output of each
# test's `make <sim>-run` goes to <sim>/logs/pulp-tests/<test>.log, and the test
# passed if that log reports SIMULATION PASSED. It writes summary.txt there, one
# PASS or FAIL line per test, prints the end of each failing log, and exits
# non-zero unless every test passed.
#
#   make -C test vsim-build CVA6_CONFIG=<cfg>
#   ./test/util/run-pulp-tests.sh vsim hello clic_simple
#
#   make -C test verilator-build CVA6_CONFIG=<cfg>
#   ./test/util/run-pulp-tests.sh verilator hello clic_simple
#
# MAX_CYCLES, like the other variables of test/Makefile, reaches the simulation
# through the environment.
#
# SPDX-License-Identifier: Apache-2.0

set -uo pipefail

export MAX_CYCLES=${MAX_CYCLES:-750000}

scriptdir="$(dirname -- "${BASH_SOURCE[0]}")"
testdir="$(realpath -m "${scriptdir}/..")"

sim="${1:-}"
if [[ "${sim}" != @(vsim|verilator) || $# -lt 2 ]]; then
    echo "usage: $0 vsim|verilator <test>..." >&2
    exit 1
fi
shift

logdir="${testdir}/${sim}/logs/pulp-tests"
summary="${logdir}/summary.txt"
mkdir -p "${logdir}"
: > "${summary}"

for t in "$@"; do
    hex="${testdir}/sw/out/${t}.hex"
    log="${logdir}/${t}.log"
    if [ -f "${hex}" ]; then
        make -C "${testdir}" "${sim}-run" HEXFILE="${hex}" > "${log}" 2>&1
    else
        echo "error: ${hex} does not exist" > "${log}"
    fi
    if grep -q "SIMULATION PASSED" "${log}"; then
        echo "PASS ${t}" | tee -a "${summary}"
    else
        echo "FAIL ${t}" | tee -a "${summary}"
    fi
done

failed=$(grep -c '^FAIL' "${summary}")
for t in $(sed -n 's/^FAIL //p' "${summary}"); do
    echo
    echo "=== FAIL ${t}: last 50 lines of ${sim}/logs/pulp-tests/${t}.log"
    tail -n 50 "${logdir}/${t}.log"
done
echo "---"
echo "pulp-tests: $(( $# - failed )) of $# passed on ${sim}"
[ "${failed}" -eq 0 ]
