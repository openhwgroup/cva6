#!/bin/bash
# Runs the RISC-V Architectural Certification Tests on the testbench, in
# parallel, and reports which passed.
#
# Each ACT ELF is self-checking: it ends by writing the EOC register with a pass
# or fail code (see sw/arch-test/rvmodel_macros.h), so the testbench's own
# pass/fail protocol is the verdict and nothing has to parse a signature.
# Failures listed in sw/arch-test/waivers.txt are reported as WAIVED instead.
#
#   make -C test/sw arch-test CVA6_CONFIG=<cfg>     # generate the ELFs
#   make -C test verilator-build CVA6_CONFIG=<cfg>  # the same <cfg>
#   ./util/run-arch-tests.sh                        # checks the two agree
#
# SPDX-License-Identifier: Apache-2.0

set -uo pipefail

NJOBS=${NJOBS:-8}
MAX_CYCLES=${MAX_CYCLES:-2000000}

scriptdir="$(dirname -- "${BASH_SOURCE[0]}")"
export testdir="$(realpath -m "${scriptdir}/..")"
export simbin="$(realpath -m "${testdir}/verilator/build/Vtest")"
export logdir="$(realpath -m "${testdir}/verilator/logs/arch-test")"
export MAX_CYCLES

# summary.txt is written only once a run is complete, so its presence means the
# run is over. Remove an earlier run's first, so that none survives this run
# stopping early.
rm -f "${logdir}/summary.txt"

export SIM_ARGS="${SIM_ARGS:-}"

if [ ! -x "${simbin}" ]; then
    echo "error: ${simbin} not built" >&2
    exit 1
fi

# The ELFs must be for the configuration the model was built for: ACT bakes the
# expected results in, so an ELF is only valid for its own configuration. The
# model's configuration is the TARGET_ define bender put in its file list.
model_config="$(grep -o -m1 'TARGET_CV[0-9A-Z_]*' "${testdir}/verilator/cva6tb.flist" 2>/dev/null \
                | sed 's/^TARGET_//' | tr '[:upper:]' '[:lower:]')"
if [ -z "${model_config}" ]; then
    echo "error: cannot tell which configuration verilator/cva6tb.flist was built for" >&2
    exit 1
fi
if [ -n "${ACT_CONFIG:-}" ] && [ "${ACT_CONFIG}" != "${model_config}" ]; then
    echo "error: ACT_CONFIG=${ACT_CONFIG} but the model is built for ${model_config}" >&2
    exit 1
fi
ACT_CONFIG="${model_config}"
ELFDIR="${ELFDIR:-${testdir}/sw/deps/riscv-arch-test/work/${ACT_CONFIG}/elfs}"
if [ ! -d "${ELFDIR}" ]; then
    echo "error: no ACT ELFs for ${ACT_CONFIG} under ${ELFDIR}; run" \
         "'make -C test/sw arch-test CVA6_CONFIG=${ACT_CONFIG}' first" >&2
    exit 1
fi

run_one () {
    hex="$1"
    t="$(basename "${hex}" .hex)"
    log="${logdir}/${t}.log"
    # An ACT test reports success by writing the EOC register with code 0, which
    # is the testbench default, so no +RetCodeSuccess is needed.
    ${simbin} +binary="${hex}" +MaxCycles="${MAX_CYCLES}" ${SIM_ARGS} > "${log}" 2>&1
    if grep -q "SIMULATION PASSED" "${log}"; then
        echo "PASS ${t}"
    else
        echo "FAIL ${t}"
    fi
}
export -f run_one

mkdir -p "${logdir}"
mapfile -t hexes < <(find "${ELFDIR}" -name '*.hex' | sort)
if [ ${#hexes[@]} -eq 0 ]; then
    echo "error: no .hex under ${ELFDIR}; run 'make -C test/sw arch-test'" >&2
    exit 1
fi
echo "arch-test: running ${#hexes[@]} ${ACT_CONFIG} ELFs from ${ELFDIR}"

# Known failures that are not core bugs, for this configuration: test name ->
# reason. A waived test still runs; it just does not count against the verdict.
declare -A waiver
waivers_file="${WAIVERS:-${testdir}/sw/arch-test/waivers.txt}"
if [ -f "${waivers_file}" ]; then
    while read -r name configs reason; do
        case "${name}" in ''|\#*) continue ;; esac
        if [ "${configs}" = "*" ] || [[ ",${configs}," == *",${ACT_CONFIG},"* ]]; then
            waiver["${name}"]="${reason}"
        fi
    done < "${waivers_file}"
fi

# Each verdict is printed as its test finishes, waivers applied, and its raw
# PASS or FAIL line lands in results.txt.
pass=0; fail=0; waived=0; unexpected=0
declare -A seen
: > "${logdir}/results.txt"
: > "${logdir}/summary.txt.tmp"
while read -r verdict t; do
    seen["${t}"]=1
    echo "${verdict} ${t}" >> "${logdir}/results.txt"
    if [ -z "${waiver[${t}]+x}" ]; then
        line="${verdict} ${t}"
        if [ "${verdict}" = PASS ]; then pass=$((pass + 1)); else fail=$((fail + 1)); fi
    elif [ "${verdict}" = FAIL ]; then
        line="WAIVED ${t} :: ${waiver[${t}]}"
        waived=$((waived + 1))
    else
        # A waiver that no longer fails must not linger and hide a regression later.
        line="UNEXPECTED-PASS ${t} :: waived but passed; remove it from ${waivers_file}"
        unexpected=$((unexpected + 1))
    fi
    echo "${line}" >> "${logdir}/summary.txt.tmp"
    echo "[${#seen[@]}/${#hexes[@]}] ${line}"
done < <(printf '%s\n' "${hexes[@]}" | xargs -n1 -P "${NJOBS}" bash -c 'run_one "$1"' _)
sort -k2 "${logdir}/summary.txt.tmp" > "${logdir}/summary.txt"
rm "${logdir}/summary.txt.tmp"

# The end of the first failing logs. Many failures usually share one cause.
mapfile -t failed < <(sed -n 's/^FAIL //p' "${logdir}/summary.txt")
for t in "${failed[@]:0:10}"; do
    echo
    echo "=== FAIL ${t}: last 20 lines of ${logdir}/${t}.log"
    tail -n 20 "${logdir}/${t}.log"
done
if [ ${#failed[@]} -gt 10 ]; then
    echo
    echo "... and $(( ${#failed[@]} - 10 )) more failing tests"
fi

echo "---"
grep -E '^(FAIL|WAIVED|UNEXPECTED-PASS)' "${logdir}/summary.txt" || true
for t in "${!waiver[@]}"; do
    [ -n "${seen[${t}]+x}" ] || echo "note: waiver for ${t} matched no test in this run"
done
echo "---"
extra=""
[ "${unexpected}" -gt 0 ] && extra=", ${unexpected} unexpectedly passed"
echo "arch-test: ${pass} passed, ${fail} failed, ${waived} waived${extra} of $(( pass + fail + waived + unexpected ))"
echo "summary in ${logdir}/summary.txt"
[ "${fail}" -eq 0 ] && [ "${unexpected}" -eq 0 ]
