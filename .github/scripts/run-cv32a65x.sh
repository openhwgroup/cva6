#!/usr/bin/env bash
# SPDX-License-Identifier: Apache-2.0
# ELF runner for CVA6 cv32a65x (veri-testharness). ACT run_cmd.txt invokes:
#   run-cv32a65x.sh {debug:--trace __TRACEFILE__} --elf <elf>
#
# __TRACEFILE__ is work/.../logs/<test>.trace.log (ACT). The runner writes
# spike-dasm instruction trace there and places the FST at <test>.fst alongside it.
#
# When installed to <install-dir>/bin/ by riscv-arch-test install-cva6.sh, set:
#   export CVA6_ROOT=<install-dir>/cva6
set -euo pipefail

ROOT="${CVA6_ROOT:-$(cd "$(dirname "$0")/../.." && pwd)}"
TARGET="cv32a65x"
SPIKE_ISA="${SPIKE_ISA:-rv32imczicsr_zcb_zba_zbb_zbc_zbs}"
SIM="${ROOT}/work-ver/Variane_testharness"
LOCK_FILE="${ROOT}/work-ver/.build.lock"

export RISCV="${RISCV:-${ROOT}/tools/riscv}"
export VERILATOR_INSTALL_DIR="${VERILATOR_INSTALL_DIR:-${ROOT}/tools/verilator}"
export SPIKE_INSTALL_DIR="${SPIKE_INSTALL_DIR:-${ROOT}/tools/spike}"
export SPIKE_PATH="${SPIKE_INSTALL_DIR}/bin"
export PATH="${VERILATOR_INSTALL_DIR}/bin:${RISCV}/bin:${SPIKE_PATH}:${PATH}"

if [[ -z "${CV_SW_PREFIX:-}" ]]; then
  gcc_bin="$(ls -1 "${RISCV}/bin"/riscv*-unknown-elf-gcc 2>/dev/null | head -n1)"
  if [[ -z "${gcc_bin}" ]]; then
    echo "$(basename "$0"): no riscv*-unknown-elf-gcc found under ${RISCV}/bin" >&2
    exit 2
  fi
  CV_SW_PREFIX="$(basename "${gcc_bin}" | sed 's/-gcc$/-/')"
  export CV_SW_PREFIX
fi

elf=""
trace=""
rest=()
while [[ $# -gt 0 ]]; do
  case "$1" in
    --elf)
      if [[ $# -ge 2 && "$2" != --* ]]; then elf="$2"; shift 2; else shift; fi ;;
    --elf=*)
      elf="${1#--elf=}"; shift ;;
    --trace)
      if [[ $# -ge 2 && "$2" != --* ]]; then trace="$2"; shift 2; else shift; fi ;;
    --trace=*)
      trace="${1#--trace=}"; shift ;;
    --help|-h)
      echo "usage: $(basename "$0") [--trace file.trace.log] --elf <path>" >&2
      exit 0 ;;
    *)
      rest+=("$1"); shift ;;
  esac
done

if [[ -z "${elf}" && ${#rest[@]} -gt 0 ]]; then
  elf="${rest[-1]}"
  unset 'rest[-1]'
fi

if [[ -z "${elf}" ]]; then
  echo "usage: $(basename "$0") [--trace file.trace.log] --elf <path>" >&2
  exit 2
fi

if [[ ! -f "${elf}" ]]; then
  echo "$(basename "$0"): ELF not found: ${elf}" >&2
  exit 2
fi
elf="$(readlink -f "${elf}")"

needs_build() {
  [[ ! -x "${SIM}" ]] && return 0
  local newest_src
  newest_src="$(find "${ROOT}/core" "${ROOT}/corev_apu/tb" \
                  \( -name '*.sv' -o -name '*.v' -o -name '*.cpp' \) \
                  -newer "${SIM}" -print -quit 2>/dev/null || true)"
  [[ -n "${newest_src}" ]]
}

(
  flock -x 200
  if needs_build; then
    echo "$(basename "$0"): building veri-testharness for ${TARGET}..." >&2
    make -C "${ROOT}" verilate \
      verilator="verilator --no-timing" \
      target="${TARGET}" \
      TRACE_COMPACT=1 \
      NUM_JOBS="${NUM_JOBS:-4}"
  fi
) 200>"${LOCK_FILE}"

tohost_addr="$("${RISCV}/bin/${CV_SW_PREFIX}nm" -B "${elf}" | awk '/[[:space:]]tohost$/ {print $1; exit}')"
if [[ -z "${tohost_addr}" ]]; then
  echo "$(basename "$0"): symbol 'tohost' not found in ${elf}" >&2
  exit 2
fi

test_base="$(basename "${elf}" .elf)"
test_file="${test_base}.S"

sim_args=( "${elf}" "+tohost_addr=${tohost_addr}" "+elf_file=${elf}" )
trace_log=""
fst_file=""
if [[ -n "${trace}" ]]; then
  trace_log="${trace}"
  if [[ "${trace_log}" == *.trace.log ]]; then
    fst_file="${trace_log%.trace.log}.fst"
  else
    fst_file="${trace_log}.fst"
  fi
  mkdir -p "$(dirname "${trace_log}")" "$(dirname "${fst_file}")"
  sim_args=( -f "${fst_file}" "${sim_args[@]}" )
fi
if [[ ${#rest[@]} -gt 0 ]]; then
  sim_args+=( "${rest[@]}" )
fi

set +e
sim_out="$("${SIM}" "${sim_args[@]}" 2>&1)"
sim_rc=$?
set -e

printf '%s\n' "${sim_out}"

if [[ -n "${trace_log}" ]]; then
  rvfi_dasm="trace_rvfi_hart_00.dasm"
  if [[ -f "${rvfi_dasm}" ]]; then
    "${SPIKE_PATH}/spike-dasm" --isa="${SPIKE_ISA}" < "${rvfi_dasm}" > "${trace_log}"
    rm -f "${rvfi_dasm}"
  else
    echo "$(basename "$0"): warning: ${rvfi_dasm} not found; no instruction trace for ${trace_log}" >&2
  fi
fi

if grep -q '\*\*\* SUCCESS \*\*\*' <<<"${sim_out}"; then
  printf 'RVCP-SUMMARY: TEST PASSED - Test File "%s"\n' "${test_file}"
  exit 0
fi

if grep -q '\*\*\* FAILED \*\*\*' <<<"${sim_out}"; then
  printf 'RVCP-SUMMARY: TEST FAILED - Test File "%s"\n' "${test_file}"
  exit "${sim_rc:-1}"
fi

echo "$(basename "$0"): simulation ended without SUCCESS/FAILED marker (rc=${sim_rc})" >&2
exit "${sim_rc:-1}"
