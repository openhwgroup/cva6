#!/usr/bin/env bash
# Copyright 2026 OpenHW Group
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

set -o pipefail

RUN_LOG="$(pwd)/ci-results/run.log"
FAILURE_SUMMARY="$(pwd)/ci-results/failure_summary.log"
EXIT_CODE_FILE="$(pwd)/ci-results/exit_code"

mkdir -p ci-results
: > "${RUN_LOG}"
: > "${FAILURE_SUMMARY}"
echo "1" > "${EXIT_CODE_FILE}"

TIER_NAME="${TIER_NAME:-Tier}"
TIER_MODE="${TIER_MODE:-script}"
TIER_CONFIG="${TIER_CONFIG:?TIER_CONFIG is required}"
TIER_TESTCASE="${TIER_TESTCASE:?TIER_TESTCASE is required}"
TIER_SIMULATOR="${TIER_SIMULATOR:?TIER_SIMULATOR is required}"
TIER_INSTALL_SCRIPT="${TIER_INSTALL_SCRIPT:-}"
TIER_TESTLIST="${TIER_TESTLIST:-}"
TIER_TEST_NAME="${TIER_TEST_NAME:-}"
TIER_LINKER="${TIER_LINKER:-}"
TIER_HWCONFIG_OPTS="${TIER_HWCONFIG_OPTS:-}"

log_info() {
  echo "$*" | tee -a "${RUN_LOG}"
}

run_logged() {
  set +e
  "$@" > >(tee -a "${RUN_LOG}") 2>&1
  local cmd_rc=$?
  return "${cmd_rc}"
}

source_logged() {
  local script_path="$1"
  set +e
  # shellcheck source=/dev/null
  source "${script_path}" > >(tee -a "${RUN_LOG}") 2>&1
  local source_rc=$?
  return "${source_rc}"
}

record_rc() {
  local step_rc="$1"
  if [ "${step_rc}" -ne 0 ] && [ "${rc}" -eq 0 ]; then
    rc="${step_rc}"
  fi
}

append_failure() {
  echo "$*" | tee -a "${FAILURE_SUMMARY}" >&2
}

collect_reports() {
  find verif/sim -name "iss_regr.log" -exec cp {} ci-results/ \; 2>/dev/null || true
}

scan_for_failures() {
  local matches
  local -a scan_files=("${RUN_LOG}")

  while IFS= read -r -d '' file_path; do
    scan_files+=("${file_path}")
  done < <(
    find verif/sim -type f \
      \( -name "*.log" -o -name "*.txt" -o -name "iss_regr.log" \) \
      -print0 2>/dev/null || true
  )

  matches="$(
    grep -HnE \
      "\\[FAILED\\]|SIMULATION FAILED|(^|[^0-9])[1-9][0-9]* FAILED|ERROR return code:|bad syscall|unrecognized opcode|extension .* required|make(\\[[0-9]+\\])?: \\*\\*\\*.*Error|terminate called|Traceback \\(most recent call last\\)" \
      "${scan_files[@]}" 2>/dev/null || true
  )"

  if [ -n "${matches}" ]; then
    append_failure "ERROR: ${TIER_NAME} job reported success, but failure patterns were found in logs."
    echo "${matches}" | tee -a "${FAILURE_SUMMARY}" >&2
    return 1
  fi

  return 0
}

scan_iss_traces() {
  local matches=""
  local critical_patterns
  critical_patterns="ERROR return code:|bad syscall|unrecognized opcode|extension .* required|terminate called|Traceback \\(most recent call last\\)"

  while IFS= read -r -d '' file_path; do
    local critical_matches
    local last_status

    critical_matches="$(grep -HnE "${critical_patterns}" "${file_path}" 2>/dev/null || true)"
    if [ -n "${critical_matches}" ]; then
      matches+="${critical_matches}"$'\n'
    fi

    last_status="$(
      grep -nE "\\*\\*\\*[[:space:]]+(FAILED|SUCCESS)[[:space:]]+\\*\\*\\*|SIMULATION FAILED" "${file_path}" 2>/dev/null | tail -n 1 || true
    )"
    if [[ -n "${last_status}" && "${last_status}" != *"SUCCESS"* ]]; then
      matches+="${file_path}:${last_status}"$'\n'
    fi
  done < <(find verif/sim -type f -name "*.iss" -print0 2>/dev/null || true)

  if [ -n "${matches}" ]; then
    append_failure "ERROR: ${TIER_NAME} job reported success, but ISS trace failure patterns were found."
    printf "%s" "${matches}" | tee -a "${FAILURE_SUMMARY}" >&2
    return 1
  fi

  return 0
}

rc=0

log_info "Running ${TIER_NAME}: ${TIER_CONFIG} / ${TIER_TESTCASE} (${TIER_MODE})"

source_logged verif/sim/setup-env.sh
record_rc "$?"

if [ "${rc}" -eq 0 ]; then
  if [ "${TIER_MODE}" = "testlist" ]; then
    if [[ "${TIER_SIMULATOR}" == *"veri-testharness"* ]]; then
      source_logged verif/regress/install-verilator.sh
      record_rc "$?"
    fi

    if [ "${rc}" -eq 0 ]; then
      source_logged verif/regress/install-spike.sh
      record_rc "$?"
    fi

    if [ "${rc}" -eq 0 ] && [ -n "${TIER_INSTALL_SCRIPT}" ]; then
      source_logged "verif/regress/${TIER_INSTALL_SCRIPT}.sh"
      record_rc "$?"
    fi

    if [ "${rc}" -eq 0 ]; then
      cva6_cmd=(
        python3 cva6.py
        "--testlist=${TIER_TESTLIST}"
        --target "${TIER_CONFIG}"
        --iss_yaml=cva6.yaml
        "--iss=${TIER_SIMULATOR}"
        "--issrun_opts=+tb_performance_mode+debug_disable=1+UVM_VERBOSITY=UVM_NONE"
      )

      if [ -n "${TIER_LINKER}" ]; then
        cva6_cmd+=("--linker=${TIER_LINKER}")
      fi

      if [ -n "${TIER_TEST_NAME}" ]; then
        cva6_cmd+=(--test "${TIER_TEST_NAME}")
      fi

      pushd verif/sim > /dev/null || rc=$?
      if [ "${rc}" -eq 0 ]; then
        run_logged "${cva6_cmd[@]}"
        record_rc "$?"
      fi
      popd > /dev/null || true
    fi
  else
    if [ -n "${TIER_HWCONFIG_OPTS}" ]; then
      export DV_HWCONFIG_OPTS="${TIER_HWCONFIG_OPTS}"
    fi

    run_logged env \
      DV_SIMULATORS="${TIER_SIMULATOR}" \
      DV_TARGET="${TIER_CONFIG}" \
      bash -e "verif/regress/${TIER_TESTCASE}.sh"
    record_rc "$?"
  fi
fi

collect_reports

if [ "${rc}" -eq 0 ] && ! compgen -G "verif/sim/out*" > /dev/null; then
  append_failure "ERROR: ${TIER_NAME} job reported success but produced no verif/sim/out* results."
  rc=1
fi

if [ "${rc}" -eq 0 ] && ! scan_for_failures; then
  rc=1
fi

if [ "${rc}" -eq 0 ] && ! scan_iss_traces; then
  rc=1
fi

echo "${rc}" > "${EXIT_CODE_FILE}"
exit "${rc}"
