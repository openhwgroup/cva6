#!/usr/bin/env bash
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
set -euo pipefail
script_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
repo_dir=$(cd -- "$script_dir/../../../.." && pwd)
if [[ $# -ne 2 ]]; then
  printf 'Usage: bash %s BUILD_DIRECTORY BASELINE_GIT_REF\n' "$0" >&2
  exit 2
fi
mkdir -p -- "$1"
build_dir=$(cd -- "$1" && pwd)
baseline_ref=$2
baseline_dir=$(mktemp -d "$build_dir/baseline-source.XXXXXX")
git -C "$repo_dir" show "$baseline_ref:core/csr_regfile.sv" > "$baseline_dir/csr_regfile.sv"
printf 'Baseline commit: %s\n' "$(git -C "$repo_dir" rev-parse "$baseline_ref^{commit}")"
printf 'Build logs: %s\n' "$build_dir"
printf 'Building and running the pre-fix CSR module (one build job)...\n'
if bash "$script_dir/run.sh" "$build_dir/before" "$baseline_dir/csr_regfile.sv" \
    > "$build_dir/before.log" 2>&1; then
  printf 'FAIL: baseline unexpectedly passed; reproduction was not established.\n' >&2
  exit 1
else
  before_status=$?
fi
if ! grep -Fq 'ISSUE3497: stepped WFI leaked halt into Debug Mode' "$build_dir/before.log"; then
  tail -n 40 "$build_dir/before.log" >&2
  printf 'FAIL: baseline failed for another reason (exit %s).\n' "$before_status" >&2
  exit 1
fi
printf 'PASS: original RTL reproduced issue #3497 (exit %s).\n' "$before_status"
printf 'Building and running the working-tree CSR module (one build job)...\n'
if bash "$script_dir/run.sh" "$build_dir/after" "$repo_dir/core/csr_regfile.sv" \
    > "$build_dir/after.log" 2>&1; then
  if ! grep -Fxq 'PASS: CVA6 CSR WFI regression' "$build_dir/after.log"; then
    printf 'FAIL: simulator exited without the final pass marker.\n' >&2
    exit 1
  fi
else
  after_status=$?
  tail -n 40 "$build_dir/after.log" >&2
  printf 'FAIL: working-tree test exited with status %s.\n' "$after_status" >&2
  exit 1
fi
grep '^PASS' "$build_dir/after.log"
printf 'PASS: before/after CSR WFI regression comparison\n'
