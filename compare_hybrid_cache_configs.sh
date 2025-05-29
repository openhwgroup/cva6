#!/bin/bash
# Run a set of benchmarks across multiple cache configurations.
# Usage: compare_hybrid_cache_configs.sh [config.yml]
set -euo pipefail

CFG_FILE=${1:-config/hybrid_cache_analysis.yml}
if [ ! -f "$CFG_FILE" ]; then
  echo "Configuration file $CFG_FILE not found" >&2
  exit 1
fi

tests=($(yq e '.tests[]' "$CFG_FILE"))
configs=($(yq e '.configs[]' "$CFG_FILE"))

TIMESTAMP=$(date +%Y%m%d_%H%M%S)
RESULT_DIR="hybrid_cache_comparison_${TIMESTAMP}"
mkdir -p "${RESULT_DIR}/config_backups" "${RESULT_DIR}/simulation_artifacts"

cp core/include/cv32a60x_config_pkg.sv "${RESULT_DIR}/config_backups/cv32a60x_config_pkg.sv.original"
cp core/include/wt_hybrid_cache_pkg.sv "${RESULT_DIR}/config_backups/wt_hybrid_cache_pkg.sv.original"

run_cache_test() {
  local CONFIG=$1
  local RESULT_SUBDIR="${RESULT_DIR}/${CONFIG}"
  mkdir -p "$RESULT_SUBDIR/simulation_artifacts"

  echo "Running tests for $CONFIG" || true
  case $CONFIG in
    WT)
      sed -i 's/DCacheType: config_pkg::[^,]*/DCacheType: config_pkg::WT/' core/include/cv32a60x_config_pkg.sv;;
    WT_HYB)
      sed -i 's/DCacheType: config_pkg::[^,]*/DCacheType: config_pkg::WT_HYB/' core/include/cv32a60x_config_pkg.sv;;
    WT_HYB_FORCE_SET_ASS)
      sed -i 's/DCacheType: config_pkg::[^,]*/DCacheType: config_pkg::WT_HYB_FORCE_SET_ASS/' core/include/cv32a60x_config_pkg.sv;;
    WT_HYB_FORCE_FULL_ASS)
      sed -i 's/DCacheType: config_pkg::[^,]*/DCacheType: config_pkg::WT_HYB_FORCE_FULL_ASS/' core/include/cv32a60x_config_pkg.sv;;
  esac
  cp core/include/cv32a60x_config_pkg.sv "$RESULT_SUBDIR/cv32a60x_config_pkg.sv.$CONFIG"

  pushd verif/sim >/dev/null
  make clean
  for t in "${tests[@]}"; do
    echo "Running $t ..." || true
    if make veri-testharness-run HWCONFIG=cv32a60x TB=core TEST="$t" TRACE=1; then
      cp -r out_* "$OLDPWD/$RESULT_SUBDIR/simulation_artifacts/" 2>/dev/null || true
    else
      echo "Test $t failed for $CONFIG" >> "$OLDPWD/$RESULT_DIR/failures.log"
    fi
  done
  popd >/dev/null
}

for cfg in "${configs[@]}"; do
  run_cache_test "$cfg"
 done

yq e -o=json '.' "$CFG_FILE" > "${RESULT_DIR}/config_used.json"
cp "${RESULT_DIR}/config_backups/cv32a60x_config_pkg.sv.original" core/include/cv32a60x_config_pkg.sv

echo "Results stored in $RESULT_DIR"
