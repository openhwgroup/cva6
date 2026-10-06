#!/bin/bash
# Format core/ with Verible the way the CI's Verible job (v0.0-4084-gf3e4d98b)
# checks it: every .v and .sv file under core/ except the configuration
# packages. CI sees core/ without its submodules, so hpdcache and cvfpu are left
# out here too.

VERIBLE=${VERIBLE:-verible-verilog-format}

cd "$(dirname "$0")/.." || exit 1
find core -regex ".*\.\(v\|sv\)$" \
  -not -path "core/cache_subsystem/hpdcache/*" -not -path "core/cvfpu/*" |
  grep -v "^core/include/.*_config_pkg\.sv$" |
  xargs "$VERIBLE" --inplace
