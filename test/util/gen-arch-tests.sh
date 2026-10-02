#!/bin/bash
# Generates the riscv-arch-test ELFs for one CVA6 configuration and converts
# them to the Verilog hex images the testbench loads with +binary. ACT computes
# every expected result on Sail from the description in sw/arch-test/<config>/,
# so the ELFs are only valid for that configuration.
#
# `make -C test/sw arch-test CVA6_CONFIG=<config>` fetches the framework and Sail
# first and calls this with where they are:
#
#   ACT_DIR=... SAIL_DIR=... ACT_RV_BINROOT=... util/gen-arch-tests.sh <config>
#
# SPDX-License-Identifier: Apache-2.0

set -euo pipefail

if [ $# -ne 1 ] || [ -z "$1" ]; then
    echo "usage: $(basename "$0") <config>, one of:" \
         $(cd "$(dirname -- "${BASH_SOURCE[0]}")/../sw/arch-test" && ls -d -- */ | tr -d /) >&2
    exit 2
fi
config="$1"
: "${ACT_DIR:?set ACT_DIR to the riscv-arch-test checkout (make -C test/sw arch-test does)}"
: "${SAIL_DIR:?set SAIL_DIR to the Sail installation (make -C test/sw arch-test does)}"
: "${ACT_RV_BINROOT:?set ACT_RV_BINROOT to the bin directory of a RISC-V GCC 15 or later}"

testdir="$(realpath -m "$(dirname -- "${BASH_SOURCE[0]}")/..")"
descdir="${testdir}/sw/arch-test"

if [ ! -d "${descdir}/${config}" ]; then
    echo "error: no ACT description for ${config}; available:" \
         $(cd "${descdir}" && ls -d -- */ | tr -d /) >&2
    exit 1
fi

# The framework checks its prerequisites only much later, from inside a
# traceback, so check them first: a RISC-V GCC 15 or later, which the rest of
# the testbench does not use, and Ruby 3.2 or later with development headers
# for the UDB gems.
v="$("${ACT_RV_BINROOT}/riscv64-unknown-elf-gcc" -dumpversion 2>/dev/null | cut -d. -f1 || true)"
if [ -z "${v}" ]; then
    echo "error: no riscv64-unknown-elf-gcc under ACT_RV_BINROOT=${ACT_RV_BINROOT}" >&2
    exit 1
elif [ "${v}" -lt 15 ]; then
    echo "error: ACT4 needs RISC-V GCC 15 or later, found ${v} at ${ACT_RV_BINROOT}" >&2
    exit 1
fi
if ! ruby -e 'exit(Gem::Version.new(RUBY_VERSION) >= Gem::Version.new("3.2") &&
                   File.exist?(File.join(RbConfig::CONFIG["rubyhdrdir"], "ruby.h")))' 2>/dev/null; then
    echo "error: ACT4 needs Ruby 3.2 or later with development headers on PATH," \
         "found $(ruby -e 'print RUBY_VERSION' 2>/dev/null || echo none)" >&2
    exit 1
fi

# The framework expects the configuration directory inside its own tree.
cfgdir="${ACT_DIR}/config/cores/${config}"
mkdir -p "${cfgdir}"
cp "${descdir}/link.ld" "${descdir}/rvmodel_macros.h" "${descdir}/${config}"/* "${cfgdir}/"

# It runs in its own uv environment, so an inherited PYTHONPATH or activated
# venv (test/.venv) is dropped rather than left to shadow or contest it. Its
# uv.lock pins that environment and must not be re-resolved: a uv older than
# the framework's cannot parse its settings and would
# otherwise resolve again and rewrite the lockfile.
(cd "${ACT_DIR}" && env -u PYTHONPATH -u VIRTUAL_ENV UV_FROZEN=1 \
    PATH="${ACT_RV_BINROOT}:${SAIL_DIR}/bin:${PATH}" \
    make CONFIG_FILES="config/cores/${config}/test_config.yaml")

# Only the final ELFs: build/ also holds a .sig.elf per test, which the
# framework runs on Sail to compute the signature and which is not a test.
elfdir="${ACT_DIR}/work/${config}/elfs"
count=0
while IFS= read -r -d '' elf; do
    "${ACT_RV_BINROOT}/riscv64-unknown-elf-objcopy" -O verilog "${elf}" "${elf%.elf}.hex"
    count=$((count + 1))
done < <(find "${elfdir}" -name '*.elf' -print0)
echo "converted ${count} ELFs to hex under ${elfdir}"
