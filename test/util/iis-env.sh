# The usual setup of the standalone testbench on IIS machines. Source it in bash
# from anywhere in the repository:
#
#   source test/util/iis-env.sh
#
# It puts RISC-V GCC 14.2 and the SEPP tools on PATH, takes Verilator from the
# oseda container and QuestaSim from its SEPP wrapper, and activates the Python
# environment of test/, creating it on first use. Simulations and the
# regression runners then run inside the container, whose libraries the
# Verilator model is built against:
#
#   make -C test/sw all
#   make -C test verilator-build
#   $OSEDA make -C test verilator-run HEXFILE=sw/out/hello.hex
#   $OSEDA ./test/util/run-pulp-tests.sh verilator hello clic_simple
#
# SPDX-License-Identifier: Apache-2.0

export OSEDA="oseda -2026.04"
export RISCV=/usr/pack/riscv-1.0-kgf/riscv64-gcc-14.2.0
export PATH="${RISCV}/bin:/usr/sepp/bin:/usr/local/bin:${PATH}"
export VERILATOR="${OSEDA} verilator"
export QUESTA=questa-2025.3

cva6tb_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
(cd "${cva6tb_dir}" && uv sync --locked --quiet) && . "${cva6tb_dir}/.venv/bin/activate"
unset cva6tb_dir
