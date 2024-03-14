#!/bin/bash
set -e
set -x
export ROOT=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
export ROOT_PROJECT=$ROOT
export RISCV=$ROOT_PROJECT/tools/riscv-toolchain/

export VERILATOR_INSTALL_DIR="$ROOT_PROJECT"/tools/verilator/

ci/make-tmp.sh

bash ci/install-prereq.sh

bash ci/install-toolchain.sh

source verif/sim/setup-env.sh

source verif/regress/install-verilator.sh
if [ -d ${VERILATOR_BUILD_DIR} ]; then
    make -C ${VERILATOR_BUILD_DIR} clean
fi

source verif/regress/install-spike.sh
if [ -d ${SPIKE_SRC_DIR}/build/ ]; then
    make -C ${SPIKE_SRC_DIR}/build clean
fi
