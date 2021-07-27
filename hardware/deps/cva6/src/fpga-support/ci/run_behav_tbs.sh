#!/usr/bin/env bash

set -e

readonly CI_DIR="$( cd $(dirname $0) ; pwd -P )"
readonly ROOT_DIR="$( cd ${CI_DIR}/.. ; pwd -P )"
readonly BEHAV_DIR="${ROOT_DIR}/behav"

cd ${CI_DIR}
git clone git@iis-git.ee.ethz.ch:pulp-platform/big.pulp.git -b master > /dev/null
readonly BIGPULP_DIR="${CI_DIR}/big.pulp"
export CF_MATH_PKG_PATH="${BIGPULP_DIR}/fe/ips/pkg/cfmath"

cd ${BEHAV_DIR}
make
