#!/bin/bash -x
##
#  Copyright 2023,2024 Cesar Fuguet
#
#  SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
#
#  Licensed under the Solderpad Hardware License v 2.1 (the “License”); you
#  may not use this file except in compliance with the License, or, at your
#  option, the Apache License version 2.0. You may obtain a copy of the
#  License at
#
#  https://solderpad.org/licenses/SHL-2.1/
#
#  Unless required by applicable law or agreed to in writing, any work
#  distributed under the License is distributed on an “AS IS” BASIS, WITHOUT
#  WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
#  License for the specific language governing permissions and limitations
#  under the License.
##
##
#  Author     : Cesar Fuguet
#  Date       : October, 2024
#  Description: Environment setup for the HPDcache's Github CI
##
export WORK_DIR=${PWD}
export BUILD_DIR=${WORK_DIR}/build
export ARCHIVE_DIR=${WORK_DIR}/archive
export PARALLEL_JOBS=7

mkdir -p ${ARCHIVE_DIR} ${BUILD_DIR} ;

#  SystemC env variables
export SYSTEMC_URL=https://github.com/accellera-official/systemc/archive/refs/tags
export SYSTEMC_VER=3.0.1
export SYSTEMC_HOME=${BUILD_DIR}/systemc-${SYSTEMC_VER}
export SYSTEMC_INCLUDE=${BUILD_DIR}/systemc-${SYSTEMC_VER}/include
export SYSTEMC_LIBDIR=${BUILD_DIR}/systemc-${SYSTEMC_VER}/lib-linux64

#  SystemC Verification library env variables
export SCV_URL=https://www.accellera.org/images/downloads/standards/systemc
export SCV_VER=2.0.1
export SCV_HOME=${BUILD_DIR}/scv-${SCV_VER}

#  Verilator env variables
export VERILATOR_URL=https://github.com/verilator/verilator
export VERILATOR_VER=v5.028
export VERILATOR_ROOT=${BUILD_DIR}/verilator-${VERILATOR_VER}

if [[ ! "${PATH}" =~ ".*${VERILATOR_ROOT}/bin.*" ]] ; then
    export PATH=${VERILATOR_ROOT}/bin:${PATH}
fi
