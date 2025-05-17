#!/bin/bash
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
#  Description: Verilator installation script
##
num_jobs=${PARALLEL_JOBS:-1} ;

if [[ "x${VERILATOR_ROOT}" == "x" ]] ; then
   echo "VERILATOR_ROOT env variable not defined" ;
   exit 1 ;
fi

verilator_installed="no"
if [[ -d ${VERILATOR_ROOT} ]] ; then
   echo "Verilator is already installed" ;
   verilator_installed="yes"
fi

if [[ "x${VERILATOR_VER}" == "x" ]] ; then
   echo "VERILATOR_VER env variable not defined" ;
   exit 1 ;
fi

if [[ "x${VERILATOR_URL}" == "x" ]] ; then
   echo "VERILATOR_URL env variable not defined" ;
   exit 1 ;
fi

if [[ ${verilator_installed} == "no" ]]; then
(
    #  clone Verilator repository
    git clone -b ${VERILATOR_VER} ${VERILATOR_URL} ${VERILATOR_ROOT} ;

    #  configure and build Verilator in-place
    cd ${VERILATOR_ROOT} ;
    autoconf ;
    ./configure ;
    [[ $? != 0 ]] && exit 1 ;

    make -j${num_jobs} ;
    [[ $? != 0 ]] && exit 1 ;

    #  housekeeping
    rm -rf ${VERILATOR_ROOT}/src/obj_dbg ;
    rm -rf ${VERILATOR_ROOT}/src/obj_opt ;
)
fi
