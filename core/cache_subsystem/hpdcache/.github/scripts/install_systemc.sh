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
#  Description: SystemC installation script
##
num_jobs=${PARALLEL_JOBS:-1} ;

#  Install SystemC
if [[ "x${SYSTEMC_HOME}" == "x" ]] ; then
   echo "SYSTEMC_HOME env variable not defined" ;
   exit 1 ;
fi

systemc_installed="no"
if [[ -e ${SYSTEMC_HOME}/lib-linux64/libsystemc.la ]] ; then
   echo "SystemC is already installed" ;
   systemc_installed="yes" ;
fi

if [[ "x${SYSTEMC_VER}" == "x" ]] ; then
   echo "SYSTEMC_VER env variable not defined" ;
   exit 1 ;
fi

if [[ "x${SYSTEMC_URL}" == "x" ]] ; then
   echo "SYSTEMC_URL env variable not defined" ;
   exit 1 ;
fi

#  get SystemC
if [[ ${systemc_installed} == "no" ]] ; then
(
    wget -O ${ARCHIVE_DIR}/${SYSTEMC_VER}.tar.gz \
        ${SYSTEMC_URL}/${SYSTEMC_VER}.tar.gz ;
    tar xzf ${ARCHIVE_DIR}/${SYSTEMC_VER}.tar.gz ;
    mv -f systemc-${SYSTEMC_VER} ${SYSTEMC_HOME} ;

    #  configure and build SystemC
    mkdir -p ${SYSTEMC_HOME}/objdir ;
    cd ${SYSTEMC_HOME}/objdir ;
    ../configure ;
    [[ $? != 0 ]] && exit 1 ;

    make -j${num_jobs} ;
    [[ $? != 0 ]] && exit 1 ;

    make install ;
    [[ $? != 0 ]] && exit 1 ;

    #  housekeeping
    rm -rf ${SYSTEMC_HOME}/objdir ;
)
fi

#  Install SCV

if [[ "x${SCV_HOME}" == "x" ]] ; then
   echo "SCV_HOME env variable not defined" ;
   exit 1 ;
fi

scv_installed="no"
if [[ -e ${SYSTEMC_HOME}/lib-linux64/libscv.la ]] ; then
   echo "SystemC Verification library is already installed" ;
   scv_installed="yes" ;
fi

if [[ "x${SCV_VER}" == "x" ]] ; then
   echo "SCV_VER env variable not defined" ;
   exit 1 ;
fi

if [[ "x${SCV_URL}" == "x" ]] ; then
   echo "SCV_URL env variable not defined" ;
   exit 1 ;
fi

if [[ ${scv_installed} == "no" ]] ; then
(
    #  get SCV
    wget -O ${ARCHIVE_DIR}/scv-${SCV_VER}.tar.gz \
            ${SCV_URL}/scv-${SCV_VER}.tar.gz ;
    tar xzf ${ARCHIVE_DIR}/scv-${SCV_VER}.tar.gz ;
    mv -f scv-${SCV_VER} ${SCV_HOME} ;

    #  configure and build SCV
    mkdir -p ${SCV_HOME}/objdir ;
    cd ${SCV_HOME}/objdir ;
    ../configure --with-systemc=${SYSTEMC_HOME} ;
    [[ $? != 0 ]] && exit 1 ;

    make -j${num_jobs} ;
    [[ $? != 0 ]] && exit 1 ;

    make install ;
    [[ $? != 0 ]] && exit 1 ;

    #  housekeeping
    rm -rf ${SCV_HOME}/objdir ;
)
fi
