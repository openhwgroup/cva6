#!/bin/sh

##
#  Copyright 2023,2024 CEA*
#  *Commissariat a l'Energie Atomique et aux Energies Alternatives (CEA)
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
#  Description: VCD to FST conversion wrapper
##
vcdfile=$1

#  Check that the VCD file exists
if [[ "x" == "x${vcdfile}" ]] ; then
    echo "usage: $(basename $0) <vcdfile>" ; exit 1
fi

#  Check that the VCD file exists
if [[ ! -e ${vcdfile} ]] ; then
    echo "error: file ${vcdfile} not found" ; exit 1
fi

#  Convert the VCD file to FST
vcd2fst -c -v ${vcdfile} -f ${vcdfile}.fst

#  Check that the FST file was generated
if [[ ! -e ${vcdfile}.fst ]] ; then
    echo "error: file ${vcdfile}.fst not generated" ; exit 1
fi

#  Remove the VCD file if the FST one was generated
rm ${vcdfile}
