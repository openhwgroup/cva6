#!/bin/sh

###############################################################################
#
# Copyright 2021 OpenHW Group
# Copyright 2021 Silicon Labs, Inc.
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     https://solderpad.org/licenses/
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
#
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
#
###############################################################################
#
# Helper bash script to determine when multiple build toolchains are configured
# to diagnose toolchain test configuration issues with the COREV verification
# testbench environment
#
###############################################################################

GNU_YES=$1
PULP_YES=$2
COREV_YES=$3
LLVM_YES=$4

# Logic to return 1 if any two toolchains are enabled
if [ ${GNU_YES} = "YES" -a ${PULP_YES} = "YES" ]; then
	echo "1"
	exit 0
fi

if [ ${GNU_YES} = "YES" -a ${COREV_YES} = "YES" ]; then
	echo "1"
	exit 0
fi

if [ ${GNU_YES} = "YES" -a ${LLVM_YES} = "YES" ]; then
	echo "1"
	exit 0
fi

if [ ${PULP_YES} = "YES" -a ${COREV_YES} = "YES" ]; then
	echo "1"
	exit 0
fi

if [ ${PULP_YES} = "YES" -a ${LLVM_YES} = "YES" ]; then
	echo "1"
	exit 0
fi

if [ ${COREV_YES} = "YES" -a ${LLVM_YES} = "YES" ]; then
	echo "1"
	exit 0
fi

echo "0"

