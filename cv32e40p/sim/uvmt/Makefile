###############################################################################
#
# Copyright 2020 OpenHW Group
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
# Makefile for the CV32E40P "uvmt_cv32" testbench.  Substantially modified
# from the original Makefile for the RI5CY testbench.
#
###############################################################################
# 
# Copyright 2019 Claire Wolf
# Copyright 2019 Robert Balas
#
# Permission to use, copy, modify, and/or distribute this software for any
# purpose with or without fee is hereby granted, provided that the above
# copyright notice and this permission notice appear in all copies.
#
# THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES WITH
# REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF MERCHANTABILITY
# AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY SPECIAL, DIRECT,
# INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES WHATSOEVER RESULTING FROM
# LOSS OF USE, DATA OR PROFITS, WHETHER IN AN ACTION OF CONTRACT, NEGLIGENCE OR
# OTHER TORTIOUS ACTION, ARISING OUT OF OR IN CONNECTION WITH THE USE OR
# PERFORMANCE OF THIS SOFTWARE.
#
# Original Author: Robert Balas (balasr@iis.ee.ethz.ch)
#
###############################################################################

# "Constants"
MAKE                  = make
MAKE_PATH            := $(shell dirname $(realpath $(lastword $(MAKEFILE_LIST))))
export CORE_V_VERIF   = $(abspath $(MAKE_PATH)/../../..)
export CV_CORE       ?= cv32e40p

DPI_DASM_SPIKE_REPO  ?= https://github.com/riscv/riscv-isa-sim.git
CV_SW_TOOLCHAIN      ?= /opt/riscv
CV_SW_PREFIX         ?= " "

include ../ExternalRepos.mk
include $(CORE_V_VERIF)/mk/uvmt/uvmt.mk
