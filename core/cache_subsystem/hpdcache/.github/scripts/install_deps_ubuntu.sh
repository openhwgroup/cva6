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
#  Description: Install dependencies for the HPDcache's Github CI
##
#  Update list of packages
sudo apt-get update ;

#  Install essential packages
sudo apt-get install -y build-essential python3 git wget file ;

#  Install Verilator dependencies
sudo apt-get install -y ccache mold numactl help2man make autoconf flex libfl-dev bison ;
