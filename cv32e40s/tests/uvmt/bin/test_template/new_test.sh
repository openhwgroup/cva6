#!/bin/bash
###############################################################################
# Copyright 2020 OpenHW Group
# Copyright 2020 Datum Technology Corporation
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
###############################################################################


#########
# ABOUT #
#########
# Simple script to take test_templates.sv and do a simple string substitution for the test name.


#############
# ARGUMENTS #
#############
test_name=$1
test_name_uppercase=${test_name^^}


###############
# ENTRY POINT #
###############
cat test_template.sv | sed -E "s/[$][{]name_uppercase[}]/$test_name_uppercase/g" | sed -E "s/[$][{]name[}]/$test_name/g" > uvmt_cv32_${test_name}_test.sv

