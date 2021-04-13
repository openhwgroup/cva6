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
###############################################################################
#
# Makefile for the "unknown simulator".  
#
###############################################################################

no_rule:
	@echo 'no SIMULATOR and rule/target specified.'
	@echo 'Usage: make SIMULATOR=<simulator> <target>'
	@echo 'e.g: make SIMULATOR=xrun hello-world'
	@exit 1

%::
	@echo '$(SIMULATOR): unknown simulator'
	@exit 1