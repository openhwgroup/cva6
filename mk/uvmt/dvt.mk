###############################################################################
#
# Copyright 2020 AMIQ EDA s.r.l. 
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
# Bring up the project inside the AMIQ DVT Eclipse IDE (https://dvteclipse.com/)
#
# Usage: make SIMULATOR=<simulator> open_in_dvt_ide
###############################################################################

DVT_COMMAND=$(DVT_HOME)/bin/dvt_cli.sh createProject $(CORE_V_VERIF) -force -lang vlog -build default $(DVT_CLI_ARGS)

ifeq ($(SIMULATOR), xrun)
	DVT_BUILD_FILE_CONTENT="+dvt_init+xcelium.xrun\n$(XRUN_COMP)\n-top $(RTLSRC_VLOG_TB_TOP)"
else
ifeq ($(SIMULATOR), vcs)
	DVT_BUILD_FILE_CONTENT="+dvt_init+vcs.vlogan\n$(VCS_COMP)\n-top $(RTLSRC_VLOG_TB_TOP)"
else
ifeq ($(SIMULATOR), vsim)
	DVT_BUILD_FILE_CONTENT="+dvt_init+questa.vlog\n-work $(VWORK) $(VLOG_FLAGS)	+incdir+$(DV_UVME_PATH) +incdir+$(DV_UVMT_PATH) +incdir+$(UVM_HOME) $(UVM_HOME)/uvm_pkg.sv -f $(CV_CORE_MANIFEST) $(VLOG_FILE_LIST) $(TBSRC_PKG) -top $(RTLSRC_VLOG_TB_TOP)"
else
	DVT_BUILD_FILE_CONTENT="+dvt_init+dvt\n-uvm\n+define+CV32E40P_ASSERT_ON\n+define+ISS+CV32E40P_TRACE_EXECUTION\n+incdir+$(DV_UVME_PATH)\n+incdir+$(DV_UVMT_PATH)\n-f $(CV_CORE_MANIFEST)\n-f $(DV_UVMT_PATH)/uvmt_$(CV_CORE_LC).flist\n-f $(DV_UVMT_PATH)/imperas_iss.flist\n-top $(RTLSRC_VLOG_TB_TOP)"
endif
endif
endif

.PHONY: open_in_dvt_ide check_dvt_home create_dvt_build_dir create_dvt_build_file dvt_dump_env_vars

create_dvt_build_dir:
	@ mkdir -p $(CORE_V_VERIF)/.dvt

create_dvt_build_file: create_dvt_build_dir $(CV_CORE_PKG) $(SVLIB_PKG)
	@ printf $(DVT_BUILD_FILE_CONTENT) > $(CORE_V_VERIF)/.dvt/default.build

open_in_dvt_ide: check_dvt_home create_dvt_build_file
	$(DVT_COMMAND)

define NEWLINE


endef

ENV_VARS := $(foreach v, $(.VARIABLES), $(if $(filter file,$(origin $(v))),  $(if $(filter-out .% NEWLINE%, $(v)), export $(v)='$($(v))' $(NEWLINE) )))
dvt_dump_env_vars:
	$(ENV_VARS)

check_dvt_home:
ifndef DVT_HOME
	@ echo "DVT_HOME env var is not set!"; \
	exit 1; \
endif
endif
