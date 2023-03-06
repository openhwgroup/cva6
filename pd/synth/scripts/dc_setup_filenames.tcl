# Copyright 2021 Thales DIS design services SAS
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
# You may obtain a copy of the License at https://solderpad.org/licenses/
#
# Original Author: Jean-Roch COULON - Thales
#

puts "RM-Info: Running script [info script]\n"

#################################################################################
# Design Compiler Reference Methodology Filenames Setup
# Script: dc_setup_filenames.tcl
# Version: J-2014.09-SP2 (January 12, 2015)
# Copyright (C) 2010-2015 Synopsys, Inc. All rights reserved.
#################################################################################

set INPUTS_DIR ${DESIGN_NAME}_${TARGET}/inputs/
set REPORTS_DIR ${DESIGN_NAME}_${TARGET}/reports/${PERIOD}/
set OUTPUTS_DIR ${DESIGN_NAME}_${TARGET}/outputs/${PERIOD}/
file mkdir ${INPUTS_DIR}
file mkdir ${REPORTS_DIR}
file mkdir ${OUTPUTS_DIR}

###############
# Input Files #
###############

set DCRM_SDC_INPUT_FILE                                 ${INPUTS_DIR}/${DESIGN_NAME}.sdc
set DCRM_CONSTRAINTS_INPUT_FILE                         ${INPUTS_DIR}/${DESIGN_NAME}.constraints.tcl

###########
# Reports #
###########

set DCRM_CHECK_LIBRARY_REPORT                           ${REPORTS_DIR}/${DESIGN_NAME}_${TECH}_synth_check_library.rpt

set DCRM_CONSISTENCY_CHECK_ENV_FILE                     ${REPORTS_DIR}/${DESIGN_NAME}_${TECH}.compile_ultra.env
set DCRM_CHECK_DESIGN_REPORT                            ${REPORTS_DIR}/${DESIGN_NAME}_${TECH}.check_design.rpt
set DCRM_ANALYZE_DATAPATH_EXTRACTION_REPORT             ${REPORTS_DIR}/${DESIGN_NAME}_${TECH}.analyze_datapath_extraction.rpt

set DCRM_FINAL_QOR_REPORT                               ${REPORTS_DIR}/${DESIGN_NAME}_${TECH}_synth_qor.rpt
set DCRM_FINAL_TIMING_REPORT                            ${REPORTS_DIR}/${DESIGN_NAME}_${TECH}_synth_timing.rpt
set DCRM_FINAL_AREA_REPORT                              ${REPORTS_DIR}/${DESIGN_NAME}_${TECH}_synth_area.rpt
set DCRM_FINAL_POWER_REPORT                             ${REPORTS_DIR}/${DESIGN_NAME}_${TECH}_synth_power.rpt
set DCRM_FINAL_CLOCK_GATING_REPORT                      ${REPORTS_DIR}/${DESIGN_NAME}_${TECH}_synth_clock_gating.rpt
set DCRM_FINAL_SELF_GATING_REPORT                       ${REPORTS_DIR}/${DESIGN_NAME}_${TECH}_synth_self_gating.rpt
set DCRM_THRESHOLD_VOLTAGE_GROUP_REPORT                 ${REPORTS_DIR}/${DESIGN_NAME}_${TECH}_synth_threshold.voltage.group.rpt
set DCRM_INSTANTIATE_CLOCK_GATES_REPORT                 ${REPORTS_DIR}/${DESIGN_NAME}_${TECH}_synth_instatiate_clock_gates.rpt
set DCRM_FINAL_POWER_REPORT                             ${REPORTS_DIR}/${DESIGN_NAME}_${TECH}_synth_power.rpt

################
# Output Files #
################

set DCRM_AUTOREAD_RTL_SCRIPT                            ${OUTPUTS_DIR}/${DESIGN_NAME}_${TECH}.autoread_rtl.tcl
set DCRM_ELABORATED_DESIGN_DDC_OUTPUT_FILE              ${OUTPUTS_DIR}/${DESIGN_NAME}_${TECH}.elab.ddc
set DCRM_COMPILE_ULTRA_DDC_OUTPUT_FILE                  ${OUTPUTS_DIR}/${DESIGN_NAME}_${TECH}.compile_ultra.ddc
set DCRM_FINAL_DDC_OUTPUT_FILE                          ${OUTPUTS_DIR}/${DESIGN_NAME}_${TECH}_synth.ddc
set DCRM_FINAL_VERILOG_OUTPUT_FILE                      ${OUTPUTS_DIR}/${DESIGN_NAME}_${TECH}_synth.v
set DCRM_FINAL_SDC_OUTPUT_FILE                          ${OUTPUTS_DIR}/${DESIGN_NAME}_${TECH}_synth.sdc
set DCRM_FINAL_SPEF_OUTPUT_FILE                         ${OUTPUTS_DIR}/${DESIGN_NAME}_${TECH}_synth.spef
set DCRM_FINAL_FSDB_OUTPUT_FILE                         ${OUTPUTS_DIR}/${DESIGN_NAME}_${TECH}_synth.fsdb
set DCRM_FINAL_VCD_OUTPUT_FILE                          ${OUTPUTS_DIR}/${DESIGN_NAME}_${TECH}_synth.vcd


puts "RM-Info: Completed script [info script]\n"
