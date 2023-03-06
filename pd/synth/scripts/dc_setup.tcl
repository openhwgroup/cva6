# Copyright 2021 Thales DIS design services SAS
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
# You may obtain a copy of the License at https://solderpad.org/licenses/
#
# Original Author: Jean-Roch COULON - Thales
#

# Variables common to all reference methodology scripts
set PERIOD                        [getenv PERIOD];
set DESIGN_NAME                   [getenv DESIGN_NAME]  ;#  The name of the top-level design
set TARGET                        [getenv TARGET];
set TECH                          [getenv TECH_NAME];
set techno                        [getenv TECH_NAME];
set FOUNDRY_PATH                  [getenv FOUNDRY_PATH];
set TARGET_LIBRARY_FILES          [getenv TARGET_LIBRARY_FILES];
set INPUT_DELAY                   [getenv INPUT_DELAY];
set OUTPUT_DELAY                  [getenv OUTPUT_DELAY];

set ADDITIONAL_LINK_LIB_FILES     "                                  ";#  Extra link logical libraries not included in TARGET_LIBRARY_FILES

# Remove messages
suppress_message LINK-17
suppress_message MWLIBP-300
suppress_message MWLIBP-301
suppress_message MWLIBP-319
suppress_message MWLIBP-319
suppress_message MWLIBP-324
suppress_message MWLIBP-311
suppress_message MWLIBP-032
suppress_message UCN-1
suppress_message UID-282

set ADDITIONAL_SEARCH_PATH " ${FOUNDRY_PATH}/synopsys ${FOUNDRY_PATH} ";
set_app_var search_path ". ${ADDITIONAL_SEARCH_PATH} $search_path"

if {$synopsys_program_name == "dc_shell"}  {
  set_app_var target_library ${TARGET_LIBRARY_FILES}
  set_app_var synthetic_library dw_foundation.sldb
  set_app_var link_library "* $target_library $ADDITIONAL_LINK_LIB_FILES $synthetic_library"
}

source -echo -verbose scripts/dc_setup_filenames.tcl

# The following setting removes new variable info messages from the end of the log file
set_app_var sh_new_variable_message false

if {$synopsys_program_name == "dc_shell"}  {

  #################################################################################
  # Design Compiler Setup Variables
  #################################################################################

  # Use the set_host_options command to enable multicore optimization to improve runtime.
  # This feature has special usage and license requirements.  Refer to the
  # "Support for Multicore Technology" section in the Design Compiler User Guide
  # for multicore usage guidelines.
  # Note: This is a DC Ultra feature and is not supported in DC Expert.

  set_host_options -max_cores 8

  # Change alib_library_analysis_path to point to a central cache of analyzed libraries
  # to save runtime and disk space.  The following setting only reflects the
  # default value and should be changed to a central location for best results.

  set_app_var alib_library_analysis_path .

  # Add any additional Design Compiler variables needed here
  define_name_rules verilog \
    -target_bus_naming_style "%s\[%d\]" \
    -allowed "a-z0-9_" \
    -first_restricted "0-9_" \
    -replacement_char "_" \
    -equal_ports_nets -inout_ports_equal_nets \
    -collapse_name_space -case_insensitive -special verilog \
    -add_dummy_nets \
    -dummy_net_prefix "synp_unconn_%d"

  # Eliminate tri-state nets and assign primitives in the output netlist"
  set_app_var verilogout_no_tri true

  # Preserve FF with not load used as spare"
  set_app_var hdlin_preserve_sequential ff+loop_variables

  ###  Power optim
  set_app_var power_remove_redundant_clock_gates true
  set_app_var power_cg_reconfig_stages true
  set_app_var compile_clock_gating_through_hierarchy  true
  set_app_var power_cg_designware true
  set_app_var power_cg_derive_related_clock true
  set_app_var do_operand_isolation true
  set_app_var power_low_power_placement true
  set_app_var power_opto_extra_high_dynamic_power_effort true

  ### Module name naming style
  set_app_var template_parameter_style "%s"
  set_app_var template_naming_style "%s"

}
