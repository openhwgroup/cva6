# Copyright 2021 Thales DIS design services SAS
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
# You may obtain a copy of the License at https://solderpad.org/licenses/
#
# Original Author: Jean-Roch COULON - Thales
#

source -echo -verbose scripts/dc_setup.tcl

set clk_name main_clk
set clk_port clk_i
set clk_ports_list [list $clk_port]
set clk_period $PERIOD
set input_delay $INPUT_DELAY
set output_delay $OUTPUT_DELAY

set_app_var search_path "../../vendor/pulp-platform/common_cells/include/ $search_path"

sh rm -rf work
sh mkdir work
define_design_lib ariane_lib -path work

set CVA6_REPO_DIR "../../"
set TARGET_CFG $TARGET
source Flist.cva6_synth

elaborate ${DESIGN_NAME} -library ariane_lib

uniquify
link

create_clock [get_ports $clk_port] -name $clk_name -period $clk_period

#set_dont_touch to keep sram as black boxes
set_dont_touch i_cache_subsystem/i_wt_dcache/i_wt_dcache_mem/gen_tag_srams[*].i_tag_sram
set_dont_touch i_cache_subsystem/i_wt_dcache/i_wt_dcache_mem/gen_data_banks[*].i_data_sram
set_dont_touch i_cache_subsystem/i_cva6_icache/gen_sram[*].data_sram
set_dont_touch i_cache_subsystem/i_cva6_icache/gen_sram[*].tag_sram

write -hierarchy -format ddc -output ${DCRM_ELABORATED_DESIGN_DDC_OUTPUT_FILE}

change_name -rule verilog -hier

# Prevent assignment statements in the Verilog netlist.
set_fix_multiple_port_nets -all -buffer_constants

#constraint the timing to and from the sram black boxes
set_input_delay -clock main_clk -max $input_delay i_cache_subsystem/i_wt_dcache/i_wt_dcache_mem/gen_tag_srams_*__i_tag_sram/gen_cut_*__gen_mem_i_tc_sram_wrapper/rdata_o[*]
set_input_delay -clock main_clk -max $input_delay i_cache_subsystem/i_wt_dcache/i_wt_dcache_mem/gen_data_banks_*__i_data_sram/gen_cut_*__gen_mem_i_tc_sram_wrapper/rdata_o[*]
set_input_delay -clock main_clk -max $input_delay i_cache_subsystem/i_cva6_icache/gen_sram_*__data_sram/gen_cut_*__gen_mem_i_tc_sram_wrapper/rdata_o[*]
set_input_delay -clock main_clk -max $input_delay i_cache_subsystem/i_cva6_icache/gen_sram_*__tag_sram/gen_cut_*__gen_mem_i_tc_sram_wrapper/rdata_o[*]

set_output_delay $output_delay -max -clock main_clk i_cache_subsystem/i_wt_dcache/i_wt_dcache_mem/gen_tag_srams_*__i_tag_sram/gen_cut_*__gen_mem_i_tc_sram_wrapper/addr_i[*]
set_output_delay $output_delay -max -clock main_clk i_cache_subsystem/i_wt_dcache/i_wt_dcache_mem/gen_data_banks_*__i_data_sram/gen_cut_*__gen_mem_i_tc_sram_wrapper/addr_i[*]
set_output_delay $output_delay -max -clock main_clk i_cache_subsystem/i_cva6_icache/gen_sram_*__data_sram/gen_cut_*__gen_mem_i_tc_sram_wrapper/addr_i[*]
set_output_delay $output_delay -max -clock main_clk i_cache_subsystem/i_cva6_icache/gen_sram_*__tag_sram/gen_cut_*__gen_mem_i_tc_sram_wrapper/addr_i[*]

# Check the current design for consistency
check_design -summary > ${DCRM_CHECK_DESIGN_REPORT}

compile_ultra -no_boundary_optimization

change_names -rules verilog -hierarchy

write -format verilog -hierarchy -output ${DCRM_FINAL_VERILOG_OUTPUT_FILE}
write -format verilog -hierarchy -output ${DESIGN_NAME}_synth.v
write -format ddc     -hierarchy -output ${DCRM_FINAL_DDC_OUTPUT_FILE}

report_timing -nworst 10  >  ${DCRM_FINAL_TIMING_REPORT}
report_timing -through i_cache_subsystem/i_wt_dcache/i_wt_dcache_mem/gen_tag_srams_*__i_tag_sram/gen_cut_*__gen_mem_i_ram/rdata_o[*] >>  ${DCRM_FINAL_TIMING_REPORT}
report_timing -through i_cache_subsystem/i_wt_dcache/i_wt_dcache_mem/gen_data_banks_*__i_data_sram/gen_cut_*__gen_mem_i_ram/rdata_o[*] >>  ${DCRM_FINAL_TIMING_REPORT}
report_timing -through i_cache_subsystem/i_cva6_icache/gen_sram_*__data_sram/gen_cut_*__gen_mem_i_ram/rdata_o[*] >>  ${DCRM_FINAL_TIMING_REPORT}
report_timing -through i_cache_subsystem/i_cva6_icache/gen_sram_*__tag_sram/gen_cut_*__gen_mem_i_ram/rdata_o[*] >>  ${DCRM_FINAL_TIMING_REPORT}
report_timing -through i_cache_subsystem/i_wt_dcache/i_wt_dcache_mem/gen_tag_srams_*__i_tag_sram/addr_i[*] >>  ${DCRM_FINAL_TIMING_REPORT}
report_timing -through i_cache_subsystem/i_wt_dcache/i_wt_dcache_mem/gen_data_banks_*__i_data_sram/addr_i[*] >>  ${DCRM_FINAL_TIMING_REPORT}
report_timing -through i_cache_subsystem/i_cva6_icache/gen_sram_*__data_sram/addr_i[*] >>  ${DCRM_FINAL_TIMING_REPORT}
report_timing -through i_cache_subsystem/i_cva6_icache/gen_sram_*__tag_sram/addr_i[*] >>  ${DCRM_FINAL_TIMING_REPORT}

report_area -hier -nosplit > ${DCRM_FINAL_AREA_REPORT}
write_parasitics -output ${DCRM_FINAL_SPEF_OUTPUT_FILE}
write_sdc ${DCRM_FINAL_SDC_OUTPUT_FILE}
write_sdf ${DESIGN_NAME}_synth.v.sdf

exit
