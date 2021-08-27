####################################################################
## Load SETUP 
####################################################################
sh date
sh echo "Current git version is `git rev-parse --short HEAD`"
source .alsaqr_synopsys_dc.setup
source scripts/design_setup.tcl
source scripts/area_report.tcl


set reAnalyzeRTL "TRUE"
set TRIAL_DIR "trial0_26_08_2021"
set DESIGN_NAME "al_saqr"
 
####################################################################
## Environment Setup
####################################################################
suppress_message { VER-130 }
set_host_option -max_core 8
set timing_enable_through_paths true

set compile_timing_high_effort true
set_app_var hdlin_sv_enable_rtl_attributes true
set_app_var write_name_nets_same_as_ports true
set_app_var hdlin_infer_multibit default_all
set compile_clock_gating_through_hierarchy true

sh mkdir -p ${TRIAL_DIR}/unmapped
sh mkdir -p ${TRIAL_DIR}/logs
sh mkdir -p ${TRIAL_DIR}/reports
sh date > ${TRIAL_DIR}/lock_date

####################################################################
## ANALYZE THE RTL CODE or Read the GTECH 
####################################################################

if { $reAnalyzeRTL == "TRUE" } {
    file delete -force -- ./work
    source -echo -verbose ./scripts/analyze_alsaqr.tcl > ${TRIAL_DIR}/logs/analyze.log
} else {
    read_file  -format ddc  ./${TRIAL_DIR}/unmapped/${DESIGN_NAME}_chip_unmapped.ddc
}


####################################################################
## ELABORATE DUSTIN TOP LEVEL
####################################################################

elaborate ${DESIGN_NAME} -work work > ${TRIAL_DIR}/reports/d00_elaborate.log
check_design                        > ${TRIAL_DIR}/reports/d01_check_design_postElab.rpt
current_design al_saqr
write -format verilog -hier -o ./${TRIAL_DIR}/unmapped/${DESIGN_NAME}_chip_unmapped.v
write -format ddc -hier -o ./${TRIAL_DIR}/unmapped/${DESIGN_NAME}_chip_unmapped.ddc ${DESIGN_NAME}
report_timing -loop -max_paths 100 > ./${TRIAL_DIR}/timing_loops.rpt

####################################################################
## DONT USE SPECIFIED CELLS
####################################################################
set_dont_use [get_lib_cells */*_A_*]
set_dont_use [get_lib_cells */*X0P5_*]
#these cells tend to leak a lot, synopsys was removing almost all of them to reduce leakage
#therefore, we do not allow it to use it in the first place
set_dont_use [get_lib_cells */*20SL*]
set_dont_use [get_lib_cells */*20L*]

####################################################################
## LINK
####################################################################
link                                                      > ${TRIAL_DIR}/reports/d03_link_alsaqr.rpt

####################################################################
## UNIQUIFY
####################################################################
after 1000
set uniquify_naming_style "alsaqr_%s_%d"
uniquify -force                                           > ${TRIAL_DIR}/reports/d04_pre_synth_uniquify.rpt

####################################################################
## SET OPERATING CONDITIONS
####################################################################
set_operating_conditions -max SSG_0P59V_0P00V_0P00V_0P00V_M40C

####################################################################
## ADD CONSTRAINTS
####################################################################
source -echo -verbose ./scripts/constraints/alsaqr.clocks.sdc       > ${TRIAL_DIR}/reports/d06_constr_clk.rpt
#source -echo -verbose ./scripts/constraints/constraints.hyper.sdc        > ${TRIAL_DIR}/reports/d05_constr_hyper.rpt
#source -echo -verbose ./scripts/constraints/constraints.peripherals.sdc  > ${TRIAL_DIR}/reports/d07_constr_periphs.rpt
source -echo -verbose ./scripts/constraints/alsaqr.exceptions.sdc   > ${TRIAL_DIR}/reports/d08_constr_excep.rpt

####################################################################
## INSERT CLK GATING CELLS
####################################################################
# clock gating
identify_clock_gating
report_clock_gating -multi_stage -nosplit > ./${TRIAL_DIR}/reports/d09_clk_gating.rpt
set_preserve_clock_gate [all_clock_gates]
set_attribute [get_cells  $CLK_GATE_CELL  ] is_clock_gating_cell true 
set_attribute [get_cells  $CLK_GATE_CELL  ] clock_gating_integrated_cell latch_posedge_precontrol 
set_clock_gating_style -minimum_bitwidth 8 -positive_edge_logic integrated:$CLK_GATE_CELL -control_point  before  -control_signal scan_enable  -max_fanout 256

report_clocks                                                       > ./${TRIAL_DIR}/reports/d10_clocks.rpt

####################################################################
## UNGROUPING
####################################################################

#  
#  ####################################################################
#  ## CRITICAL RANGE (DEBUG ONLY)
#  ####################################################################
#  set_critical_range 200 *
#  
#  #set_dont_touch [get_cells vdd_core_pads*.i_vdd_core_pad]
#  #set_dont_touch [get_cells vdd_io_pads*.i_vdd_io_pad]
#  #set_dont_touch [get_cells i_vdd_pwr_on_ctr_io_pad]
#  #set_dont_touch [get_cells cluster_vdd_pads*.i_vdd_cluster_pad]
#  #set_dont_touch [get_cells vss_core_pads*.i_gnd_core_pad]
#  #set_dont_touch [get_cells vss_io_pads*.i_gnd_io_pad]
#  
#  ####################################################################
#  ## COMPILE ULTRA
#  ####################################################################
check_design                                              > ./${TRIAL_DIR}/reports/d11_check_design_precompile.rpt
compile_ultra -no_autoungroup -timing -gate_clock 
check_design                                              > ./${TRIAL_DIR}/reports/d12_check_design_postcompile.rpt

####################################################################
## POST SYNTHESIS UNIQUIFY 
####################################################################
set uniquify_naming_style "alsaqr_%s_%d"
uniquify -force                                           > ./${TRIAL_DIR}/reports/d13_uniquify_post_synth.rpt

####################################################################
## POST SYNTHESIS DDC
####################################################################
sh mkdir -p ./${TRIAL_DIR}/mapped
write -f ddc -hierarchy  -output ./${TRIAL_DIR}/mapped/alsaqr_postsyn.ddc

####################################################################
## POST SYNTHESIS NETLIST
####################################################################
change_names -rules verilog -hier
define_name_rules fixbackslashes -allowed "A-Za-z0-9_" -first_restricted "\\" -remove_chars
change_names -rule fixbackslashes -h
sh mkdir -p ./${TRIAL_DIR}/netlists
write -format verilog -hier -o ./${TRIAL_DIR}/netlists/alsaqr_chip.v

####################################################################
## REPORTS
####################################################################
report_timing      -nosplit                                                                                  > ./${TRIAL_DIR}/reports/timing.rpt
report_area  -hier -nosplit                                                                                  > ./${TRIAL_DIR}/reports/area.rpt
report_resources -hierarchy                                                                                  > ./${TRIAL_DIR}/reports/dp_resource.rpt
report_clock_gating                                                                                          > ./${TRIAL_DIR}/reports/clock_gating_postsyn.rpt
report_units                                                                                                 > ./${TRIAL_DIR}/reports/units.rpt
report_timing -through [ get_pins soc_domain_i/pulp_soc_i/fc_subsystem_i/FC_CORE_lFC_CORE/*                ] > ./${TRIAL_DIR}/reports/core.rpt
report_timing -through [ get_pins soc_domain_i/pulp_soc_i/fc_subsystem_i/FC_CORE_lFC_CORE/instr*           ] > ./${TRIAL_DIR}/reports/core_instr.rpt
report_timing -through [ get_pins soc_domain_i/pulp_soc_i/fc_subsystem_i/FC_CORE_lFC_CORE/data*            ] > ./${TRIAL_DIR}/reports/core_data.rpt
report_timing -through [ get_pins soc_domain_i/pulp_soc_i/fc_subsystem_i/FC_CORE_lFC_CORE/ex_stage_i/*     ] > ./${TRIAL_DIR}/reports/core_exstage.rpt
report_timing -through [ get_pins soc_domain_i/pulp_soc_i/fc_subsystem_i/FC_CORE_lFC_CORE/ex_stage_i/*fpu* ] > ./${TRIAL_DIR}/reports/core_fpu.rpt

report_timing -max_paths 10 -to SOC_CLK                                                                      > ./${TRIAL_DIR}/reports/timing_soc_clock.rpt
report_timing -max_paths 10 -to PER_CLK                                                                      > ./${TRIAL_DIR}/reports/timing_per_clock.rpt
report_timing -max_paths 10 -to CLU_CLK                                                                      > ./${TRIAL_DIR}/reports/timing_clu_clock.rpt
report_timing -max_paths 10 -to EPE_CLK                                                                      > ./${TRIAL_DIR}/reports/timing_epe_clock.rpt

####################################################################
## WRITE OUT CONSTRAINTS
####################################################################
write_sdc   ./${TRIAL_DIR}/constraints.sdc

####################################################################
## START GUI
####################################################################
sh date
sh echo "Current git version is `git rev-parse --short HEAD`"
sh echo "Synthesis of AlSaqr has finished."
start_gui
