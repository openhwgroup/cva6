######################################################################################################
## File Name : SpyGlass Goal Setup File
## Purpose   : This file contains commonly used parameters for some of the methodology goals. User can
##             further customize options, parameter values specific to a goal as required.
## Type      : This is a tcl compatible file and can read all native tcl commands along with SpyGlass
##             commands.
## Usage     : This file is read under SpyGlass Project File{.prj}.
#######################################################################################################

##Common Options used in a goal scope #################################################################
 # How to add a new rule(s) not present in a given goal, in the  goal scope? 
   # set_goal_option addrules {<Rule-Name#1> <Rule-Name#2>}
 # How to remove/disable the run of a rule(s) existing in a goal during goal run? 
   # set_goal_option ignorerules {<Rule-Name#1> <Rule-Name#2>}
 # Reading a goal specfic SGDC file
   # read_file -type sgdc <sgdc-file>
 # Reading a goal specfic Waiver file
   # read_file -type waiver <waiver-file>
########################################################################################################

## Goal:cdc/cdc_verify_struct ##################
   current_goal cdc/cdc_verify_struct 
   set_goal_option report {count moresimple moresimple_sevclass sign_off summary waiver CKSGDCInfo Clock-Reset-Summary CDC-report Ac_sync_group_detail Glitch_detailed CrossingInfo SynchInfo Clock-Reset-Detail}
   set_parameter dump_sync_info detailed 
   #set_parameter allow_combo_logic yes
   #set_parameter synchronize_cells { }
   #set_parameter synchronize_data_cells { }

## Goal:cdc/cdc_verify #########################
   current_goal cdc/cdc_verify
   set_goal_option report {count moresimple moresimple_sevclass sign_off summary waiver CKSGDCInfo Clock-Reset-Summary CDC-report Ac_sync_group_detail Glitch_detailed}
   set_parameter fa_atime 20
   set_parameter fa_scope block
   #set_parameter cdc_dump_assertions "sva"
   #set_parameter fa_dump_hybrid partial,fail
   #set_parameter allow_combo_logic yes
   #set_parameter synchronize_cells { }
   #set_parameter synchronize_data_cells { }
   #set_parameter fa_solvemethod 2
   #set_parameter fa_multicore yes
   #set_parameter fa_parallelfile <filename> 

## Goal:dft/dft_scan_ready ######################
   current_goal dft/dft_scan_ready
   set_parameter dftGenerateStuckAtFaultReport all
   #set_goal_option addrules Info_synthRedundant
   #set_goal_option addrules Info_untestable
   #set_parameter dft_ignore_constant_supply_flip_flops on
   #set_goal_option enable_const_prop_thru_seq yes
   #set_parameter dft_show_schematic_info_in_coverage_audit on

## Goal:dft/dft_best_practice ####################
   current_goal dft/dft_best_practice
   set_parameter dftGenerateStuckAtFaultReport all
   #set_goal_option addrules Info_synthRedundant
   #set_goal_option addrules Info_untestable
   #set_parameter dft_ignore_constant_supply_flip_flops on
   #set_goal_option enable_const_prop_thru_seq yes
   #set_parameter dft_show_schematic_info_in_coverage_audit on

## How to define a user specified/custom Goal ########################
## Here is an example of how to create a custom goal 'rdc_verify_struct' to run RDC rule 'Ar_resetcross01, Ar_resetcross_matrix01' 
   # define_goal rdc_verify_struct -policy { clock-reset } {
   # set_goal_option rules {Ar_resetcross01 Ar_resetcross_matrix01}
   # set_parameter report_for_single_busbit yes
   # }
## Goal: none to finish the scope of last goal in this file ######
   current_goal none
#####################################################################################################
