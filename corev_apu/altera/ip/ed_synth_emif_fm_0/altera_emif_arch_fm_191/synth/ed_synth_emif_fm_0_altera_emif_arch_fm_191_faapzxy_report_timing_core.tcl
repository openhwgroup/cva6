# (C) 2001-2024 Intel Corporation. All rights reserved.
# Your use of Intel Corporation's design tools, logic functions and other 
# software and tools, and its AMPP partner logic functions, and any output 
# files from any of the foregoing (including device programming or simulation 
# files), and any associated documentation or information are expressly subject 
# to the terms and conditions of the Intel Program License Subscription 
# Agreement, Intel FPGA IP License Agreement, or other applicable 
# license agreement, including, without limitation, that your use is for the 
# sole purpose of programming logic devices manufactured by Intel and sold by 
# Intel or its authorized distributors.  Please refer to the applicable 
# agreement for further details.




################################################################
# Helper function to add a report_timing-based analysis section
################################################################
proc ed_synth_emif_fm_0_altera_emif_arch_fm_191_faapzxy_add_report_timing_analysis {opcname inst var_array_name summary_name title from_clks to_clks from_nodes to_nodes } {

   #######################################
   # Need access to global variables
   upvar 1 $summary_name global_summary
   upvar 1 $var_array_name var

   set num_failing_path 10

   set setup_margin    999.9
   set hold_margin     999.9
   set recovery_margin 999.9
   set removal_margin  999.9

   set hold_only_corner [get_operating_conditions_info [get_operating_conditions] -is_hold_only]

   if {!$hold_only_corner && ([get_collection_size [get_timing_paths -from_clock $from_clks -to_clock $to_clks -from $from_nodes -to $to_nodes -npaths 1 -setup]] > 0)} {
      set res_0        [report_timing -quiet -detail full_path -from_clock $from_clks -to_clock $to_clks -from $from_nodes -to $to_nodes -npaths $num_failing_path -panel_name "$inst $title (setup)" -setup]
      set setup_margin [lindex $res_0 1]
   } else {
      set setup_margin "--"
   }

   if {[get_collection_size [get_timing_paths -from_clock $from_clks -to_clock $to_clks -from $from_nodes -to $to_nodes -npaths 1 -hold]] > 0} {
      set res_1        [report_timing -quiet -detail full_path -from_clock $from_clks -to_clock $to_clks -from $from_nodes -to $to_nodes -npaths $num_failing_path -panel_name "$inst $title (hold)" -hold]
      set hold_margin  [lindex $res_1 1]
   }

   if {$var(DIAG_TIMING_REGTEST_MODE)} {
      lappend global_summary [list $opcname 0 "$title ($opcname)" $setup_margin $hold_margin]
   }

   if {!$hold_only_corner && ([get_collection_size [get_timing_paths -from_clock $from_clks -to_clock $to_clks -from $from_nodes -to $to_nodes -npaths 1 -recovery]] > 0)} {
      set res_0           [report_timing -quiet -detail full_path -from_clock $from_clks -to_clock $to_clks -from $from_nodes -to $to_nodes -npaths $num_failing_path -panel_name "$inst $title (recovery)" -recovery]
      set recovery_margin [lindex $res_0 1]
   } else {
      set recovery_margin "--"
   }

   if {[get_collection_size [get_timing_paths -from_clock $from_clks -to_clock $to_clks -from $from_nodes -to $to_nodes -npaths 1 -removal]] > 0} {
      set res_1           [report_timing -quiet -detail full_path -from_clock $from_clks -to_clock $to_clks -from $from_nodes -to $to_nodes -npaths $num_failing_path -panel_name "$inst $title (removal)" -removal]
      set removal_margin  [lindex $res_1 1]
   } else {
      set removal_margin "--"
   }

   if {$var(DIAG_TIMING_REGTEST_MODE)} {
      lappend global_summary [list $opcname 0 "$title Recovery/Removal ($opcname)" $recovery_margin $removal_margin]
   }

   return [list $setup_margin $hold_margin $recovery_margin $removal_margin]
}

#############################################################
# Other Core-Logic related Timing Analysis
#############################################################

proc ed_synth_emif_fm_0_altera_emif_arch_fm_191_faapzxy_add_c2p_p2c_report_timing_analysis {opcname inst pin_array_name var_array_name summary_name title from_clks to_clks from_nodes to_nodes p2c} {

   #######################################
   # Need access to global variables
   upvar 1 $summary_name global_summary
   upvar 1 $var_array_name var
   upvar 1 $pin_array_name pins

   set num_failing_path 10

   set setup_margin    999.9
   set hold_margin     999.9
   set recovery_margin 999.9
   set removal_margin  999.9
   set debug 0

   set hold_only_corner [get_operating_conditions_info [get_operating_conditions] -is_hold_only]

   set positive_fcolour [list "black" "blue" "blue"]
   set negative_fcolour [list "black" "red"  "red"]
   set summary [list]

   # Get the periphery clocks
   if {$p2c} {
      set phyclks $from_clks
   } else {
      set phyclks $to_clks
   }

   # Set panel names
   set panel_name_setup  "$inst $title (setup)"
   set panel_name_hold   "$inst $title (hold)"
   set panel_name_recovery  "$inst $title (recovery)"
   set panel_name_removal   "$inst $title (removal)"	
   set disable_panel_color_flag ""
   set quiet_flag ""

   # Generate the default margins
   if {!$hold_only_corner} {
      set res_0        [report_timing -quiet -detail full_path -from_clock $from_clks -to_clock $to_clks -from $from_nodes -to $to_nodes -npaths $num_failing_path -panel_name $panel_name_setup -setup $disable_panel_color_flag $quiet_flag]
      set setup_margin [lindex $res_0 1]
   } else {
      set setup_margin "--"
   }
   set res_1        [report_timing -quiet -detail full_path -from_clock $from_clks -to_clock $to_clks -from $from_nodes -to $to_nodes -npaths $num_failing_path -panel_name $panel_name_hold -hold $disable_panel_color_flag $quiet_flag]
   set hold_margin  [lindex $res_1 1]

   set recovery_paths 0
   set removal_paths 0

   if {!$hold_only_corner && ([get_collection_size [get_timing_paths -from_clock $from_clks -to_clock $to_clks -from $from_nodes -to $to_nodes -npaths 1 -recovery]] > 0)} {
      set recovery_paths 1
      set res_2        [report_timing -quiet -detail full_path -from_clock $from_clks -to_clock $to_clks -from $from_nodes -to $to_nodes -npaths $num_failing_path -panel_name $panel_name_recovery -recovery $disable_panel_color_flag $quiet_flag]
      set recovery_margin [lindex $res_2 1]
   } else {
      set recovery_margin "--"
   }

   if {[get_collection_size [get_timing_paths -from_clock $from_clks -to_clock $to_clks -from $from_nodes -to $to_nodes -npaths 1 -removal]] > 0} {
      set removal_paths 1
      set res_3        [report_timing -quiet -detail full_path -from_clock $from_clks -to_clock $to_clks -from $from_nodes -to $to_nodes -npaths $num_failing_path -panel_name $panel_name_removal  -removal  $disable_panel_color_flag $quiet_flag]
	   set removal_margin  [lindex $res_3 1]
   } else {
	   set removal_margin  "--"
   }

   if {$var(DIAG_TIMING_REGTEST_MODE)} {
      lappend global_summary [list $opcname 0 "$title ($opcname)" $setup_margin $hold_margin]
      if {($recovery_paths == 1) || ($removal_paths == 1)} {
         lappend global_summary [list $opcname 0 "$title Recovery/Removal ($opcname)" $recovery_margin $hold_margin]
      }
   }

   return [list $setup_margin $hold_margin $recovery_margin $removal_margin]
}


proc ed_synth_emif_fm_0_altera_emif_arch_fm_191_faapzxy_perform_core_analysis {opcname inst pin_array_name var_array_name summary_name} {

   #######################################
   # Need access to global variables
   upvar 1 $summary_name global_summary
   upvar 1 $var_array_name var
   upvar 1 $pin_array_name pins
   global ::io_only_analysis

   # Debug switch. Change to 1 to get more run-time debug information
   set debug 0
   set result 1

   ###############################
   # PHY analysis
   ###############################

   set analysis_name "Core"

   if {$::io_only_analysis == 1} {
      set setup_slack "--"
      set hold_slack  "--"
      lappend global_summary [list $opcname 0 "$analysis_name ($opcname)" $setup_slack $hold_slack]
      post_message -type warning "Early EMIF IO timing estimate does not include core FPGA timing"
   } elseif {$var(IS_HPS)} {
      # No core timing analysis required by HPS interface
      set setup_slack "--"
      set hold_slack  "--"
      lappend global_summary [list $opcname 0 "$analysis_name ($opcname)" $setup_slack $hold_slack]
      lappend global_summary [list $opcname 0 "$analysis_name Recovery/Removal ($opcname)" $setup_slack $hold_slack]
   } else {

      set master_instname $pins(master_instname)
      set coreclkname [list ${master_instname}_core_usr_* ${master_instname}_core_afi_* ${master_instname}_core_dft_* ${master_instname}_ref_clock ${master_instname}_core_nios_clk [ed_synth_emif_fm_0_altera_emif_arch_fm_191_faapzxy_get_clock_name_from_pin_name $pins(pll_ref_clock)]]
      set coreclks [get_clocks -nowarn $coreclkname]

      set phyclkname [list ${inst}_phy_*]
      set phyclks [get_clocks -nowarn $phyclkname]

      set emif_regs [get_registers $inst|*]
      set rest_regs [remove_from_collection [all_registers] $emif_regs]

      set setup_margin    999.9
      set hold_margin     999.9
      set recovery_margin 999.9
      set removal_margin  999.9

      # Core/periphery transfers

      # Core-to-periphery
      set res [ed_synth_emif_fm_0_altera_emif_arch_fm_191_faapzxy_add_c2p_p2c_report_timing_analysis $opcname $inst $pin_array_name var global_summary "Core To Periphery" $coreclks $phyclks "*" $emif_regs 0]
      set setup_margin    [min $setup_margin    [lindex $res 0]]
      set hold_margin     [min $hold_margin     [lindex $res 1]]
      set recovery_margin [min $recovery_margin [lindex $res 2]]
      set removal_margin  [min $removal_margin  [lindex $res 3]]

      # Periphery-to-core
      set res [ed_synth_emif_fm_0_altera_emif_arch_fm_191_faapzxy_add_c2p_p2c_report_timing_analysis $opcname $inst $pin_array_name var global_summary "Periphery To Core" $phyclks $coreclks $emif_regs "*" 1]
      set setup_margin    [min $setup_margin    [lindex $res 0]]
      set hold_margin     [min $hold_margin     [lindex $res 1]]
      set recovery_margin [min $recovery_margin [lindex $res 2]]
      set removal_margin  [min $removal_margin  [lindex $res 3]]

      # Pure Core transfers

      set_active_clocks [remove_from_collection [all_clocks] $phyclks]

      # EMIF logic within FPGA core
      set res [ed_synth_emif_fm_0_altera_emif_arch_fm_191_faapzxy_add_report_timing_analysis $opcname $inst var global_summary "Within Core" $coreclks $coreclks $emif_regs $emif_regs]
      set setup_margin    [min $setup_margin    [lindex $res 0]]
      set hold_margin     [min $hold_margin     [lindex $res 1]]
      set recovery_margin [min $recovery_margin [lindex $res 2]]
      set removal_margin  [min $removal_margin  [lindex $res 3]]

      # Transfers between EMIF and user logic
      set res [ed_synth_emif_fm_0_altera_emif_arch_fm_191_faapzxy_add_report_timing_analysis $opcname $inst var global_summary "IP to User Logic" "*" "*" $emif_regs $rest_regs]
      set setup_margin    [min $setup_margin    [lindex $res 0]]
      set hold_margin     [min $hold_margin     [lindex $res 1]]
      set recovery_margin [min $recovery_margin [lindex $res 2]]
      set removal_margin  [min $removal_margin  [lindex $res 3]]

      # Transfers between user and EMIF logic
      set res [ed_synth_emif_fm_0_altera_emif_arch_fm_191_faapzxy_add_report_timing_analysis $opcname $inst var global_summary "User Logic to IP" "*" "*" $rest_regs $emif_regs]
      set setup_margin    [min $setup_margin    [lindex $res 0]]
      set hold_margin     [min $hold_margin     [lindex $res 1]]
      set recovery_margin [min $recovery_margin [lindex $res 2]]
      set removal_margin  [min $removal_margin  [lindex $res 3]]

      # Transfers within non-EMIF logic (not reported by default since they are irrelevant to EMIF IP)
      if {$var(DIAG_TIMING_REGTEST_MODE)} {
         set res [ed_synth_emif_fm_0_altera_emif_arch_fm_191_faapzxy_add_report_timing_analysis $opcname $inst var global_summary "Within User Logic" $coreclks $coreclks $rest_regs $rest_regs]
         set setup_margin    [min $setup_margin    [lindex $res 0]]
         set hold_margin     [min $hold_margin     [lindex $res 1]]
         set recovery_margin [min $recovery_margin [lindex $res 2]]
         set removal_margin  [min $removal_margin  [lindex $res 3]]
      }

      set_active_clocks [all_clocks]

      lappend global_summary [list $opcname 0 "$analysis_name ($opcname)" $setup_margin $hold_margin]
      lappend global_summary [list $opcname 0 "$analysis_name Recovery/Removal ($opcname)" $recovery_margin $removal_margin]
   }
}


