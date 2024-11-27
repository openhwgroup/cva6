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


#####################################################################
#
# THIS IS AN AUTO-GENERATED FILE!
# -------------------------------
# If you modify this files, all your changes will be lost if you
# regenerate the core!
#
# FILE DESCRIPTION
# ----------------
# This file specifies the timing constraints of the memory device and
# of the memory interface

# ------------------------------------------- #
# -                                         - #
# --- Some useful functions and variables --- #
# -                                         - #
# ------------------------------------------- #

set script_dir [file dirname [info script]]
source "$script_dir/ed_synth_emif_fm_0_altera_emif_arch_fm_191_faapzxy_ip_parameters.tcl"
source "$script_dir/ed_synth_emif_fm_0_altera_emif_arch_fm_191_faapzxy_parameters.tcl"
source "$script_dir/ed_synth_emif_fm_0_altera_emif_arch_fm_191_faapzxy_pin_map.tcl"

#--------------------------------------------#
# -                                        - #
# --- Determine when SDC is being loaded --- #
# -                                        - #
#--------------------------------------------#

set syn_flow 0
set sta_flow 0
set fit_flow 0
set pow_flow 0
if { $::TimeQuestInfo(nameofexecutable) == "quartus_map" || $::TimeQuestInfo(nameofexecutable) == "quartus_syn" } {
   set syn_flow 1
} elseif { $::TimeQuestInfo(nameofexecutable) == "quartus_sta" } {
   set sta_flow 1
} elseif { $::TimeQuestInfo(nameofexecutable) == "quartus_fit" } {
   set fit_flow 1
} elseif { $::TimeQuestInfo(nameofexecutable) == "quartus_pow" } {
   set pow_flow 1
}
set ::io_only_analysis 0

# ------------------------ #
# -                      - #
# --- GENERAL SETTINGS --- #
# -                      - #
# ------------------------ #

# This is a global setting and will apply to the whole design.
# This setting is required for the memory interface to be
# properly constrained.
derive_clock_uncertainty

# Debug switch. Change to 1 to get more run-time debug information
set debug 0

# All timing requirements will be represented in nanoseconds with up to 3 decimal places of precision
set_time_format -unit ns -decimal_places 3

# Determine if entity names are on
set entity_names_on [ ed_synth_emif_fm_0_altera_emif_arch_fm_191_faapzxy_are_entity_names_on ]

# ---------------------- #
# -                    - #
# --- DERIVED TIMING --- #
# -                    - #
# ---------------------- #

# PLL multiplier to mem clk
regexp {([0-9\.]+) ps} $var(PLL_REF_CLK_FREQ_PS_STR) match var(PHY_REF_CLK_FREQ_PS)
regexp {([0-9\.]+) ps} $var(PLL_VCO_FREQ_PS_STR) match var(PHY_VCO_FREQ_PS)
set pll_multiplier [ ed_synth_emif_fm_0_altera_emif_arch_fm_191_faapzxy_round_3dp [expr $var(PHY_MEM_CLK_FREQ_MHZ)/$var(PHY_REF_CLK_FREQ_MHZ)] ]
set vco_multiplier [expr int($var(PHY_REF_CLK_FREQ_PS)/$var(PHY_VCO_FREQ_PS))]

# Half of memory clock cycle
set half_period [ ed_synth_emif_fm_0_altera_emif_arch_fm_191_faapzxy_round_3dp [ expr $var(UI) / 2.0 ] ]

# Half of reference clock
set ref_period      [ ed_synth_emif_fm_0_altera_emif_arch_fm_191_faapzxy_round_3dp [ expr $var(PHY_REF_CLK_FREQ_PS)/1000.0] ]
set ref_half_period [ ed_synth_emif_fm_0_altera_emif_arch_fm_191_faapzxy_round_3dp [ expr $ref_period / 2.0 ] ]

# Other clock periods
set tCK_AFI     [ ed_synth_emif_fm_0_altera_emif_arch_fm_191_faapzxy_round_3dp [ expr 1000.0/$var(PHY_MEM_CLK_FREQ_MHZ)*$var(USER_CLK_RATIO) ] ]
set tCK_C2P_P2C [ ed_synth_emif_fm_0_altera_emif_arch_fm_191_faapzxy_round_3dp [ expr 1000.0/$var(PHY_MEM_CLK_FREQ_MHZ)*$var(C2P_P2C_CLK_RATIO) ] ]
set tCK_PHY     [ ed_synth_emif_fm_0_altera_emif_arch_fm_191_faapzxy_round_3dp [ expr 1000.0/$var(PHY_MEM_CLK_FREQ_MHZ)*$var(PHY_HMC_CLK_RATIO) ] ]

# Asymmetric uncertainties on address and command paths
set ac_min_delay [ ed_synth_emif_fm_0_altera_emif_arch_fm_191_faapzxy_round_3dp [ expr - $var(tIH) + $var(CA_TO_CK_BD_PKG_SKEW) ]]
set ac_max_delay [ ed_synth_emif_fm_0_altera_emif_arch_fm_191_faapzxy_round_3dp [ expr   $var(tIS) + $var(CA_TO_CK_BD_PKG_SKEW) ]]

# ---------------------- #
# -                    - #
# --- INTERFACE RATE --- #
# -                    - #
# ---------------------- #

# -------------------------------------------------------------------- #
# -                                                                  - #
# --- This is the main call to the netlist traversal routines      --- #
# --- that will automatically find all pins and registers required --- #
# --- to apply timing constraints.                                 --- #
# --- During the fitter, the routines will be called only once     --- #
# --- and cached data will be used in all subsequent calls.        --- #
# -                                                                  - #
# -------------------------------------------------------------------- #

if { ! [ info exists ed_synth_emif_fm_0_altera_emif_arch_fm_191_faapzxy_sdc_cache ] } {
   ed_synth_emif_fm_0_altera_emif_arch_fm_191_faapzxy_initialize_ddr_db ed_synth_emif_fm_0_altera_emif_arch_fm_191_faapzxy_ddr_db var
   set ed_synth_emif_fm_0_altera_emif_arch_fm_191_faapzxy_sdc_cache 1
} else {
   if { $debug } {
      post_message -type info "SDC: reusing cached DDR DB"
   }
}

# ------------------------------------------------------------- #
# -                                                           - #
# --- If multiple instances of this core are present in the --- #
# --- design they will all be constrained through the       --- #
# --- following loop                                        --- #
# -                                                           - #
# ------------------------------------------------------------- #

set instances [ array names ed_synth_emif_fm_0_altera_emif_arch_fm_191_faapzxy_ddr_db ]
foreach { inst } $instances {
   if { [ info exists pins ] } {
      unset pins
   }
   array set pins $ed_synth_emif_fm_0_altera_emif_arch_fm_191_faapzxy_ddr_db($inst)

   # ----------------------- #
   # -                     - #
   # --- REFERENCE CLOCK --- #
   # -                     - #
   # ----------------------- #

   # First determine if a reference clock has already been created (i.e. Reference clock sharing)
   set ref_clock_exists [ ed_synth_emif_fm_0_altera_emif_arch_fm_191_faapzxy_does_ref_clk_exist $pins(pll_ref_clock) ]
   if { $ref_clock_exists == 0 }  {
      # This is the reference clock used by the PLL to derive any other clock in the core
      create_clock -period "$var(PHY_REF_CLK_FREQ_MHZ)MHz" -waveform [ list 0 $ref_half_period ] $pins(pll_ref_clock) -add -name ${inst}_ref_clock
   }
   set pins(ref_clock_name) [ed_synth_emif_fm_0_altera_emif_arch_fm_191_faapzxy_get_clock_name_from_pin_name $pins(pll_ref_clock)]

   # ------------------ #
   # -                - #
   # --- PLL CLOCKS --- #
   # -                - #
   # ------------------ #

   # VCO clock
   #We also detect and save the index of the clocks that drive the CPAs
   set is_master [expr {([string compare $inst $pins(master_instname)] == 0) ? 1 : 0}]
   set i_vco_clock 0
   set i_cpa_clock_tile_pri -1
   set i_cpa_clock_tile_sec -1
   foreach { vco_clock } $pins(pll_vco_clock) {

      set suffix "_${i_vco_clock}"
      if {$vco_clock == $pins(master_vco_clock)} {
         set suffix ""
         if {$is_master} {
            set i_cpa_clock_tile_pri $i_vco_clock
         }
      } elseif {$vco_clock == $pins(master_vco_clock_sec)} {
         if {$is_master} {
            set i_cpa_clock_tile_sec $i_vco_clock
         }
      }

      set local_pll_vco_clk_${i_vco_clock} [ ed_synth_emif_fm_0_altera_emif_arch_fm_191_faapzxy_get_or_add_generated_clock \
         -target $vco_clock \
         -name "${inst}_vco_clk${suffix}" \
         -source $pins(pll_ref_clock) \
         -multiply_by [expr $vco_multiplier ]  \
         -divide_by 1 \
         -phase 0 ]
      incr i_vco_clock
   }
   
   if {! $var(IS_HPS)} {
      if {$is_master} {
         if {$i_cpa_clock_tile_pri == -1} {
            post_message -type critical_warning "Failed to find CPA clock index"
         }
         if {$i_cpa_clock_tile_sec == -1 && $var(PHY_PING_PONG_EN)} {
            post_message -type critical_warning "Failed to find CPA clock index for secondary interface"
         }
      }
   }

   # Core clocks
   set core_clocks [list]
   set core_clocks_local [list]

   # Skip if we're in HPS mode since there's no user accessible core clock
   # and there's no transfers within core fabric to analyze
   if {! $var(IS_HPS)} {

      set local_pll_master_vco_clock [ ed_synth_emif_fm_0_altera_emif_arch_fm_191_faapzxy_get_or_add_generated_clock \
         -target $pins(master_vco_clock) \
         -name "${pins(master_instname)}_vco_clk" \
         -source $pins(pll_ref_clock) \
         -multiply_by [expr $vco_multiplier ]  \
         -divide_by 1 \
         -phase 0 ]

      # emif_usr_clk
      # Clock only exists when HMC is used.
      set local_core_usr_clock ""
      if {$pins(master_core_usr_clock) != ""} {
         set name "core_usr_clk"
         set master_core_clock $pins(master_core_usr_clock)
         set divide_by [expr {$var(PLL_VCO_TO_MEM_CLK_FREQ_RATIO) * $var(USER_CLK_RATIO)}]
         set phase [expr {$var(PLL_PHY_CLK_VCO_PHASE) * 45.0 / $divide_by}]

         set local_core_usr_clock [ ed_synth_emif_fm_0_altera_emif_arch_fm_191_faapzxy_get_or_add_generated_clock \
            -target $master_core_clock \
            -name "${pins(master_instname)}_${name}" \
            -source $pins(master_vco_clock) \
            -multiply_by 1 \
            -divide_by $divide_by\
            -phase $phase ]

         lappend core_clocks $pins(master_core_usr_clock)
         lappend core_clocks_local $local_core_usr_clock 
      }
      
      # emif_usr_clk_sec
      # Clock only exists when ping-pong HMC is used
      set local_core_usr_clock_sec ""
      if {$pins(master_core_usr_clock_sec) != ""} {
         set name "core_usr_clk_sec"
         set master_core_clock_sec $pins(master_core_usr_clock_sec)
         set divide_by [expr {$var(PLL_VCO_TO_MEM_CLK_FREQ_RATIO) * $var(USER_CLK_RATIO)}]
         set phase [expr {$var(PLL_PHY_CLK_VCO_PHASE) * 45.0 / $divide_by}]

         set local_core_usr_clock_sec [ ed_synth_emif_fm_0_altera_emif_arch_fm_191_faapzxy_get_or_add_generated_clock \
            -target $master_core_clock_sec \
            -name "${pins(master_instname)}_${name}" \
            -source $pins(master_vco_clock_sec) \
            -multiply_by 1 \
            -divide_by $divide_by\
            -phase $phase ]

         lappend core_clocks $pins(master_core_usr_clock_sec)
         lappend core_clocks_local $local_core_usr_clock_sec 
      }      

      # emif_usr_half_clk
      # Clock only exists when HMC is used and in 2x bridge mode
      set local_core_usr_half_clock ""
      if {$pins(master_core_usr_half_clock) != ""} {
         set name "core_usr_half_clk"
         set master_core_clock $pins(master_core_usr_half_clock)
         set divide_by [expr {$var(PLL_VCO_TO_MEM_CLK_FREQ_RATIO) * $var(USER_CLK_RATIO) * 2}]
         set phase [expr {$var(PLL_PHY_CLK_VCO_PHASE) * 45.0 / $divide_by}]

         set local_core_usr_half_clock [ ed_synth_emif_fm_0_altera_emif_arch_fm_191_faapzxy_get_or_add_generated_clock \
            -target $master_core_clock \
            -name "${pins(master_instname)}_${name}" \
            -source $pins(master_vco_clock) \
            -multiply_by 1 \
            -divide_by $divide_by\
            -phase $phase ]

         lappend core_clocks $pins(master_core_usr_half_clock)
         lappend core_clocks_local $local_core_usr_half_clock
      }
      
      # emif_usr_half_clk
      # Clock only exists when ping-pong HMC is used and in 2x bridge mode
      set local_core_usr_half_clock_sec ""
      if {$pins(master_core_usr_half_clock_sec) != ""} {
         set name "core_usr_half_clk_sec"
         set master_core_clock_sec $pins(master_core_usr_half_clock_sec)
         set divide_by [expr {$var(PLL_VCO_TO_MEM_CLK_FREQ_RATIO) * $var(USER_CLK_RATIO) * 2}]
         set phase [expr {$var(PLL_PHY_CLK_VCO_PHASE) * 45.0 / $divide_by}]

         set local_core_usr_half_clock [ ed_synth_emif_fm_0_altera_emif_arch_fm_191_faapzxy_get_or_add_generated_clock \
            -target $master_core_clock_sec \
            -name "${pins(master_instname)}_${name}" \
            -source $pins(master_vco_clock_sec) \
            -multiply_by 1 \
            -divide_by $divide_by\
            -phase $phase ]

         lappend core_clocks $pins(master_core_usr_half_clock_sec)
         lappend core_clocks_local $local_core_usr_half_clock
      }      

      # afi_clk
      # Clock only exists when HMC isn't used.
      set local_core_afi_clock ""
      if {$pins(master_core_afi_clock) != ""} {
         set name "core_afi_clk"
         set master_core_clock $pins(master_core_afi_clock)
         if {$var(USER_CLK_RATIO) == 8} {
            set divide_by [expr {$var(PLL_VCO_TO_MEM_CLK_FREQ_RATIO) * $var(USER_CLK_RATIO) / 2}]
         } else {
            set divide_by [expr {$var(PLL_VCO_TO_MEM_CLK_FREQ_RATIO) * $var(USER_CLK_RATIO)}]
         }
         set phase [expr {$var(PLL_PHY_CLK_VCO_PHASE) * 45.0 / $divide_by}]

         set local_core_afi_clock [ ed_synth_emif_fm_0_altera_emif_arch_fm_191_faapzxy_get_or_add_generated_clock \
            -target $master_core_clock \
            -name "${pins(master_instname)}_${name}" \
            -source $pins(master_vco_clock) \
            -multiply_by 1 \
            -divide_by $divide_by\
            -phase $phase ]

         lappend core_clocks $pins(master_core_afi_clock)
         lappend core_clocks_local $local_core_afi_clock
      }

      # extra CPA output for PE test purpose.
      set local_core_dft_cpa_1_clock "" 
      if {$pins(master_core_dft_cpa_1_clock) != ""} {
         set name "core_dft_cpa_1_clk"
         set master_core_clock $pins(master_core_dft_cpa_1_clock)
         set divide_by [expr {$var(PLL_VCO_TO_MEM_CLK_FREQ_RATIO) * $var(USER_CLK_RATIO)}]
         set phase [expr {$var(PLL_PHY_CLK_VCO_PHASE) * 45.0 / $divide_by}]

         set local_core_dft_cpa_1_clock [ ed_synth_emif_fm_0_altera_emif_arch_fm_191_faapzxy_get_or_add_generated_clock \
            -target $master_core_clock \
            -name "${pins(master_instname)}_${name}" \
            -source $pins(master_vco_clock) \
            -multiply_by 1 \
            -divide_by $divide_by\
            -phase $phase ]

         lappend core_clocks $pins(master_core_dft_cpa_1_clock)
         lappend core_clocks_local $local_core_dft_cpa_1_clock
      }
      
      # Calibration master logic clock
      if {$pins(master_cal_master_clk) != ""} {
         set pll_cal_master_clk [get_pins -nowarn $pins(master_cal_master_clk)]

         if {[get_collection_size $pll_cal_master_clk] > 0} {
            set name              "core_cal_master_clk"
            set master_core_clock $pins(master_cal_master_clk)
            set divide_by         $var(pll_c4_cnt) 
            set phase             [expr { [lindex $var(PLL_C_CNT_PHASE_PS_STR_4) 0] * 360.0 / $var(PHY_VCO_FREQ_PS) / $var(pll_c4_cnt) } ]
            set duty_cyc          $var(PLL_C_CNT_DUTY_CYCLE_4)
            
            set local_cal_master_clock [ ed_synth_emif_fm_0_altera_emif_arch_fm_191_faapzxy_get_or_add_generated_clock \
               -target $master_core_clock \
               -name "${pins(master_instname)}_${name}" \
               -source $pins(master_vco_clock) \
               -multiply_by 1  \
               -divide_by $divide_by  \
               -phase $phase \
               -duty_cycle $duty_cyc ]

            lappend core_clocks $pins(master_cal_master_clk)
            lappend core_clocks_local $local_cal_master_clock
         }
      }
      
      # Calibration slave logic clock
      if {$pins(master_cal_slave_clk) != ""} {
         set pll_cal_slave_clk [get_pins -nowarn $pins(master_cal_slave_clk)]

         if {[get_collection_size $pll_cal_slave_clk] > 0} {
            set name              "core_cal_slave_clk"
            set master_core_clock $pins(master_cal_slave_clk)
            set divide_by         $var(pll_c3_cnt) 
            set phase             [expr { [lindex $var(PLL_C_CNT_PHASE_PS_STR_3) 0] * 360.0 / $var(PHY_VCO_FREQ_PS) / $var(pll_c3_cnt) } ]
            set duty_cyc          $var(PLL_C_CNT_DUTY_CYCLE_3)
            
            set local_cal_slave_clock [ ed_synth_emif_fm_0_altera_emif_arch_fm_191_faapzxy_get_or_add_generated_clock \
               -target $master_core_clock \
               -name "${pins(master_instname)}_${name}" \
               -source $pins(master_vco_clock) \
               -multiply_by 1  \
               -divide_by $divide_by  \
               -phase $phase \
               -duty_cycle $duty_cyc ]

            lappend core_clocks $pins(master_cal_slave_clk)
            lappend core_clocks_local $local_cal_slave_clock
         }
      }

      # Optional PLL Extra clocks
      for {set i_extra_clk 0} {$i_extra_clk < $var(PLL_NUM_OF_EXTRA_CLKS)} {incr i_extra_clk} {
         set pll_extra_clk [get_pins -nowarn $pins(pll_extra_clk_${i_extra_clk})]

         # PLL counter may not exist if clock isn't actually connected and used
         if {[get_collection_size $pll_extra_clk] > 0} {
            set i_clk_cnt_num     [expr {$i_extra_clk + $var(pll_num_of_reserved_cnts)}]
            set name              "core_extra_clk_${i_extra_clk}"
            set master_core_clock $pins(pll_extra_clk_${i_extra_clk})
            set divide_by         $var(pll_c${i_clk_cnt_num}_cnt)
            set phase             [expr { [lindex $var(PLL_C_CNT_PHASE_PS_STR_${i_clk_cnt_num}) 0] * 360.0 / $var(PHY_VCO_FREQ_PS) / $var(pll_c${i_clk_cnt_num}_cnt) } ]
            set duty_cyc          $var(PLL_C_CNT_DUTY_CYCLE_${i_clk_cnt_num})

            set local_pll_extra_clock [ ed_synth_emif_fm_0_altera_emif_arch_fm_191_faapzxy_get_or_add_generated_clock \
               -target $master_core_clock \
               -name "${pins(master_instname)}_${name}" \
               -source $pins(master_vco_clock) \
               -multiply_by 1  \
               -divide_by $divide_by  \
               -phase $phase \
               -duty_cycle $duty_cyc ]
         }
      }
   }

   # Periphery clocks
   set periphery_clocks [list]
   set i_phy_clock 0
   foreach { phy_clock } $pins(pll_phy_clock) {
      set divide_by [expr {$var(PLL_VCO_TO_MEM_CLK_FREQ_RATIO) * $var(PHY_HMC_CLK_RATIO)}]
      set phase [expr {$var(PLL_PHY_CLK_VCO_PHASE) * 45.0 / $divide_by}]

      set local_phy_clk_${i_phy_clock} [ ed_synth_emif_fm_0_altera_emif_arch_fm_191_faapzxy_get_or_add_generated_clock \
         -target $phy_clock \
         -name "${inst}_phy_clk_${i_phy_clock}" \
         -source [lindex $pins(pll_vco_clock) $i_phy_clock] \
         -multiply_by 1 \
         -divide_by $divide_by \
         -phase $phase ]
      lappend periphery_clocks [set local_phy_clk_${i_phy_clock}]
      incr i_phy_clock
   }

   set i_phy_clock_l 0
   foreach { phy_clock_l } $pins(pll_phy_clock_l) {
      set divide_by [expr {$var(PLL_VCO_TO_MEM_CLK_FREQ_RATIO) * $var(C2P_P2C_CLK_RATIO)}]
      set phase [expr {$var(PLL_PHY_CLK_VCO_PHASE) * 45.0 / $divide_by}]

      set local_phy_clk_l_${i_phy_clock_l} [ ed_synth_emif_fm_0_altera_emif_arch_fm_191_faapzxy_get_or_add_generated_clock \
         -target $phy_clock_l \
         -name "${inst}_phy_clk_l_${i_phy_clock_l}" \
         -source [lindex $pins(pll_vco_clock) $i_phy_clock_l] \
         -multiply_by 1 \
         -divide_by $divide_by \
         -phase $phase ]
      lappend periphery_clocks [set local_phy_clk_l_${i_phy_clock_l}]
      incr i_phy_clock_l
   }

   # ------------------------ #
   # -                      - #
   # --- WRITE FIFO CLOCK --- #
   # -                      - #
   # ------------------------ #

   set write_fifo_clk [get_keepers ${inst}*|tile_gen[*].lane_gen[*].lane_inst|lane_inst~out_phy_reg]

   set i_wf_clock 0
   foreach_in_collection wf_clock $write_fifo_clk {
      set vco_clock_id [ed_synth_emif_fm_0_altera_emif_arch_fm_191_faapzxy_get_vco_clk_id $wf_clock var]
      if {$vco_clock_id == -1} {
         post_message -type critical_warning "Failed to find VCO clock"
      } else {
         set local_wf_clk_${i_wf_clock} [ ed_synth_emif_fm_0_altera_emif_arch_fm_191_faapzxy_get_or_add_generated_clock \
           -target [get_node_info -name $wf_clock] \
           -name "${inst}_wf_clk_${i_wf_clock}" \
           -source [get_node_info -name $vco_clock_id] \
           -multiply_by 1 \
           -divide_by [expr $var(PLL_VCO_TO_MEM_CLK_FREQ_RATIO)] \
           -phase 0 ]        
      }   
      incr i_wf_clock     
   }      

   # ---------------- #
   # -              - #
   # --- A/C PATH --- #
   # -              - #
   # ---------------- #

   # Only during the Fitter do we need to have constraints to allow for auto-delay chain code to
   # pick appropirate good settings
   # Also, only need it if address/command is not calibrated
   if {($fit_flow == 1) && ($var(CA_DESKEW) == 0)} {

      # First, define CK and CK#clocks because A/C timing is defined w.r.t. to these.
      set master_ck_clock ""
      foreach ac_clk_pin $pins(ac_clk) ac_clk_pin_n $pins(ac_clk_n) {
         set master_ck_clock [get_fanins $ac_clk_pin]
         foreach_in_collection check_pin $master_ck_clock {
            set check_pin_name [get_node_info -name $check_pin]
            if {[regexp {out_phy_reg$} $check_pin_name]} {
               set master_ck_clock $check_pin_name
               break
            }
         }
         create_generated_clock -multiply_by 1 -source $master_ck_clock $ac_clk_pin -name $ac_clk_pin     
         create_generated_clock -multiply_by 1 -invert -source $master_ck_clock $ac_clk_pin_n -name $ac_clk_pin_n     
      }
   
      foreach { ac_clk_pin } $pins(ac_clk) {
         # ac_pins can contain input ports such as mem_err_out_n
         # Loop through each ac pin to make sure we only apply set_output_delay to output ports
         foreach { ac_pin } $pins(ac_sync) {
            set ac_port [ get_ports $ac_pin ]
            if {[get_collection_size $ac_port] > 0} {
               if [ get_port_info -is_output_port $ac_port ] {
                  # Specifies the minimum delay difference between the DQS pin and the address/control pins:
                  set_output_delay -min $ac_min_delay -clock [get_clocks $ac_clk_pin] $ac_port -add_delay

                  # Specifies the maximum delay difference between the DQS pin and the address/control pins:
                  set_output_delay -max $ac_max_delay -clock [get_clocks $ac_clk_pin] $ac_port -add_delay
               }
            }
         }
      }
   } else {
      set_false_path -to $pins(ac_sync)
      set_output_delay -clock $pins(ref_clock_name) 0 $pins(ac_sync)
   }


   # ----------------- #
   # -               - #
   # --- READ PATH --- #
   # -               - #
   # ----------------- #

   foreach { read_clock } $pins(rclk) {
      create_clock -period "$var(PHY_MEM_CLK_FREQ_MHZ)MHz" -waveform [ list 0 $half_period ] $read_clock -name ${read_clock}_IN -add
   }

   # ------------------------------ #
   # -                            - #
   # --- MULTICYCLE CONSTRAINTS --- #
   # -                            - #
   # ------------------------------ #
   
   if {!$var(IS_HPS)} {

      # Relax timing to the input of the synchronizer for the local_reset_req signal
      # setup=7 and hold=6 are somewhat arbitrary choices
      if {$is_master} {
         set tmp "${inst}|arch|arch_inst|non_hps.core_clks_rsts_inst|local_reset_req_sync_gen_master.local_reset_req_sync_inst|din_s1"
         set tmp_pin [get_pins -nowarn [list "${tmp}|d" "${tmp}|*data"]]
         set tmp_reg [get_registers -nowarn $tmp]
         if {$fit_flow == 1} {
            set_multicycle_path -through $tmp_pin -to $tmp -setup 7 -end
            set_multicycle_path -through $tmp_pin -to $tmp -hold  6 -end
         } else {
            set_false_path -through $tmp_pin -to $tmp_reg
         }
      }

      # Soft reset synchronizers
      # See RTL for the justification of setup=7 and hold=6
      set tmp "${inst}|arch|arch_inst|non_hps.core_clks_rsts_inst|*reset_sync*"
      set tmp_pin [get_pins -nowarn ${inst}|arch|arch_inst|non_hps.core_clks_rsts_inst|*reset_sync*|clrn]
      set tmp_reg [get_registers -nowarn $tmp]
      if {[get_collection_size $tmp_pin] > 0} {
         if {$fit_flow == 1} {
            set_multicycle_path -through $tmp_pin -to $tmp -setup 7 -end
            set_multicycle_path -through $tmp_pin -to $tmp -hold 6 -end
         } else {
            set_false_path -through $tmp_pin -to $tmp_reg
         }
      }

      # seq2core_reset_done comes out of the PHY at up to 666MHz. Needs to be treated as async with synchronizer in the core.
      # setup=7 and hold=6 are somewhat arbitrary choices
      set tmp "${inst}|arch|arch_inst|seq_if_inst|non_hps.seq2core_reset_done_sync_inst|din_s1"
      set tmp_pin [get_pins -nowarn [list "${tmp}|d" "${tmp}|*data"]]
      set tmp_reg [get_registers -nowarn $tmp]
      if {[get_collection_size $tmp_pin] > 0} {
         if {$fit_flow == 1} {
            set_multicycle_path -through $tmp_pin -to $tmp -setup 7 -end
            set_multicycle_path -through $tmp_pin -to $tmp -hold  6 -end
         } else {
            set_false_path -through $tmp_pin -to $tmp_reg
         }
      }      
      
      # ac_parity_err 
      # setup=7 and hold=6 are somewhat arbitrary choices
      set tmp "${inst}|arch|arch_inst|seq_if_inst|non_hps.seq2core_ac_parity_sync_inst|din_s1"
      set tmp_pin [get_pins -nowarn [list "${tmp}|d" "${tmp}|*data"]]
      set tmp_reg [get_registers -nowarn $tmp]
      if {[get_collection_size $tmp_pin] > 0} {
         if {$fit_flow == 1} {
            set_multicycle_path -through $tmp_pin -to $tmp -setup 7 -end
            set_multicycle_path -through $tmp_pin -to $tmp -hold  6 -end
         } else {
            set_false_path -through $tmp_pin -to $tmp_reg
         }      
      }

      # afi_cal_in_progress (used by cal_counter module)
      # setup=7 and hold=6 are somewhat arbitrary choices
      set tmp "${inst}|arch|arch_inst|seq_if_inst|non_hps.afi_cal_in_progress_sync_inst|din_s1"
      set tmp_pin [get_pins -nowarn [list "${tmp}|d" "${tmp}|*data"]]
      set tmp_reg [get_registers -nowarn $tmp]
      if {[get_collection_size $tmp_pin] > 0} {
         if {$fit_flow == 1} {
            set_multicycle_path -through $tmp_pin -to $tmp -setup 7 -end
            set_multicycle_path -through $tmp_pin -to $tmp -hold  6 -end
         } else {
            set_false_path -through $tmp_pin -to $tmp_reg
         }      
      }
      
      # afi_cal_success
      # setup=7 and hold=6 are somewhat arbitrary choices
      set tmp "${inst}|arch|arch_inst|seq_if_inst|non_hps.afi_cal_success_sync_inst|din_s1"
      set tmp_pin [get_pins -nowarn [list "${tmp}|d" "${tmp}|*data"]]
      set tmp_reg [get_registers -nowarn $tmp]
      if {[get_collection_size $tmp_pin] > 0} {
         if {$fit_flow == 1} {
            set_multicycle_path -through $tmp_pin -to $tmp -setup 7 -end
            set_multicycle_path -through $tmp_pin -to $tmp -hold  6 -end
         } else {
            set_false_path -through $tmp_pin -to $tmp_reg
         }
      }      
      
      # afi_cal_fail
      # setup=7 and hold=6 are somewhat arbitrary choices
      set tmp "${inst}|arch|arch_inst|seq_if_inst|non_hps.afi_cal_fail_sync_inst|din_s1"
      set tmp_pin [get_pins -nowarn [list "${tmp}|d" "${tmp}|*data"]]
      set tmp_reg [get_registers -nowarn $tmp]
      if {[get_collection_size $tmp_pin] > 0} {
         if {$fit_flow == 1} {
            set_multicycle_path -through $tmp_pin -to $tmp -setup 7 -end
            set_multicycle_path -through $tmp_pin -to $tmp -hold  6 -end
         } else {
            set_false_path -through $tmp_pin -to $tmp_reg
         }
      }      

      # cal_counter synchronizer for global_reset_n_int
      set tmp "${inst}|arch|arch_inst|cal_counter_inst|non_hps.inst_sync_reset_n|din_s1"
      set tmp_pin [get_pins -nowarn [list "${tmp}|d" "${tmp}|*data"]]
      set tmp_reg [get_registers -nowarn $tmp]
      if {[get_collection_size $tmp_pin] > 0} {
         if {$fit_flow == 1} {
            set_multicycle_path -through $tmp_pin -to $tmp -setup 7 -end
            set_multicycle_path -through $tmp_pin -to $tmp -hold  6 -end
         } else {
            set_false_path -through $tmp_pin -to $tmp_reg
         }      
      }
      
      # cal_counter synchronizer for afi_cal_in_progress
      set tmp "${inst}|arch|arch_inst|cal_counter_inst|non_hps.inst_sync_cal_in_progress|din_s1"
      set tmp_pin [get_pins -nowarn [list "${tmp}|d" "${tmp}|*data"]]
      set tmp_reg [get_registers -nowarn $tmp]
      if {[get_collection_size $tmp_pin] > 0} {
         if {$fit_flow == 1} {
            set_multicycle_path -through $tmp_pin -to $tmp -setup 7 -end
            set_multicycle_path -through $tmp_pin -to $tmp -hold  6 -end
         } else {
            set_false_path -through $tmp_pin -to $tmp_reg
         }
      }      

      set tmp [get_pins -nowarn ${inst}|arch|arch_inst|io_tiles_wrap_inst|io_tiles_inst|tile_gen[*].tile_ctrl_inst|afi_core2ctl[6]]
      if {[get_collection_size $tmp] > 0} {
         set_multicycle_path -to ${inst}|arch|arch_inst|io_tiles_wrap_inst|io_tiles_inst|tile_gen[*].tile_ctrl_inst~hmc_reg0 -through $tmp -from [get_keepers *reset*] -setup 3 -end
         set_multicycle_path -to ${inst}|arch|arch_inst|io_tiles_wrap_inst|io_tiles_inst|tile_gen[*].tile_ctrl_inst~hmc_reg0 -through $tmp -from [get_keepers *reset*] -hold  2 -end
      }

      if {$var(PHY_USERMODE_OCT)} {
         set tmp [get_pins -nowarn ${inst}|arch|arch_inst|io_tiles_wrap_inst|io_tiles_inst|tile_gen[*].tile_ctrl_inst|afi_ctl2core[19]]
         if {[get_collection_size $tmp] > 0} {
            set_multicycle_path -from ${inst}|arch|arch_inst|io_tiles_wrap_inst|io_tiles_inst|tile_gen[*].tile_ctrl_inst~hmc_reg0 -through ${inst}|arch|arch_inst|io_tiles_wrap_inst|io_tiles_inst|tile_gen[*].tile_ctrl_inst|afi_ctl2core[19] -to *gen_oct_cal_req.gen_oct_cal_req_no_hps.oct_cal_req_regs* -setup 4 -start
            set_multicycle_path -from ${inst}|arch|arch_inst|io_tiles_wrap_inst|io_tiles_inst|tile_gen[*].tile_ctrl_inst~hmc_reg0 -through ${inst}|arch|arch_inst|io_tiles_wrap_inst|io_tiles_inst|tile_gen[*].tile_ctrl_inst|afi_ctl2core[19] -to *gen_oct_cal_req.gen_oct_cal_req_no_hps.oct_cal_req_regs* -hold  3 -start
         }

         set tmp [get_pins -nowarn ${inst}|arch|arch_inst|io_tiles_wrap_inst|io_tiles_inst|tile_gen[*].tile_ctrl_inst|afi_core2ctl[7]]
         if {[get_collection_size $tmp] > 0} {
            set_multicycle_path -from ${inst}|arch|arch_inst|seq_if_inst|gen_oct_cal_rdy.gen_oct_cal_rdy_no_hps.oct_cal_rdy_regs|regs.sr_out* -to ${inst}|arch|arch_inst|io_tiles_wrap_inst|io_tiles_inst|tile_gen[*].tile_ctrl_inst~hmc_reg0 -through ${inst}|arch|arch_inst|io_tiles_wrap_inst|io_tiles_inst|tile_gen[*].tile_ctrl_inst|afi_core2ctl[7] -setup 4 -start
            set_multicycle_path -from ${inst}|arch|arch_inst|seq_if_inst|gen_oct_cal_rdy.gen_oct_cal_rdy_no_hps.oct_cal_rdy_regs|regs.sr_out* -to ${inst}|arch|arch_inst|io_tiles_wrap_inst|io_tiles_inst|tile_gen[*].tile_ctrl_inst~hmc_reg0 -through ${inst}|arch|arch_inst|io_tiles_wrap_inst|io_tiles_inst|tile_gen[*].tile_ctrl_inst|afi_core2ctl[7] -hold  3 -start
         }
      }

      set ufi_wr [get_keepers -nowarn ${inst}|arch|arch_inst|fm_ufis|*ufi_write_reg]
      set ufi_rd [get_keepers -nowarn ${inst}|arch|arch_inst|fm_ufis|*ufi_read_reg]

      if {([get_collection_size $ufi_wr] > 0) && ([get_collection_size $ufi_rd] > 0)} {
         set_multicycle_path -from $ufi_wr -to $ufi_rd -setup 1 -end
         set_multicycle_path -from $ufi_wr -to $ufi_rd -hold  1 -end
      }
   }

   if {$var(AMM_C2P_UFI_MODE) != "pin_ufi_use_in_direct_out_direct"} {
      set ufi_reg [get_keepers -nowarn ${inst}|arch|arch_inst|fm_ufis|*amm_c2p_ufi_i|*ufi_read_reg]
      if {[get_collection_size $ufi_reg] > 0} {
         set_min_delay -from $ufi_reg -to ${inst}|arch|arch_inst|io_tiles_wrap_inst|io_tiles_inst|*phy_reg* -0.200
      }
   }
   if {$var(AMM_P2C_UFI_MODE) != "pin_ufi_use_in_direct_out_direct"} {
      set ufi_reg [get_keepers -nowarn ${inst}|arch|arch_inst|fm_ufis|*amm_p2c_ufi_i|*ufi_write_reg]
      if {[get_collection_size $ufi_reg] > 0} {
         set_min_delay -to $ufi_reg -from ${inst}|arch|arch_inst|io_tiles_wrap_inst|io_tiles_inst|*phy_reg* -0.200
      }
   }
   if {$var(MMR_C2P_UFI_MODE)!= "pin_ufi_use_in_direct_out_direct"} {
      set ufi_reg [get_keepers -nowarn ${inst}|arch|arch_inst|fm_ufis|*mmr_c2p_ufi_i|*ufi_read_reg]
      if {[get_collection_size $ufi_reg] > 0} {
         set_min_delay -from $ufi_reg -to ${inst}|arch|arch_inst|io_tiles_wrap_inst|io_tiles_inst|*phy_reg* -0.200
      }
   }
   if {$var(MMR_P2C_UFI_MODE)!= "pin_ufi_use_in_direct_out_direct"} {
      set ufi_reg [get_keepers -nowarn ${inst}|arch|arch_inst|fm_ufis|*mmr_p2c_ufi_i|*ufi_write_reg]
      if {[get_collection_size $ufi_reg] > 0} {
         set_min_delay -to $ufi_reg -from ${inst}|arch|arch_inst|io_tiles_wrap_inst|io_tiles_inst|*phy_reg* -0.200
      }
   }
   if {$var(SEQ_C2P_UFI_MODE) != "pin_ufi_use_in_direct_out_direct"} {
      set ufi_reg [get_keepers -nowarn ${inst}|arch|arch_inst|fm_ufis|*seq_c2p_ufi_i|*ufi_read_reg]
      if {[get_collection_size $ufi_reg] > 0} {
         set_min_delay -from $ufi_reg -to ${inst}|arch|arch_inst|io_tiles_wrap_inst|io_tiles_inst|*hmc_reg* -0.200
      }
   }
   if {$var(SEQ_P2C_UFI_MODE) != "pin_ufi_use_in_direct_out_direct"} {
      set ufi_reg [get_keepers -nowarn ${inst}|arch|arch_inst|fm_ufis|*seq_p2c_ufi_i|*ufi_write_reg]
      if {[get_collection_size $ufi_reg] > 0} {
         set_min_delay -to $ufi_reg -from ${inst}|arch|arch_inst|io_tiles_wrap_inst|io_tiles_inst|*hmc_reg* -0.200
      }
   }
   if {$var(ECC_C2P_UFI_MODE) != "pin_ufi_use_in_direct_out_direct"} {
      set ufi_reg [get_keepers -nowarn ${inst}|arch|arch_inst|fm_ufis|*ecc_c2p_ufi_i|*ufi_read_reg]
      if {[get_collection_size $ufi_reg] > 0} {
         set_min_delay -from $ufi_reg -to ${inst}|arch|arch_inst|io_tiles_wrap_inst|io_tiles_inst|*phy_reg* -0.200
      }
   }
   if {$var(ECC_P2C_UFI_MODE) != "pin_ufi_use_in_direct_out_direct"} {
      set ufi_reg [get_keepers -nowarn ${inst}|arch|arch_inst|fm_ufis|*ecc_p2c_ufi_i|*ufi_write_reg]
      if {[get_collection_size $ufi_reg] > 0} {
         set_min_delay -to $ufi_reg -from ${inst}|arch|arch_inst|io_tiles_wrap_inst|io_tiles_inst|*phy_reg* -0.200
      }
   }
   if {$var(LANE_C2P_UFI_MODE) != "pin_ufi_use_in_direct_out_direct"} {
      set ufi_reg [get_keepers -nowarn ${inst}|arch|arch_inst|fm_ufis|*lane_c2p_ufi_i|*ufi_read_reg]
      if {[get_collection_size $ufi_reg] > 0} {
         set_min_delay -from $ufi_reg -to ${inst}|arch|arch_inst|io_tiles_wrap_inst|io_tiles_inst|*phy_reg* -0.200
      }
   }
   if {$var(LANE_P2C_UFI_MODE) != "pin_ufi_use_in_direct_out_direct"} {
      set ufi_reg [get_keepers -nowarn ${inst}|arch|arch_inst|fm_ufis|*lane_p2c_ufi_i|*ufi_write_reg]
      if {[get_collection_size $ufi_reg] > 0} {
         set_min_delay -to $ufi_reg -from ${inst}|arch|arch_inst|io_tiles_wrap_inst|io_tiles_inst|*phy_reg* -0.200
      }
   }
   if {$var(SIDEBAND_C2P_UFI_MODE) != "pin_ufi_use_in_direct_out_direct"} {
      set ufi_reg [get_keepers -nowarn ${inst}|arch|arch_inst|fm_ufis|*sideband_c2p_ufi_i|*ufi_read_reg]
      if {[get_collection_size $ufi_reg] > 0} {
         set_min_delay -from $ufi_reg -to ${inst}|arch|arch_inst|io_tiles_wrap_inst|io_tiles_inst|*phy_reg* -0.200
      }
   }
   if {$var(SIDEBAND_P2C_UFI_MODE) != "pin_ufi_use_in_direct_out_direct"} {
      set ufi_reg [get_keepers -nowarn ${inst}|arch|arch_inst|fm_ufis|*sideband_p2c_ufi_i|*ufi_write_reg]
      if {[get_collection_size $ufi_reg] > 0} {
         set_min_delay -to $ufi_reg -from ${inst}|arch|arch_inst|io_tiles_wrap_inst|io_tiles_inst|*phy_reg* -0.200
      }
   }
   
   foreach periphery_clock $periphery_clocks {
      set_clock_uncertainty -10ps -add -enable_same_physical_edge -hold -from [get_clocks $periphery_clock] -to [get_clocks $periphery_clock]
   }

   if {!$var(IS_HPS)} {
      set dll_reset [get_pins -nowarn ${inst}|arch|arch_inst|io_tiles_wrap_inst|io_tiles_inst|tile_gen[*].lane_gen[*].lane_inst|lane_inst|core_dll[2]]
      if {[get_collection_size $dll_reset] > 0} {
         if {$fit_flow == 1} {
            set_multicycle_path -through ${inst}|arch|arch_inst|io_tiles_wrap_inst|io_tiles_inst|tile_gen[*].lane_gen[*].lane_inst|lane_inst|core_dll[2] -setup 8 -end
            set_multicycle_path -through ${inst}|arch|arch_inst|io_tiles_wrap_inst|io_tiles_inst|tile_gen[*].lane_gen[*].lane_inst|lane_inst|core_dll[2] -hold  7 -end
         } else {
            set_false_path -through ${inst}|arch|arch_inst|io_tiles_wrap_inst|io_tiles_inst|tile_gen[*].lane_gen[*].lane_inst|lane_inst|core_dll[2]
         }
      }
   }

   # ------------------------------ #
   # -                            - #
   # --- FALSE PATH CONSTRAINTS --- #
   # -                            - #
   # ------------------------------ #

   if {$var(C2C_TG_FALSE_PATH)} {
      set_false_path -from tg|tg|* -to tg|tg|*
   }   

   
   foreach ac_buf_path [concat $var(PATTERNS_AC_CLK) $var(PATTERNS_AC_SYNC) $var(PATTERNS_AC_ASYNC)] {
     set length [string length $ac_buf_path]
     set last_char [string range $ac_buf_path [expr $length -1] [expr $length -1]]
     
     if {[string equal $last_char "o"] == 1} {

        set word_idx [string first "cal_oct" $ac_buf_path]
        if {$word_idx == -1 } {
            set word_idx [string first "no_oct" $ac_buf_path]
            set suffix "no_oct.obuf"
        } else {
            set suffix "cal_oct.obuf"
        }
        set sub_path [string range $ac_buf_path 0 [expr {$word_idx - 1}]]

        set buf_path ${inst}|${sub_path}${suffix}
        set oe_path  "${buf_path}|oe"

        set_false_path -through $oe_path
        set_disable_timing -from oe -to o $buf_path
      }
   }


   foreach ac_n_buf_path $var(PATTERNS_AC_CLK_N) {
     set length [string length $ac_n_buf_path]
     set last_char [string range $ac_n_buf_path [expr $length -1] [expr $length -1]]
     
     if {[string equal $last_char "o"] == 1} {

        set word_idx [string first "cal_oct" $ac_n_buf_path]
        if {$word_idx == -1 } {
            set word_idx [string first "no_oct" $ac_n_buf_path]
            set suffix "no_oct.obuf_bar"
        } else {
            set suffix "cal_oct.obuf_bar"
        }
        set sub_path [string range $ac_n_buf_path 0 [expr {$word_idx - 1}]]

        set buf_path ${inst}|${sub_path}${suffix}
        set oe_path  "${buf_path}|oe"

        set_false_path -through $oe_path
        set_disable_timing -from oe -to o $buf_path
      }
   }


   foreach dqdqs_buf_path [concat $var(PATTERNS_WCLK) $var(PATTERNS_WDATA) $var(PATTERNS_DBI) $var(PATTERNS_DM)] {
     set length [string length $dqdqs_buf_path]
     set last_char [string range $dqdqs_buf_path [expr $length -1] [expr $length -1]]
     
     if {[string equal $last_char "o"] == 1} {
        set word_idx [string first "cal_oct" $dqdqs_buf_path]
        set suffix "cal_oct.obuf"
        
        set sub_path [string range $dqdqs_buf_path 0 [expr {$word_idx - 1}]]
        set buf_path ${inst}|${sub_path}${suffix}
        set oe_path  "${buf_path}|oe"
        set_false_path -through $oe_path
        set_disable_timing -from oe -to o $buf_path
      }
   } 

   foreach dqdqs_buf_path $var(PATTERNS_WCLK_N) {
     set length [string length $dqdqs_buf_path]
     set last_char [string range $dqdqs_buf_path [expr $length -1] [expr $length -1]]
     
     if {[string equal $last_char "o"] == 1} {
        set word_idx [string first "cal_oct" $dqdqs_buf_path]
        set suffix "cal_oct.obuf_bar"
        
        set sub_path [string range $dqdqs_buf_path 0 [expr {$word_idx - 1}]]
        set buf_path ${inst}|${sub_path}${suffix}
        set oe_path  "${buf_path}|oe"
        set_false_path -through $oe_path
        set_disable_timing -from oe -to o $buf_path
      }
   }

   # DQ/DQS pins are calibrated
   set_false_path -to $pins(wdata)
   set_false_path -from $pins(rdata)
   set_output_delay -clock $pins(ref_clock_name) 0 $pins(wdata)
   set_input_delay -clock $pins(ref_clock_name) 0 $pins(rdata)
   if {[llength $pins(dm)] > 0} {
      set_false_path -to $pins(dm)
      set_output_delay -clock $pins(ref_clock_name) 0 $pins(dm)
   }
   if {[llength $pins(dbi)] > 0} {
      set_false_path -to $pins(dbi)
      set_false_path -from $pins(dbi)
      set_output_delay -clock $pins(ref_clock_name) 0 $pins(dbi)
      set_input_delay -clock $pins(ref_clock_name) 0 $pins(dbi)
   }
   set_false_path -to $pins(wclk)
   set_output_delay -clock $pins(ref_clock_name) 0 $pins(wclk)
   if {[llength $pins(wclk_n)] > 0} {
      set_false_path -to $pins(wclk_n)
      set_output_delay -clock $pins(ref_clock_name) 0 $pins(wclk_n)
   }
   set_false_path -from $pins(rclk)
   if {[llength $pins(rclk_n)] > 0} {
      set_false_path -from $pins(rclk_n)
   }
   if {[llength $pins(ac_clk)] > 0} {
      set_false_path -to $pins(ac_clk)
      set_output_delay -clock $pins(ref_clock_name) 0 $pins(ac_clk) -add
   }
   if {[llength $pins(ac_clk_n)] > 0} {
      set_false_path -to $pins(ac_clk_n)
      set_output_delay -clock $pins(ref_clock_name) 0 $pins(ac_clk_n) -add
   }

   if {[llength $pins(ac_async)] > 0} {
      set_false_path -to $pins(ac_async)
      set_false_path -from $pins(ac_async)
      foreach ac_async $pins(ac_async) {
         if {[get_port_info -is_input $ac_async] || [get_port_info -is_inout $ac_async]} {
            set_input_delay -clock $pins(ref_clock_name) 0 $ac_async
         }
         if {[get_port_info -is_output $ac_async] || [get_port_info -is_inout $ac_async]} {
            set_output_delay -clock $pins(ref_clock_name) 0 $ac_async
         }
      }
   }
   
   if {!$var(IS_HPS)} {
      set tmp_pins_0 [get_pins -nowarn ${inst}|arch|arch_inst|io_tiles_wrap_inst|io_tiles_inst|tile_gen[*].lane_gen[*].lane_inst|lane_inst|core2dbc_rd_data_rdy]
      set tmp_pins_1 [get_pins -nowarn ${inst}|arch|arch_inst|io_tiles_wrap_inst|io_tiles_inst|tile_gen[*].lane_gen[*].lane_inst|lane_inst|dbc2core_rd_data_vld0]
      if {[get_collection_size $tmp_pins_0] > 0 && [get_collection_size $tmp_pins_1] > 0} {
         set_false_path -through $tmp_pins_0 -through $tmp_pins_1
      }
   }

   # ------------------------- #
   # -                       - #
   # --- CLOCK UNCERTAINTY --- #
   # -                       - #
   # ------------------------- #

   if {!$var(IS_HPS) && ($fit_flow == 1 || $sta_flow == 1)} {

      #################################
      # C2P/P2C transfers
      #################################

      # Get P2C / C2P Multi-tile clock uncertainty
      set p2c_c2p_multi_tile_clock_uncertainty [ed_synth_emif_fm_0_altera_emif_arch_fm_191_faapzxy_get_p2c_c2p_clock_uncertainty $inst var]

      # Get extra periphery clock uncertainty
      set periphery_clock_uncertainty [list]
      ed_synth_emif_fm_0_altera_emif_arch_fm_191_faapzxy_get_periphery_clock_uncertainty periphery_clock_uncertainty var

      # Get Fitter overconstraints
      if {$fit_flow == 1} {
         ed_synth_emif_fm_0_altera_emif_arch_fm_191_faapzxy_get_periphery_overconstraints periphery_overconstraints_st periphery_overconstraints_mt var
      } else {
         set periphery_overconstraints_st [list 0.0 0.0 0.0 0.0]
         set periphery_overconstraints_mt [list 0.0 0.0 0.0 0.0]
      }

      # Now loop over core/periphery clocks and set clock uncertainty
      set i_core_clock 0
      foreach core_clock $core_clocks {
         if {$core_clock != ""} {

            set local_core_clock [lindex $core_clocks_local $i_core_clock]
            
            if {$core_clock == $pins(master_core_usr_clock_sec) || $core_clock == $pins(master_core_usr_half_clock_sec)} {
               set same_tile_index $i_cpa_clock_tile_sec
            } else {
               set same_tile_index $i_cpa_clock_tile_pri
            }

            set i_phy_clock 0
            foreach { phy_clock } $pins(pll_phy_clock_l) {
               
               if {$i_phy_clock != $same_tile_index} {
                  # C2P/P2C where the periphery tile != CPA tile.
                  # For these transfers the SDC explicitly overrides the clock uncertainty values.
                  # Therefore, when overconstraining we must not use the "-add" option.
                  set add_to_derived ""
                  set c2p_su         [expr {$p2c_c2p_multi_tile_clock_uncertainty + [lindex $periphery_overconstraints_mt 0] + [lindex $periphery_clock_uncertainty 0]}]
                  set c2p_h          [expr {$p2c_c2p_multi_tile_clock_uncertainty + [lindex $periphery_overconstraints_mt 1] + [lindex $periphery_clock_uncertainty 1]}]
                  set p2c_su         [expr {$p2c_c2p_multi_tile_clock_uncertainty + [lindex $periphery_overconstraints_mt 2] + [lindex $periphery_clock_uncertainty 2]}]
                  set p2c_h          [expr {$p2c_c2p_multi_tile_clock_uncertainty + [lindex $periphery_overconstraints_mt 3] + [lindex $periphery_clock_uncertainty 3]}]
               } else {
                  # C2P/P2C where the periphery tile == CPA tile
                  # For these transfers it is safe to use the -add option since we rely on 
                  # derive_clock_uncertainty for the base value.
                  set add_to_derived "-add"
                  set c2p_su         [expr [lindex $periphery_overconstraints_st 0] + [lindex $periphery_clock_uncertainty 0]]
                  set c2p_h          [expr [lindex $periphery_overconstraints_st 1] + [lindex $periphery_clock_uncertainty 1]]
                  set p2c_su         [expr [lindex $periphery_overconstraints_st 2] + [lindex $periphery_clock_uncertainty 2]]
                  set p2c_h          [expr [lindex $periphery_overconstraints_st 3] + [lindex $periphery_clock_uncertainty 3]]
               }

               set catch_exception [catch {set local_phy_clk_l_${i_phy_clock}} result]
               if {$catch_exception == 0} {
                  set_clock_uncertainty -from [get_clocks $local_core_clock] -to   [get_clocks [set local_phy_clk_l_${i_phy_clock}]] -suppress_warnings -setup {*}$add_to_derived $c2p_su
                  set_clock_uncertainty -from [get_clocks $local_core_clock] -to   [get_clocks [set local_phy_clk_l_${i_phy_clock}]] -suppress_warnings -hold  {*}$add_to_derived $c2p_h
                  set_clock_uncertainty -to   [get_clocks $local_core_clock] -from [get_clocks [set local_phy_clk_l_${i_phy_clock}]] -suppress_warnings -setup {*}$add_to_derived $p2c_su
                  set_clock_uncertainty -to   [get_clocks $local_core_clock] -from [get_clocks [set local_phy_clk_l_${i_phy_clock}]] -suppress_warnings -hold  {*}$add_to_derived $p2c_h
                  
                  if {$sta_flow == 1 && $var(CUT_C2P_P2C_PATHS)} {
                     set_false_path -to [get_clocks [set local_phy_clk_l_${i_phy_clock}]] 
                     set_false_path -from [get_clocks [set local_phy_clk_l_${i_phy_clock}]] 
                  }
               }

               set catch_exception [catch {set local_phy_clk_${i_phy_clock}} result]
               if {$catch_exception == 0} {
                  set_clock_uncertainty -from [get_clocks $local_core_clock] -to   [get_clocks [set local_phy_clk_${i_phy_clock}]] -suppress_warnings -setup {*}$add_to_derived $c2p_su
                  set_clock_uncertainty -from [get_clocks $local_core_clock] -to   [get_clocks [set local_phy_clk_${i_phy_clock}]] -suppress_warnings -hold  {*}$add_to_derived $c2p_h
                  set_clock_uncertainty -to   [get_clocks $local_core_clock] -from [get_clocks [set local_phy_clk_${i_phy_clock}]] -suppress_warnings -setup {*}$add_to_derived $p2c_su
                  set_clock_uncertainty -to   [get_clocks $local_core_clock] -from [get_clocks [set local_phy_clk_${i_phy_clock}]] -suppress_warnings -hold  {*}$add_to_derived $p2c_h
                  
                  if {$sta_flow == 1 && $var(CUT_C2P_P2C_PATHS) } {
                     set_false_path -to [get_clocks [set local_phy_clk_${i_phy_clock}]] 
                     set_false_path -from [get_clocks [set local_phy_clk_${i_phy_clock}]] 
                  }
               
               }

               incr i_phy_clock
            }
         }
         incr i_core_clock
      }

      #################################
      # Within-core transfers
      #################################

      # Get extra core clock uncertainty
      set core_clock_uncertainty [list]
      ed_synth_emif_fm_0_altera_emif_arch_fm_191_faapzxy_get_core_clock_uncertainty core_clock_uncertainty var

      # Get Fitter overconstraints
      if {$fit_flow == 1} {
         ed_synth_emif_fm_0_altera_emif_arch_fm_191_faapzxy_get_core_overconstraints core_overconstraints var
      } else {
         set core_overconstraints [list 0.0 0.0 0.0 0.0]
      }

      set c2c_same_su         [expr [lindex $core_overconstraints 0] + [lindex $core_clock_uncertainty 0]]
      set c2c_same_h          [expr [lindex $core_overconstraints 1] + [lindex $core_clock_uncertainty 1]]
      set c2c_diff_su         [expr [lindex $core_overconstraints 2] + [lindex $core_clock_uncertainty 2]]
      set c2c_diff_h          [expr [lindex $core_overconstraints 3] + [lindex $core_clock_uncertainty 3]]

      # For these transfers it is safe to use the -add option of set_clock_uncertainty since
      # we rely on derive_clock_uncertainty for the base value.
      foreach src_core_clock_local $core_clocks_local {
         if {$src_core_clock_local != ""} {
            foreach dst_core_clock_local $core_clocks_local {
               if {$dst_core_clock_local != ""} {
                  if {$src_core_clock_local == $dst_core_clock_local} {
                     # Same clock network transfers
                     set_clock_uncertainty -from $src_core_clock_local -to $dst_core_clock_local -setup -add $c2c_same_su
                     set_clock_uncertainty -from $src_core_clock_local -to $dst_core_clock_local -hold -enable_same_physical_edge -add $c2c_same_h
                  } else {
                     # Transfers between different core clock networks
                     set_clock_uncertainty -from $src_core_clock_local -to $dst_core_clock_local -setup -add $c2c_diff_su
                     set_clock_uncertainty -from $src_core_clock_local -to $dst_core_clock_local -hold -add $c2c_diff_h
                  }
               }
            }
         }
      }

   }

   # --------------------- #
   # -                   - #
   # --- ACTIVE CLOCKS --- #
   # -                   - #
   # --------------------- #

   if {(($::quartus(nameofexecutable) ne "quartus_fit") && ($::quartus(nameofexecutable) ne "quartus_map"))} {

      if {$var(C2P_P2C_PR) && [llength $periphery_clocks] > 0 && !$debug} {
         post_sdc_message info "Setting periphery clocks as inactive; use Report DDR to timing analyze periphery clocks"
         set_active_clocks [remove_from_collection [get_active_clocks] [get_clocks $periphery_clocks]]
      }
   }
}

# -------------------------- #
# -                        - #
# --- REPORT DDR COMMAND --- #
# -                        - #
# -------------------------- #

add_ddr_report_command "source [list [file join [file dirname [info script]] ${::GLOBAL_ed_synth_emif_fm_0_altera_emif_arch_fm_191_faapzxy_corename}_report_timing.tcl]]"

