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
# This file contains the timing constraints for the Altera PLL.
#    * The helper routines are defined in io_pll_altera_iopll_1931_oypl3jq_pin_map.tcl
#
# NOTE
# ----
# Debug switch. Change to 1 to get more run-time debug information
set debug 0

set script_dir [file dirname [info script]]

source "$script_dir/io_pll_altera_iopll_1931_oypl3jq_parameters.tcl"
source "$script_dir/io_pll_altera_iopll_1931_oypl3jq_pin_map.tcl"

####################
#                  #
# GENERAL SETTINGS #
#                  #
####################

# This is a global setting and will apply to the whole design.
# This setting is required for the memory interface to be
# properly constrained.
derive_clock_uncertainty


# All timing requirements will be represented in nanoseconds with up to 3 decimal places of precision
set_time_format -unit ns -decimal_places 3

# Determine if entity names are on
set entity_names_on [ ai_are_entity_names_on ]

if {[catch {load_package atoms
            load_package sdc_ext
            load_package design
            catch {read_atom_netlist} read_atom_netlist_out
            set read_atom_netlist_error [regexp "ERROR" $read_atom_netlist_out]
            } err_loading_packages]} {
    post_message -type error "Failed to load packages required by IOPLL SDC: $err_loading_packages"
}

# This is the main call to the netlist traversal routines
# that will automatically find all pins and registers required
# to apply timing constraints.
# During the fitter, the routines will be called only once
# and cached data will be used in all subsequent calls.



if {[info exists ::GLOBAL_top_io_pll_altera_iopll_1931_oypl3jq_corename_ai_pll_db]} {
    # Clean-up stale content
    unset ::GLOBAL_top_io_pll_altera_iopll_1931_oypl3jq_corename_ai_pll_db
}
if {[catch {ai_initialize_pll_db ::GLOBAL_top_io_pll_altera_iopll_1931_oypl3jq_corename_ai_pll_db} err_initializing_db]} {
    post_message -type warning "Failed to find atom information in IOPLL SDC: $err_initializing_db"
}

# If multiple instances of this core are present in the
# design they will all be constrained through the
# following loop
set instances [ array names ::GLOBAL_top_io_pll_altera_iopll_1931_oypl3jq_corename_ai_pll_db ]
foreach { inst } $instances {
	if { [ info exists pins ] } {
		# Clean-up stale content
		unset pins
	}
	
	# -------------------------------- #
	# -                              - #
	# --- Determine PLL Parameters --- #
	# -                              - #
	# -------------------------------- #
	
	set pll_atoms [get_atom_nodes -matching ${inst}* -type IOPLL]
	set num_pll_inst [get_collection_size $pll_atoms]
	
	if {$num_pll_inst > 1} { 
		# Error condition
		post_message -type error "SDC: More than one PLL atom found with instance name $inst"
	} else {
		# Use IP generated parameters
		if { $debug } {
			post_message -type info "SDC: using IP generated parameter values"
		}
	}

    # These dictionaries hold all the clock information.
    lassign $::GLOBAL_top_io_pll_altera_iopll_1931_oypl3jq_corename_ai_pll_db($inst) base_clock_data_dict gen_clock_data_dict
	
	# ------------------------ #
	# -                      - #
	# ---REFERENCE CLOCK(s)--- #
	# -                      - #
	# ------------------------ #
    dict for {clock_key info} $base_clock_data_dict {
        dict with info {
            if {$is_fpga_pin && !$exists} {
               create_clock -period $period \
                   -waveform [ list 0 $half_period] \
                   -name $name $port_node_name
            }
        }
    }
	# ------------------------- #
	# -                       - #
	# --- OUTPUT PLL CLOCKS --- #
	# -                       - #
	# ------------------------- #
    dict for {clock_key info} $gen_clock_data_dict {
        dict with info {
            if {[is_post_syn_sta]} {
                if {$is_valid && !$exists} {
                    create_non_virtual_generated_clock_with_master_or_source \
                        $master \
                        $src \
                        $name \
                        $multiply_by \
                        $divide_by \
                        $phase \
                        $duty_cycle \
                        $pin_node_name

                    if {[string match lvds* $clock_key] && [string match *loaden* $pattern] && [dict exists $gen_clock_data_dict $clock_key "through_pin" ] } {
                        set_max_delay_in_fit_or_false_path_in_sta_through_no_warn $through_pin $max_delay
                    }
                } elseif {[is_m_n_cntr $pattern]} {
                    create_virtual_generated_clock_with_master_or_source \
                        $master \
                        $src \
                        $name \
                        $multiply_by \
                        $divide_by \
                        $phase \
                        $duty_cycle
                }
            } else {
                if {$is_valid && !$exists} {
                    create_generated_clock -add \
                        -source $src \
                        -name $name \
                        -multiply_by $multiply_by \
                        -divide_by $divide_by \
                        -phase $phase \
                        -duty_cycle $duty_cycle \
                        $pin_node_name

                    if {[string match lvds* $clock_key] && [string match *loaden* $pattern] && [dict exists $gen_clock_data_dict $clock_key "through_pin" ] } {
                        set_max_delay_in_fit_or_false_path_in_sta_through_no_warn $through_pin $max_delay
                    }
                }
            }
        }
    }

    foreach_in_collection node [get_nodes -no_duplicates -nowarn "${inst}|tennm_pll|dprio_rst_n"] {
        set_false_path -through [get_node_info -name $node]
    }
}
