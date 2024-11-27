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
# This file contains the traversal routines that are used by
# io_pll_altera_iopll_1931_oypl3jq.sdc scripts. 
#
# These routines are only meant to support the SDC. 
# Trying to using them in a different context can have unexpected 
# results.

set ::GLOBAL_top_io_pll_altera_iopll_1931_oypl3jq_corename_debug 0

set script_dir [file dirname [info script]]

source [file join $script_dir io_pll_altera_iopll_1931_oypl3jq_parameters.tcl]

proc get_warnings_disabled {} {
    set local_disable_warnings true
    set inis [split [get_global_assignment -name INI_VARS] ";"]
    foreach ini $inis {
        set ini_lst [split $ini "="]
        lassign $ini_lst ini_name ini_value
        if {$ini_name == "disable_warnings" && $ini_value == "off"} {
            set local_disable_warnings false
            break
        }
    }
    return $local_disable_warnings 
}
set ::GLOBAL_top_io_pll_altera_iopll_1931_oypl3jq_corename_disable_warnings [get_warnings_disabled]

# ----------------------------------------------------------------
#
proc ai_post_message {msg_type msg {msg_context sta_only}} {
#
# Description: Posts a message to Quartus, depending on 
# msg_context (sta_only, all)
#              
#              
#
# ----------------------------------------------------------------

    if {$msg_type == "debug"} {
        if {$::GLOBAL_top_io_pll_altera_iopll_1931_oypl3jq_corename_debug} {
            puts $msg
        }
    } else {
        if {$msg_context == "all"} {
            post_message -type $msg_type $msg
        } elseif {$msg_context == "sta_only"} {
            if {$::TimeQuestInfo(nameofexecutable) == "quartus_sta"} {
                post_message -type $msg_type $msg
            }
        }
    }
}

# ----------------------------------------------------------------
#
proc ai_are_entity_names_on { } {
#
# Description: Determines if the entity names option is on
#
# ----------------------------------------------------------------
	return [set_project_mode -is_show_entity]	
}

# ----------------------------------------------------------------
#
proc ai_initialize_pll_db { pll_db_par } {
#
# Description: Gets the instances of this particular PLL IP and creates the pin
#              cache
#
# ----------------------------------------------------------------
	upvar $pll_db_par local_pll_db

	global ::GLOBAL_top_io_pll_altera_iopll_1931_oypl3jq_corename

	ai_post_message info "Initializing PLL database for CORE $::GLOBAL_top_io_pll_altera_iopll_1931_oypl3jq_corename"
	set instance_list [ai_get_core_instance_list $::GLOBAL_top_io_pll_altera_iopll_1931_oypl3jq_corename]

	foreach instname $instance_list {
		ai_post_message info "Finding port-to-pin mapping for CORE: $::GLOBAL_top_io_pll_altera_iopll_1931_oypl3jq_corename INSTANCE: $instname"

		set clock_data_dicts [ai_get_pll_pins $instname]
		lassign $clock_data_dicts base_clock_data_dict gen_clock_data_dict
        print_clock_data $base_clock_data_dict
        print_clock_data $gen_clock_data_dict 

		set local_pll_db($instname) $clock_data_dicts 
	}
}

# ----------------------------------------------------------------
#
proc ai_get_core_instance_list {corename} {
#
# Description: Converts node names from one style to another style
#
# ----------------------------------------------------------------
	set full_instance_list [ai_get_core_full_instance_list $corename]
	set instance_list [list]

	foreach inst $full_instance_list {
		if {[lsearch $instance_list [escape_brackets $inst]] == -1} {
            ai_post_message debug "Found instance:  $inst"
			lappend instance_list $inst
		}
	}
	return $instance_list
}

# ----------------------------------------------------------------
#
proc ai_get_core_full_instance_list {corename} {
#
# Description: Finds the instances of the particular IP by searching through the cells
#
# ----------------------------------------------------------------

	set instance_list [design::get_instances -entity $corename]
                               
	if {[ llength $instance_list ] == 0} {

        if {!$::GLOBAL_top_io_pll_altera_iopll_1931_oypl3jq_corename_disable_warnings} {
            ai_post_message warning "The auto-constraining script was not able to detect any instance for core < $corename >" all
            ai_post_message warning "Verify the following:"
            ai_post_message warning " The core < $corename > is instantiated within another component (wrapper)" all
            ai_post_message warning " The core is not the top-level of the project" all
        }
	}

	return $instance_list
}
proc ai_get_registers {pattern} {
    if {$::GLOBAL_top_io_pll_altera_iopll_1931_oypl3jq_corename_disable_warnings} {
        return [get_registers -nowarn -no_duplicates $pattern]
    } else {
        return [get_registers -no_duplicates $pattern]
    }
}
proc ai_get_pins {pattern} {
    if {$::GLOBAL_top_io_pll_altera_iopll_1931_oypl3jq_corename_disable_warnings} {
        return [get_pins -nowarn -no_duplicates $pattern]
    } else {
        return [get_pins -no_duplicates $pattern]
    }
}
proc ai_get_pin_node_name {pattern} {
    set pin_collection [ai_get_pins $pattern]
    set num_pins [get_collection_size $pin_collection]
    if {$num_pins == 1} {
        foreach_in_collection id $pin_collection {
            set node_name [get_node_info -name $id]	     
            return $node_name
        }
    } 
    return ""
 
}

# ----------------------------------------------------------------
#
proc ai_get_collection_size_from_pattern {pattern} {
#
# Description: Takes a string regex and gets the pin collection.
#
# ----------------------------------------------------------------
    set pin_collection [get_pins -no_duplicates $pattern]
    return [get_collection_size $pin_collection]
}

# ----------------------------------------------------------------
#
proc print_clock_data {d} {
#
# Description: Prints clock data dict
#
# ---------------------------------------------------------------- 
    dict for {clock_key info} $d {
        ai_post_message debug "Clock:  $clock_key"
        dict for {key val} $info {
            ai_post_message debug "   $key: $val"
        }
    }
}

# ----------------------------------------------------------------
#
proc ai_subst_instname {clock_data_dict patt} {
#
# Description: Takes a string regex and gets the pin collection.
#
# ----------------------------------------------------------------
    dict for {clock_key info} $clock_data_dict {
        dict with info {
            regsub -all "__inst_name__" $name $patt new_name
            regsub -all "__inst_name__" $pattern $patt new_pattern
            
            dict set clock_data_dict $clock_key name $new_name
            dict set clock_data_dict $clock_key pattern $new_pattern
            
            if {[dict exists $clock_data_dict $clock_key "through_pin" ]} {
                regsub -all "__inst_name__" $through_pin $patt new_through_pin
                dict set clock_data_dict $clock_key through_pin $new_through_pin
            }
        }
    }
    return $clock_data_dict
}
# ----------------------------------------------------------------
#
proc ai_update_genclk_div_mult {clock_data_dict pll_parameters_dict} {
#
# Description: Updates the dict with div/mult values collected from
# the PLL's atom parameters.
#
# ----------------------------------------------------------------
    set compensated_counter_div 0
    set clock_to_compensate [dict get $pll_parameters_dict clock_to_compensate]
    # Loop over dict to find the compensated counter's div value first.
    dict for {clock_key info} $clock_data_dict {
        dict with info {
            if {[info exists counter_index]} { 
                if {$counter_index == $clock_to_compensate} {
                    set compensated_counter_div [dict get $pll_parameters_dict c${counter_index}_total]
                }
            }
        }
        unset -nocomplain counter_index
    }
    dict for {clock_key info} $clock_data_dict {
        dict with info {
            ai_post_message debug "Getting div/mult factors for clock $clock_key" 

            set ccnt -1
            if {[info exists counter_index]} {
                set ccnt [dict get $pll_parameters_dict c${counter_index}_total]
			    set ccnt_dc [dict get $pll_parameters_dict duty_cycle${counter_index}]
            } else {
                set counter_index -1
			    set ccnt_dc 50
            }
            set mult_div [ai_get_mult_div_factors \
                $clock_key \
                $src \
                [dict get $pll_parameters_dict n_total] \
                [dict get $pll_parameters_dict m_total] \
                $ccnt \
                $counter_index \
                $compensated_counter_div \
                [dict get $pll_parameters_dict compensation_mode] \
                [dict get $pll_parameters_dict clock_to_compensate]]

            lassign $mult_div mult div

            ai_post_message debug "Setting mult_div factors for: $clock_key to $mult/$div"

            dict set clock_data_dict $clock_key multiply_by $mult
            dict set clock_data_dict $clock_key divide_by $div
            dict set clock_data_dict $clock_key duty_cycle $ccnt_dc
        }
        unset -nocomplain counter_index
    }
    return $clock_data_dict
}
# ----------------------------------------------------------------
#
proc ai_set_genclk_pin_info {clock_data_dict} {
#
# Description: Updates the dict with pin info collected from making
# STA API calls.
#
# ----------------------------------------------------------------
    dict for {clock_key info} $clock_data_dict {
        dict with info {
            ai_post_message debug "Setting pin info for clock $clock_key"
            if {$node_type == "register"} {
                set pin_collection [ai_get_registers $pattern]
            } elseif {$node_type == "pin"} {
                set pin_collection [ai_get_pins $pattern]
            } else {
                ai_post_message "debug" "Incorrect type of node."
            }
            set num_pins [get_collection_size $pin_collection]
            if {$num_pins == 1} {
                # Always set valid to true if we found the pin node
                ai_post_message debug "Setting clock as valid."
                dict set clock_data_dict $clock_key is_valid true
                
                # This for loop should only loop once.
                foreach_in_collection id $pin_collection {
                    set node_name [get_node_info -name $id]	     
                    dict set clock_data_dict $clock_key pin_id $id
                    dict set clock_data_dict $clock_key pin_node_name $node_name
                }
                # Check if clock_exists, if it does, then
                # set key "exists" on the clock info dict.
                dict set clock_data_dict $clock_key exists [ai_clock_exists $node_name]

            
            } else {
                dict set clock_data_dict $clock_key is_valid false
            }

        }
    }
    return $clock_data_dict
    
    
} 
# ----------------------------------------------------------------
#
proc ai_set_baseclk_pin_info {clock_data_dict refclk_data_dict pll_name} {
#
    # Description: Updates the dict with pin info collected from refclk data
    # dict, which was obtained by traversing netlist.
#
# ----------------------------------------------------------------
    ai_post_message debug "In ai_set_baseclk_pin_info"

    dict for {clock_key info} $clock_data_dict {
        dict with info {
            ai_post_message debug "Setting pin info for clock $clock_key"
            
            set node_name ""
            dict for {clock_id info} $refclk_data_dict {
                dict with info {
                    # Figure out which refclk is the baseclk based on input muxes 
                    set pll_atom [ai_get_pll_atom $pll_name]
                    set clkin_enum "ENUM_IOPLL_CLKIN_0_SRC"
                    if {!$is_main_refclk} {
                        set clkin_enum "ENUM_IOPLL_CLKIN_1_SRC"
                    }
                    set refclk_src [get_atom_node_info -key $clkin_enum -node $pll_atom]

                    set refclk_port_name "$pattern"
                    if {[regexp {[0-9]+} $refclk_src refclk_index]} {
                        set refclk_port_name "$pattern\[$refclk_index\]"
                    } 
                    if {[string equal -nocase $refclk_port_name $ref_pin_node_name]} {
                        dict set clock_data_dict $clock_key pin_id $ref_pin_id
                        dict set clock_data_dict $clock_key pin_node_name $ref_pin_node_name
                        dict set clock_data_dict $clock_key port_id $ref_port_id
                        dict set clock_data_dict $clock_key port_node_name $ref_port_node_name
                        dict set clock_data_dict $clock_key is_fpga_pin $ref_is_fpga_pin
                        set node_name $ref_port_node_name
                        break
                    }
                }
            }
            # Check if clock_exists, if it does, then
            # set key "exists" on the clock info dict.
            dict set clock_data_dict $clock_key exists [ai_clock_exists $node_name]

        }
    }
    return $clock_data_dict
    
}
proc ai_get_n_cnt_clock_node_name {gen_clock_data_dict} {
    dict for {clock_key info} $gen_clock_data_dict {
        dict with info {
            ai_post_message debug "Clock:  $clock_key, pin_node_name: $pin_node_name"

            if {$clock_key == "n_cnt_clock"} {
                return $pin_node_name
            }
        }
    }
    return ""
}

# ----------------------------------------------------------------
#
proc ai_update_baseclk_data {base_clock_data_dict pll_parameters_dict} {
#
    # Description: Updates the refclk information based on atom settings
#
# ----------------------------------------------------------------
    ai_post_message debug "In ai_update_baseclk_data_dict"

    dict for {base_clock_key info} $base_clock_data_dict {
        dict with info {
            if {$is_main_refclk} {
                set ref_period [dict get $pll_parameters_dict refclk_period]
                set ref_period [expr round($ref_period * 1000.0)/1000.0] 
                set ref_period [format %.3f $ref_period]
                dict set base_clock_data_dict $base_clock_key period $ref_period

                set half_period [expr $ref_period /2]
                set half_period [expr round($half_period * 1000.0)/1000.0] 
                set half_period [format %.3f $half_period]
                dict set base_clock_data_dict $base_clock_key half_period $half_period
            }
        }
    }

    return $base_clock_data_dict
}

# ----------------------------------------------------------------
#
proc ai_update_genclk_sources {base_clock_data_dict gen_clock_data_dict pll_parameters_dict} {
#
# Description: Updates the genclk data dict with src nodes from the appropriate
#              refclks
#
# ----------------------------------------------------------------
    ai_post_message debug "In ai_update_genclk_sources"

    # Check if vcoph pin exists, if it does then set the clock source
    # as vcoph otherwise set it to either refclk or n_cnt_clock
    set vcoph_exists false
    if {[dict exists $gen_clock_data_dict vcoph]} {
        set vcoph_pin_name [ai_get_pin_node_name [dict get $gen_clock_data_dict vcoph pattern]]
        if {$vcoph_pin_name != ""} {
            ai_post_message debug "vcoph pin name: $vcoph_pin_name "
            set vcoph_exists true
        }
    }

    dict for {clock_key info} $gen_clock_data_dict {
        dict with info {
            ai_post_message debug "Setting src pin info for clock $clock_key"

            set node_name ""
            set main_refclk_key ""
            dict for {base_clock_key base_clock_data_dict_info} $base_clock_data_dict {
                dict with base_clock_data_dict_info {
                    if {$is_main_refclk} {
                        set main_refclk_key $base_clock_key
                        if {$is_fpga_pin} {
                            set node_name $port_node_name
                        } else {
                            set node_name $pin_node_name
                        }
                        break
                    }
                }
            }
            if {$clock_key != "n_cnt_clock" && ![dict get $pll_parameters_dict n_bypass]} {
                set src "n_cnt_clock"
            }

            if {$src == "refclk" || $src == "cascade_in" || $src == "pll_cascade_in" || $src == "core_refclk"} {
                set src_ $node_name
            } elseif {$src == "n_cnt_clock"} {
                if {[is_post_syn_sta]} {
                    set gen_clock_data_dict_for_post_syn $gen_clock_data_dict
                    dict for {clk_key gen_clock_data_dict_for_post_syn_info} $gen_clock_data_dict_for_post_syn {
                        if {$clk_key == "n_cnt_clock"} {
                            dict set gen_clock_data_dict $clock_key master [dict get $gen_clock_data_dict_for_post_syn_info name]
                        }
                    }
                } else {
                    set src_ [ai_get_n_cnt_clock_node_name $gen_clock_data_dict]
                }
            } else {
                set src_ ""
                ai_post_message "warning" "Undefined clock source: $src"
                dict set gen_clock_data_dict $clock_key is_valid false
            }

            if {$clock_key != "n_cnt_clock" && $clock_key != "vcoph" && $vcoph_exists} {
                set src_ $vcoph_pin_name
            }
            dict set gen_clock_data_dict $clock_key src $src_
        }
    }
    return $gen_clock_data_dict
}
proc ai_invalidate_clocks {clock_data_dict} {
    # Set the is_valid flag on each clock to false
    dict for {clock_key info} $clock_data_dict {
        dict with info {
            dict set clock_data_dict $clock_key is_valid false
        }
    }
    return $clock_data_dict
}
proc ai_get_first_outclk_node {clock_data_dict} {
    set outclk_pin_id "None"
    dict for {clock_key info} $clock_data_dict {
        dict with info {
            if {$node_type == "pin" && $is_valid} {
                set outclk_pin_id $pin_id
                break
            }
        }
    }
    if {$outclk_pin_id == "None"} {
        ai_post_message "warning" "Could not find any valid outclks"
    }
    return $outclk_pin_id 
}
# ----------------------------------------------------------------
#
proc ai_get_pll_pins { instname } {
#
# Description: Stores the pins of interest for the instance of the IP
#
# ----------------------------------------------------------------

    set base_clock_data_dict $::GLOBAL_top_io_pll_altera_iopll_1931_oypl3jq_base_clock_data
    set gen_clock_data_dict $::GLOBAL_top_io_pll_altera_iopll_1931_oypl3jq_gen_clock_data
    # First regsub the instance name for the pin names and patterns.
    set base_clock_data_dict [ai_subst_instname $base_clock_data_dict $instname]
    set gen_clock_data_dict [ai_subst_instname $gen_clock_data_dict $instname]


    set pll_parameters_dict [ai_get_pll_atom_parameters $instname] 
    set gen_clock_data_dict [ai_set_genclk_pin_info $gen_clock_data_dict]

    ai_post_message debug "gen_clock_data_dict initial: "
    print_clock_data $gen_clock_data_dict 
    
    # Traverse the first generated clock back to find FPGA pins for refclks.
    set outclk_node_id [ai_get_first_outclk_node $gen_clock_data_dict]
    if {$outclk_node_id != "None"} {
        set refclk_data_dict [ai_get_input_clk_info $outclk_node_id]
        ai_post_message debug "refclk_data_dict: "
        print_clock_data $refclk_data_dict

        set base_clock_data_dict [ai_set_baseclk_pin_info $base_clock_data_dict $refclk_data_dict $instname]
        set gen_clock_data_dict [ai_update_genclk_sources $base_clock_data_dict $gen_clock_data_dict $pll_parameters_dict]
        set gen_clock_data_dict [ai_update_genclk_div_mult $gen_clock_data_dict $pll_parameters_dict] 
        set base_clock_data_dict [ai_update_baseclk_data $base_clock_data_dict $pll_parameters_dict] 
        ai_post_message debug "base_clock_data_dict: "
        print_clock_data $base_clock_data_dict 
        ai_post_message debug "gen_clock_data_dict final: "
        print_clock_data $gen_clock_data_dict
    } else {
        # Make sure that we don't create any clock constraints
        # if no output clock was found
        set gen_clock_data_dict [ai_invalidate_clocks $gen_clock_data_dict]
    }
    
    return [list $base_clock_data_dict $gen_clock_data_dict]
    
}

# ----------------------------------------------------------------
#
proc ai_get_input_clk_info { outclk_pin_id } {
#
# Description: Searches back from the output of the PLL to find the reference clock pin.
#              If the reference clock is fed by an input buffer, it finds that pin, otherwise
#              in cascading modes it will return the immediate reference clock input of the PLL.
#
# ----------------------------------------------------------------
	if {[ai_is_node_type_pll_clk $outclk_pin_id]} {
        #stores the refclk pin ids that were found by tracing the 
        #output clocks back up
		array set refclk_array [list]
		ai_traverse_fanin_up_to_depth $outclk_pin_id ai_is_node_type_pll_inclk clock refclk_array 20
        array set refclk_info_array [list]
        foreach {net_id id} [array get refclk_array] {
            set net_name [get_node_info -name $net_id]
            set refclk_info_array($net_id) $net_name

        }
        # Dict to hold the refclk info found by traversing the netlist back.
        # refclk_data = {
        #   clock_id = {
        #       ref_pin_id: str,
        #       ref_pin_node_name: str,
        #       ref_port_id: str,
        #       ref_port_node_name: str,
        #       ref_is_fpga_pin: true/false,
        #   }
        # }
        set refclk_data [dict create]
        
        set clock_id 0

        #only works if there is either 1 or 2 refclks
		if {[array size refclk_array] == 1 || [array size refclk_array] == 2} {
            #iterate over each refclk pin and trace back to find its input port
            foreach refclk_pin_id [array names refclk_info_array] {
                array set user_refclk_array [list]
                array unset refclk_array
                array unset user_refclk_array [list]
					 
                ai_traverse_fanin_up_to_depth $refclk_pin_id ai_is_node_type_user_clock clock user_refclk_array 5
                ai_traverse_fanin_up_to_depth $refclk_pin_id ai_is_node_type_pin clock refclk_array 5
					 
                # If fed by any user specified clock (which could be specified at the pin level or at the
                # buffer level), then use that pin as the source.
                # Otherwise, trace back to the dedicated input pin (depth 5 so that we don't include global clocks)
                if {[array size user_refclk_array] == 1 || [array size refclk_array] < 1} {
                    # Fed by a user specified clock, a global clock etc. 
                    dict set refclk_data $clock_id ref_pin_id $refclk_pin_id 
                    dict set refclk_data $clock_id ref_pin_node_name $refclk_info_array($refclk_pin_id)
                    dict set refclk_data $clock_id ref_port_id ""
                    dict set refclk_data $clock_id ref_port_node_name ""
                    dict set refclk_data $clock_id ref_is_fpga_pin false
                } else {
                    # Fed by a dedicated input pin
                    set port_id_ [lindex [array names refclk_array] 0]

                    dict set refclk_data $clock_id ref_pin_id $refclk_pin_id 
                    dict set refclk_data $clock_id ref_pin_node_name $refclk_info_array($refclk_pin_id)
                    dict set refclk_data $clock_id ref_port_id $port_id_
                    dict set refclk_data $clock_id ref_port_node_name [get_node_info -name $port_id_]
                    dict set refclk_data $clock_id ref_is_fpga_pin true
                }

                incr clock_id
            }
        } else {
			ai_post_message critical_warning "Could not find PLL ref clock that feeds [get_node_info -name $outclk_pin_id]" all
		}
	} else {
		ai_post_message error "Internal error: ai_get_input_clk_info only works for PLL output clocks" all
	}
	return $refclk_data
}

# ----------------------------------------------------------------
#
proc ai_is_node_type_pin { node_id } {
#
# Description: Determines if a node is a top-level port of the FPGA
#
# ----------------------------------------------------------------

	set node_type [get_node_info -type $node_id]
	if {$node_type == "port"} {
		set result 1
	} else {
		set result 0
	}
	return $result
}

# ----------------------------------------------------------------
#
proc ai_is_node_type_user_clock { node_id } {
#
# Description: Determines if a node is a user-defined clock
#
# ----------------------------------------------------------------
    set node_name [get_node_info -name $node_id]	 
   
    if {[ai_clock_exists $node_name]} {
        return 1
    } else {
        return 0
    }
}

# ----------------------------------------------------------------
#
proc ai_is_node_type_pll_clk { node_id } {
#
# Description: Determines if a node is an output of a PLL
#
# ----------------------------------------------------------------

	set cell_id [get_node_info -cell $node_id]
	
	if {$cell_id == ""} {
		set result 0
	} else {
		set atom_type [get_cell_info -atom_type $cell_id]
		if {$atom_type == "IOPLL"} {
			set node_name [get_node_info -name $node_id]
            ai_post_message debug "Node_name: $node_name"
			if {[string match "*fourteennm_pll\|outclk\\\[*\\\]" $node_name]||[string match "*tennm_pll\|outclk\\\[*\\\]" $node_name]} {
				set result 1
			} elseif {[string match "*fourteennm_pll~ncntr_reg" $node_name]||[string match "*tennm_pll~ncntr_reg" $node_name]} {
				set result 1				
			} elseif {[string match "*fourteennm_pll~c*cntr_reg" $node_name]||[string match "*tennm_pll~c*cntr_reg" $node_name]} {
				set result 1				
			} elseif {[string match "*fourteennm_pll~mcntr_reg" $node_name]||[string match "*tennm_pll~mcntr_reg" $node_name]} {
				set result 1				
			} elseif {[string match "*fourteennm_pll\|lvds_clk\\\[*\\\]" $node_name]||[string match "*tennm_pll\|lvds_clk\\\[*\\\]" $node_name]} {
				set result 1				
			} elseif {[string match "*fourteennm_pll\|loaden\\\[*\\\]" $node_name]||[string match "*tennm_pll\|loaden\\\[*\\\]" $node_name]} {
				set result 1
			} elseif {[string match "*fourteennm_pll\|vcoph\\\[*\\\]" $node_name]||[string match "*tennm_pll\|vcoph\\\[*\\\]" $node_name]} {
				set result 1
			} elseif {[string match "*fourteennm_pll\|pll_cascade_out" $node_name]||[string match "*tennm_pll\|pll_cascade_out" $node_name]} {
				set result 1
			} elseif {[string match "*fourteennm_pll\|extclk_output\\\[*\\\]" $node_name]||[string match "*tennm_pll\|extclk_output\\\[*\\\]" $node_name]} {
				set result 1
			} else {
				set result 0
			}
		} else {
			set result 0
		}
	}
	return $result
}

# ----------------------------------------------------------------
#
proc ai_is_node_type_pll_inclk { node_id } {
#
# Description: Determines if a node is an input of a PLL
#
# ----------------------------------------------------------------


	set cell_id [get_node_info -cell $node_id]
	
	if {$cell_id == ""} {
		set result 0
	} else {
		set atom_type [get_cell_info -atom_type $cell_id]
		if {$atom_type == "IOPLL"} {
			set node_name [get_node_info -name $node_id]
			set fanin_edges [get_node_info -clock_edges $node_id]
			if {([string match "*|refclk\\\[*\\\]" $node_name]) && [llength $fanin_edges] > 0} {
				set result 1
            } elseif {([string match "*|pll_cascade_in" $node_name]) && [llength $fanin_edges] > 0} {
				set result 1
            } elseif {([string match "*|cascade_in" $node_name]) && [llength $fanin_edges] > 0} {
				set result 1
            } elseif {([string match "*|core_refclk" $node_name]) && [llength $fanin_edges] > 0} {
				set result 1
			} else {
				set result 0
			}
		} else {
			set result 0
		}
	}
	return $result
}

# -----------------------------------------------------------------
#
proc ai_find_pll_inclk { match_command edge_type } {
#
# Desciption: Finds the pll inclk pin whose name matches the
#             match_command. Returns the inclk pin name if such
#             a pin is found, and returns "" if it is not found
#
# -----------------------------------------------------------------

    set fanin_id ""
    foreach_in_collection pin [get_pins $match_command] {
        if {[llength [get_node_info -${edge_type}_edges $pin]] > 0} {
            set fanin_id $pin
            break
        }
    }
    return $fanin_id
}

# ----------------------------------------------------------------
#
proc ai_traverse_fanin_up_to_depth { node_id match_command edge_type results_array_name depth} {
#
# Description: General traversal function up until a depth.  Use a function pointer to decide
#              ending conditions.
#
# ----------------------------------------------------------------

	upvar 1 $results_array_name results

	if {$depth < 0} {
		error "Internal error: Bad timing netlist search depth"
	}

	ai_post_message debug "\[ai_traverse_fanin_up_to_depth\] called with node_id: $node_id cmd: \"$match_command\" type: $edge_type node: [get_node_info -name $node_id]"
	if {[is_post_syn_sta] && $match_command == "ai_is_node_type_pll_inclk"} {
		set atom_name [get_cell_info -name [get_node_info -cell $node_id]]
        set fanin_id [ai_find_pll_inclk $atom_name|core*refclk* $edge_type]
        if {$fanin_id == ""} {
            set fanin_id [ai_find_pll_inclk $atom_name|pll*cascade*in* $edge_type]
        }
        if {$fanin_id == ""} {
            set fanin_id [ai_find_pll_inclk $atom_name|ref*clk* $edge_type]
        }
		set results($fanin_id) 1
		ai_post_message debug "\[ai_traverse_fanin_up_to_depth\] post syn model returning fanin id: [get_node_info -name $fanin_id]"
		return
	}

	set fanin_edges [get_node_info -${edge_type}_edges $node_id]
	set number_of_fanin_edges [llength $fanin_edges]
	for {set i 0} {$i != $number_of_fanin_edges} {incr i} {
		set fanin_edge [lindex $fanin_edges $i]
		set fanin_id [get_edge_info -src $fanin_edge]
		if {$match_command == "" || [eval $match_command $fanin_id] != 0} {
			set results($fanin_id) 1
		} elseif {$depth == 0} {
		} else {
			ai_traverse_fanin_up_to_depth $fanin_id $match_command $edge_type results [expr {$depth - 1}]
		}
	}
}

# ----------------------------------------------------------------
#
proc ai_index_in_collection { col j } {
#
# Description: Returns a particular index in a collection.
#              Analagous to lindex for lists.
#
# ----------------------------------------------------------------

	set i 0
	foreach_in_collection path $col {
		if {$i == $j} {
			return $path
		}
		set i [expr $i + 1]
	}
	return ""
}

#
# Description: Rounds a given floating point number
#              to 3 decimal places
#
# ----------------------------------------------------------------
proc ai_round_3dp { x } {
    return [expr { round($x * 1000) / 1000.0  } ]
}

# ----------------------------------------------------------------
# Description: Checks whether a given clock already exists 
# ----------------------------------------------------------------
proc ai_clock_exists { clock_name } {
    set clock_found false
    set input_clocks_col [get_clocks -nowarn]
    set num_input_clocks [get_collection_size $input_clocks_col]
    
    if {$num_input_clocks > 0} {
        foreach_in_collection iclk $input_clocks_col {
            if {![is_clock_defined $iclk]} {
                continue
            }

            set clk_targets_col [get_clock_info -target $iclk]
            set num_clk_targets [get_collection_size $clk_targets_col]
            if {$num_clk_targets > 0} {
                foreach_in_collection itgt $clk_targets_col {
                    set node_name [get_node_info -name $itgt]
                    if {[string compare $node_name $clock_name] == 0} {
                        set clock_found true
                        break
                    }
                }
            }
            if {$clock_found == true} {
                break;
            }
        }
    }

   return $clock_found 
}

proc ai_get_pll_atom {instname} {
    foreach_in_collection node [get_atom_nodes -type IOPLL] {
        set name [get_atom_node_info -key NAME -node $node]
        set node_list($name) $node

        if {[string first $instname $name] > -1} {
            return $node
        }
    }
    set sdc_file_name [info script]
    ai_post_message warning "Could not find IOPLL atom with the name <$instname> while processing <$sdc_file_name>. Please check the synthesis report to ensure that the IOPLL was not synthesized away." all
}
proc ai_get_mult_div_factors {clock_key src ncnt mcnt ccnt counter_index \
                              compensated_counter_div compensation_mode \
                              clock_to_compensate} {
    if {$clock_key == "vcoph"} {
        set clock_mult $mcnt
        set clock_div 1
    } elseif {$clock_key == "n_cnt_clock"} {
        set clock_mult 1
        set clock_div $ncnt
    } elseif {$clock_key == "m_cnt_clock"} {
        set clock_mult 1
        set clock_div [expr {$mcnt * $ncnt}]
    } else {

        if {[string first "vcoph" $src] > -1} {
            set clock_mult 1
            set clock_div $ccnt
        } else {
            # Handle NDFB mode. 
            # The equation for counter which is to be compensated: C_k = M / N
            # The equation for all other counters:                 C_!k = (M * C_k) / (N * C_!k)
            if {$compensation_mode == "NON_DEDICATED_SOURCE_SYNC" || $compensation_mode == "NON_DEDICATED_NORMAL"} {
                if {$counter_index == $clock_to_compensate} {
                    set clock_mult $mcnt
                    # Instead of dividing by N, we just divide by 1
                    # since a clock based on the N counter would be created
                    # if N > 1 and this clock would be derived based on that,
                    # so we already have a division happening.
                    set clock_div 1
                } else {
                    set clock_mult [expr $mcnt * $compensated_counter_div]
                    set clock_div $ccnt
                }
            } else {
                ai_post_message debug "Normal C counter"
                set clock_mult $mcnt
                set clock_div $ccnt
            }
        }
    }
    return [list $clock_mult $clock_div]

}
# ----------------------------------------------------------------
#
proc ai_get_pll_atom_parameters {instname} {
#
# Description: Gets the PLL paramaters from the Quartus atom and not 
#              from the IP generated parameters.
#
# ----------------------------------------------------------------

    set pll_atom [ai_get_pll_atom $instname]
																			 
	dict set pll_params compensation_mode [get_atom_node_info -key ENUM_IOPLL_FEEDBACK -node $pll_atom]
	dict set pll_params clock_to_compensate [get_atom_node_info -key INT_IOPLL_CLOCK_TO_COMPENSATE -node $pll_atom]

    # Get refclk frequency (might have changed since IP generation)
    set refclk_freq [get_atom_node_info -key TIME_IOPLL_REFCLK_TIME -node $pll_atom]
    set refclk_int [string trim $refclk_freq "*MHZmhz"]
    set refclk_period [expr 1000.0 / $refclk_int]
    dict set pll_params refclk_period $refclk_period

	dict set pll_params m_hi_div [get_atom_node_info -key INT_IOPLL_M_COUNTER_HIGH -node $pll_atom]
	dict set pll_params m_lo_div [get_atom_node_info -key INT_IOPLL_M_COUNTER_LOW -node $pll_atom]
	dict set pll_params m_bypass [get_atom_node_info -key BOOL_IOPLL_M_COUNTER_BYPASS_EN -node $pll_atom]
    if {[dict get $pll_params m_bypass]} {
        set total 1
    } else {
        set total  [expr [dict get $pll_params m_hi_div] + [dict get $pll_params m_lo_div]]
    }
	dict set pll_params m_total $total

	dict set pll_params n_hi_div [get_atom_node_info -key INT_IOPLL_N_COUNTER_HIGH -node $pll_atom]
	dict set pll_params n_lo_div [get_atom_node_info -key INT_IOPLL_N_COUNTER_LOW -node $pll_atom]
	dict set pll_params n_bypass [get_atom_node_info -key BOOL_IOPLL_N_COUNTER_BYPASS_EN -node $pll_atom]
    if {[dict get $pll_params n_bypass]} {
        set total 1
    } else {
        set total  [expr [dict get $pll_params n_hi_div] + [dict get $pll_params n_lo_div]]
    }
	dict set pll_params n_total $total

	for { set i 0 } { $i < 9} { incr i } {
        # Get the C counter parameter settings from the atom netlist
        dict set pll_params c${i}_hi_div [get_atom_node_info -key INT_IOPLL_C${i}_HIGH -node $pll_atom]
        dict set pll_params c${i}_lo_div [get_atom_node_info -key INT_IOPLL_C${i}_LOW -node $pll_atom]
        dict set pll_params c${i}_bypass [get_atom_node_info -key BOOL_IOPLL_C${i}_BYPASS_EN -node $pll_atom]
        dict set pll_params c${i}_odd_div_duty_en [get_atom_node_info -key BOOL_IOPLL_C${i}_EVEN_DUTY_EN -node $pll_atom]

        # Calculate the total counter value
        if {[dict get $pll_params c${i}_bypass]} {
            set total 1
        } else {
            set total [expr [dict get $pll_params c${i}_hi_div] + [dict get $pll_params c${i}_lo_div]]
        }
        dict set pll_params c${i}_total $total

        # Calculate the duty cycle
        if {[dict get $pll_params c${i}_bypass]} {
            set total_duty 50
        } else {
            if {[dict get $pll_params c${i}_odd_div_duty_en]} {
                set duty_tweak 1
            } else {
                set duty_tweak 0
            }
            set total_duty [expr (([dict get $pll_params c${i}_hi_div] - (0.5*$duty_tweak))*100)/$total]
		    set total_duty [format %.3f $total_duty]
        }
        dict set pll_params duty_cycle${i} $total_duty
    }

    return $pll_params
}

#__ACDS_USER_COMMENT__Set max delay if in fit flow, otherwise set false path through "through_pin"
# originally in the LVDS SDC. This is called if we are exporting loaden to LVDS
proc set_max_delay_in_fit_or_false_path_in_sta_through_no_warn {through_pin delay} {

    set through_pin_collection [get_pins -compatibility_mode -nowarn $through_pin]
    if {[get_collection_size $through_pin_collection] <= 0} { return }
    
    # if fit_flow == 1
    if {$::TimeQuestInfo(nameofexecutable) == "quartus_fit" } { 
        set_max_delay -through $through_pin_collection $delay
    } else { 
        set_false_path -through $through_pin_collection
    } 
} 

# ----------------------------------------------------------------
#
proc is_m_n_cntr {pattern} {
#
# Description: Determines if a pattern matches m/n_cntr
#
# ----------------------------------------------------------------

    if {[string match "*fourteennm_pll~ncntr_reg" $pattern]||[string match "*tennm_pll~ncntr_reg" $pattern]||
        [string match "*fourteennm_pll~mcntr_reg" $pattern]||[string match "*tennm_pll~mcntr_reg" $pattern]||
        [string match "*tennm_ph2_iopll~ncntr_reg" $pattern]||[string match "*tennm_ph2_iopll~mcntr_reg" $pattern]} {
            return 1
    } else {
        return 0
    }
}

# ----------------------------------------------------------------
#
proc create_non_virtual_generated_clock_with_master_or_source \
{master source name multiply_by divide_by phase duty_cycle pin_node_name} {
#
# Description: Creates a non-virtual generated clock using
#              the -source or the -master argument
#
# ----------------------------------------------------------------
    if {$master != ""} {
        create_generated_clock -add \
            -master $master \
            -name $name \
            -multiply_by $multiply_by \
            -divide_by $divide_by \
            -phase $phase \
            -duty_cycle $duty_cycle \
            $pin_node_name
    } else {
        create_generated_clock -add \
            -source $source \
            -name $name \
            -multiply_by $multiply_by \
            -divide_by $divide_by \
            -phase $phase \
            -duty_cycle $duty_cycle \
            $pin_node_name
    }
}

# ----------------------------------------------------------------
#
proc create_virtual_generated_clock_with_master_or_source \
{master source name multiply_by divide_by phase duty_cycle} {
#
# Description: Creates a virtual generated clock using
#              the -source or the -master argument
#
# ----------------------------------------------------------------
    if {$master != ""} {
        create_generated_clock -add \
            -master $master \
            -name $name \
            -multiply_by $multiply_by \
            -divide_by $divide_by \
            -phase $phase \
            -duty_cycle $duty_cycle
    } else {
        create_generated_clock -add \
            -source $source \
            -name $name \
            -multiply_by $multiply_by \
            -divide_by $divide_by \
            -phase $phase \
            -duty_cycle $duty_cycle
    }
}
