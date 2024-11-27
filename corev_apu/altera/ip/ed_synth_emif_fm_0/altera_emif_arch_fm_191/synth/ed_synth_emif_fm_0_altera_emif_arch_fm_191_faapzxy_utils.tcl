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



set script_dir [file dirname [info script]]

load_package sdc_ext
load_package design

proc ed_synth_emif_fm_0_altera_emif_arch_fm_191_faapzxy_index_in_collection { col j } {
   set i 0
   foreach_in_collection path $col {
      if {$i == $j} {
         return $path
      }
      set i [expr $i + 1]
   }
   return ""
}


proc ed_synth_emif_fm_0_altera_emif_arch_fm_191_faapzxy_get_clock_to_pin_name_mapping {} {
   set result [list]
   set clocks_collection [get_clocks]
   foreach_in_collection clock $clocks_collection {
      if { ![is_clock_defined $clock] } {
         continue
      }
      set clock_name [get_clock_info -name $clock]
      set clock_target [get_clock_info -targets $clock]
      set first_index [ed_synth_emif_fm_0_altera_emif_arch_fm_191_faapzxy_index_in_collection $clock_target 0]
      set catch_exception_net [catch {get_net_info -name $first_index} pin_name_net]
      if {$catch_exception_net == 0} {
         lappend result [list $clock_name $pin_name_net]
      } else {
         set catch_exception_port [catch {get_port_info -name $first_index} pin_name_port]
         if {$catch_exception_port == 0} {
            lappend result [list $clock_name $pin_name_port]
         } else {
            set catch_exception_reg [catch {get_register_info -name $first_index} pin_name_reg]
            if {$catch_exception_reg == 0} {
               lappend result [list $clock_name $pin_name_reg]
            } else {
               set catch_exception_pin [catch {get_pin_info -name $first_index} pin_name_pin]
               if {$catch_exception_pin == 0} {
                  lappend result [list $clock_name $pin_name_pin]
               }
            }
         }
      }
   }
   return $result
}


proc ed_synth_emif_fm_0_altera_emif_arch_fm_191_faapzxy_get_clock_name_from_pin_name { pin_name } {
   set table [ed_synth_emif_fm_0_altera_emif_arch_fm_191_faapzxy_get_clock_to_pin_name_mapping]
   foreach entry $table {
      if {[string compare [lindex [lindex [split $entry] 1] 0] $pin_name] == 0} {
         return [lindex $entry 0]
      }
   }
   return ""
}



proc ed_synth_emif_fm_0_altera_emif_arch_fm_191_faapzxy_find_all_keepers { mystring } {
   set allkeepers [get_keepers $mystring ]

   foreach_in_collection keeper $allkeepers {
      set keepername [ get_node_info -name $keeper ]

      puts "$keepername"
   }
}

proc ed_synth_emif_fm_0_altera_emif_arch_fm_191_faapzxy_round_3dp { x } {
   return [expr { round($x * 1000) / 1000.0  } ]
}

proc ed_synth_emif_fm_0_altera_emif_arch_fm_191_faapzxy_get_current_timequest_report_folder {} {

   set catch_exception [catch {get_current_timequest_report_folder} error_message]
   if {[regexp ERROR $error_message] == 1} {
      return "ReportDDR"
   } else {
      return [get_current_timequest_report_folder]
   }
}

proc ed_synth_emif_fm_0_altera_emif_arch_fm_191_faapzxy_get_timequest_name {hier_name} {
   set sta_name $hier_name
   return $sta_name
}

proc ed_synth_emif_fm_0_altera_emif_arch_fm_191_faapzxy_are_entity_names_on { } {
   return [set_project_mode -is_show_entity]
}

proc ed_synth_emif_fm_0_altera_emif_arch_fm_191_faapzxy_get_core_instance_list {corename} {
   global ::io_only_analysis

   if {$::io_only_analysis == 1}  {
      set instance_list [list $corename]

   } else {
      set full_instance_list [ed_synth_emif_fm_0_altera_emif_arch_fm_191_faapzxy_get_core_full_instance_list $corename]
      set instance_list [list]

      foreach inst $full_instance_list {
         set sta_name [ed_synth_emif_fm_0_altera_emif_arch_fm_191_faapzxy_get_timequest_name $inst]
         if {[lsearch $instance_list [escape_brackets $sta_name]] == -1} {
            lappend instance_list $sta_name
         }
      }

   }
   return $instance_list
}

proc ed_synth_emif_fm_0_altera_emif_arch_fm_191_faapzxy_get_or_add_generated_clock {args} {
   array set opts [list -name "" -target "" -source "" -multiply_by 1 -divide_by 1 -phase 0]
   array set opts $args

   set multiply_by [expr int($opts(-multiply_by))]
   if {[expr $multiply_by - $opts(-multiply_by)] != 0.0} {
      post_message -type error "Specify an integer ranging from 0 to 99999999 for the option -multiply_by"
      return ""
   }

   set clock_name [ed_synth_emif_fm_0_altera_emif_arch_fm_191_faapzxy_get_clock_name_from_pin_name $opts(-target)]

   if {[string compare -nocase $clock_name ""] == 0} {
      set nets [get_nets $opts(-target) -nowarn]
      if {[get_collection_size $nets] > 0} {
         set pin_name [get_pin_info -name [get_net_info -pin $nets]]
         set clock_name [ed_synth_emif_fm_0_altera_emif_arch_fm_191_faapzxy_get_clock_name_from_pin_name $pin_name]

         if {[string compare -nocase $clock_name ""] != 0} {
            if {[regexp -nocase "lvds_clk" $pin_name] || [regexp -nocase "loaden" $pin_name] } {
               remove_clock $clock_name
               set clock_name ""
            }
          }
       }
   } else {
      if {([string compare -nocase $opts(-name) ""] != 0) && ([string compare -nocase $opts(-name) $clock_name])} {

         if {[regexp -nocase "pll_inst\|outclk" $opts(-target)]} {
            remove_clock $clock_name
            set clock_name ""
         }
      }
   }

   if {[string compare -nocase $clock_name ""] == 0} {
      set clock_name $opts(-name)

      create_generated_clock \
         -name $clock_name \
         -source $opts(-source) \
         -multiply_by $multiply_by \
         -divide_by $opts(-divide_by) \
         -phase $opts(-phase) \
         $opts(-target)
   }

   return $clock_name
}

proc ed_synth_emif_fm_0_altera_emif_arch_fm_191_faapzxy_get_core_full_instance_list {corename} {

   set instance_list [list]

   if {[is_fitter_in_qhd_mode]} {
      set instance_list_pre [design::get_instances -entity $corename]

   } else {
      set instance_list_pre [get_entity_instances $corename]
   }

   foreach instance $instance_list_pre {
      regsub {\|arch$} $instance "" instance_no_arch
      lappend instance_list $instance_no_arch
   }

   if {[ llength $instance_list ] == 0} {
      post_message -type error "The auto-constraining script was not able to detect any instance for core < $corename >"
      post_message -type error "Make sure the core < $corename > is instantiated within another component (wrapper)"
      post_message -type error "and it's not the top-level for your project"
   }

   return $instance_list
}


proc ed_synth_emif_fm_0_altera_emif_arch_fm_191_faapzxy_traverse_fanin_up_to_depth { node_id match_command edge_type results_array_name depth} {
   upvar 1 $results_array_name results

   if {$depth < 0} {
      error "Internal error: Bad timing netlist search depth"
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
         ed_synth_emif_fm_0_altera_emif_arch_fm_191_faapzxy_traverse_fanin_up_to_depth $fanin_id $match_command $edge_type results [expr {$depth - 1}]
      }
   }
}

proc ed_synth_emif_fm_0_altera_emif_arch_fm_191_faapzxy_is_node_type_pin { node_id } {
   set node_type [get_node_info -type $node_id]
   if {$node_type == "port"} {
      set result 1
   } else {
      set result 0
   }
   return $result
}

proc ed_synth_emif_fm_0_altera_emif_arch_fm_191_faapzxy_get_pll_clock_name { clock_id } {
   set clock_name [get_node_info -name $clock_id]

   return $clock_name
}

proc post_sdc_message {msg_type msg} {
   global ::io_only_analysis

   if {($::io_only_analysis == 1) || $::TimeQuestInfo(nameofexecutable) != "quartus_fit"} {
      post_message -type $msg_type $msg
   }
}

proc ed_synth_emif_fm_0_altera_emif_arch_fm_191_faapzxy_get_names_in_collection { col } {
   set res [list]
   foreach_in_collection node $col {
      lappend res [ get_node_info -name $node ]
   }
   return $res
}

proc ed_synth_emif_fm_0_altera_emif_arch_fm_191_faapzxy_format_3dp { x } {
   return [format %.3f $x]
}

proc ed_synth_emif_fm_0_altera_emif_arch_fm_191_faapzxy_get_colours { x y } {

   set fcolour [list "black"]
   if {$x < 0} {
      lappend fcolour "red"
   } else {
      lappend fcolour "blue"
   }
   if {$y < 0} {
      lappend fcolour "red"
   } else {
      lappend fcolour "blue"
   }

   return $fcolour
}

proc min { a b } {
   if { $a == "" } {
      return $b
   } elseif { $a < $b } {
      return $a
   } else {
      return $b
   }
}

proc max { a b } {
   if { $a == "" } {
      return $b
   } elseif { $a > $b } {
      return $a
   } else {
      return $b
   }
}

proc ed_synth_emif_fm_0_altera_emif_arch_fm_191_faapzxy_max_in_collection { col attribute } {
   set i 0
   set max 0
   foreach_in_collection path $col {
      if {$i == 0} {
         set max [get_path_info $path -${attribute}]
      } else {
         set temp [get_path_info $path -${attribute}]
         if {$temp > $max} {
            set max $temp
         }
      }
      set i [expr $i + 1]
   }
   return $max
}

proc ed_synth_emif_fm_0_altera_emif_arch_fm_191_faapzxy_min_in_collection { col attribute } {
   set i 0
   set min 0
   foreach_in_collection path $col {
      if {$i == 0} {
         set min [get_path_info $path -${attribute}]
      } else {
         set temp [get_path_info $path -${attribute}]
         if {$temp < $min} {
            set min $temp
         }
      }
      set i [expr $i + 1]
   }
   return $min
}

proc ed_synth_emif_fm_0_altera_emif_arch_fm_191_faapzxy_min_in_collection_to_clock { col attribute clock } {
   set i 0
   set min ERROR
   foreach_in_collection path $col {
      if {[get_clock_info -name [get_path_info $path -to_clock]] == $clock} {
         if {$i == 0} {
            set min [get_path_info $path -${attribute}]
         } else {
            set temp [get_path_info $path -${attribute}]
            if {$temp < $min} {
               set min $temp
            }
         }
         set i [expr $i + 1]
      }
   }
   return $min
}

proc ed_synth_emif_fm_0_altera_emif_arch_fm_191_faapzxy_min_in_collection_from_clock { col attribute clock } {
   set i 0
   set min ERROR
   foreach_in_collection path $col {
      if {[get_clock_info -name [get_path_info $path -from_clock]] == $clock} {
         if {$i == 0} {
            set min [get_path_info $path -${attribute}]
         } else {
            set temp [get_path_info $path -${attribute}]
            if {$temp < $min} {
               set min $temp
            }
         }
         set i [expr $i + 1]
      }
   }
   return $min
}

proc ed_synth_emif_fm_0_altera_emif_arch_fm_191_faapzxy_min_in_collection_to_name { col attribute name } {
   set i 0
   set min 0
   foreach_in_collection path $col {
      if {[get_node_info -name [get_path_info $path -to]] == $name} {
         if {$i == 0} {
            set min [get_path_info $path -${attribute}]
         } else {
            set temp [get_path_info $path -${attribute}]
            if {$temp < $min} {
               set min $temp
            }
         }
         set i [expr $i + 1]
      }
   }
   return $min
}

proc ed_synth_emif_fm_0_altera_emif_arch_fm_191_faapzxy_min_in_collection_from_name { col attribute name } {
   set i 0
   set min 0
   foreach_in_collection path $col {
      if {[get_node_info -name [get_path_info $path -from]] == $name} {
         if {$i == 0} {
            set min [get_path_info $path -${attribute}]
         } else {
            set temp [get_path_info $path -${attribute}]
            if {$temp < $min} {
               set min $temp
            }
         }
         set i [expr $i + 1]
      }
   }
   return $min
}

proc ed_synth_emif_fm_0_altera_emif_arch_fm_191_faapzxy_max_in_collection_to_name { col attribute name } {
   set i 0
   set max 0
   foreach_in_collection path $col {
      if {[get_node_info -name [get_path_info $path -to]] == $name} {
         if {$i == 0} {
            set max [get_path_info $path -${attribute}]
         } else {
            set temp [get_path_info $path -${attribute}]
            if {$temp > $max} {
               set max $temp
            }
         }
         set i [expr $i + 1]
      }
   }
   return $max
}

proc ed_synth_emif_fm_0_altera_emif_arch_fm_191_faapzxy_max_in_collection_from_name { col attribute name } {
   set i 0
   set max 0
   foreach_in_collection path $col {
      if {[get_node_info -name [get_path_info $path -from]] == $name} {
         if {$i == 0} {
            set max [get_path_info $path -${attribute}]
         } else {
            set temp [get_path_info $path -${attribute}]
            if {$temp > $max} {
               set max $temp
            }
         }
         set i [expr $i + 1]
      }
   }
   return $max
}


proc ed_synth_emif_fm_0_altera_emif_arch_fm_191_faapzxy_min_in_collection_to_name2 { col attribute name } {
   set i 0
   set min 0
   foreach_in_collection path $col {
      if {[regexp $name [get_node_info -name [get_path_info $path -to]]]} {
         if {$i == 0} {
            set min [get_path_info $path -${attribute}]
         } else {
            set temp [get_path_info $path -${attribute}]
            if {$temp < $min} {
               set min $temp
            }
         }
         set i [expr $i + 1]
      }
   }
   return $min
}

proc ed_synth_emif_fm_0_altera_emif_arch_fm_191_faapzxy_min_in_collection_from_name2 { col attribute name } {
   set i 0
   set min 0
   foreach_in_collection path $col {
      if {[regexp $name [get_node_info -name [get_path_info $path -from]]]} {
         if {$i == 0} {
            set min [get_path_info $path -${attribute}]
         } else {
            set temp [get_path_info $path -${attribute}]
            if {$temp < $min} {
               set min $temp
            }
         }
         set i [expr $i + 1]
      }
   }
   return $min
}

proc ed_synth_emif_fm_0_altera_emif_arch_fm_191_faapzxy_max_in_collection_to_name2 { col attribute name } {
   set i 0
   set max 0
   foreach_in_collection path $col {
      if {[regexp $name [get_node_info -name [get_path_info $path -to]]]} {
         if {$i == 0} {
            set max [get_path_info $path -${attribute}]
         } else {
            set temp [get_path_info $path -${attribute}]
            if {$temp > $max} {
               set max $temp
            }
         }
         set i [expr $i + 1]
      }
   }
   return $max
}

proc ed_synth_emif_fm_0_altera_emif_arch_fm_191_faapzxy_max_in_collection_from_name2 { col attribute name } {
   set i 0
   set max 0
   foreach_in_collection path $col {
      if {[regexp $name [get_node_info -name [get_path_info $path -from]]]} {
         if {$i == 0} {
            set max [get_path_info $path -${attribute}]
         } else {
            set temp [get_path_info $path -${attribute}]
            if {$temp > $max} {
               set max $temp
            }
         }
         set i [expr $i + 1]
      }
   }
   return $max
}

proc ed_synth_emif_fm_0_altera_emif_arch_fm_191_faapzxy_sort_proc {a b} {
   set idxs [list 1 2 0]
   foreach i $idxs {
      set ai [lindex $a $i]
      set bi [lindex $b $i]
      if {$ai > $bi} {
         return 1
      } elseif { $ai < $bi } {
         return -1
      }
   }
   return 0
}

proc ed_synth_emif_fm_0_altera_emif_arch_fm_191_faapzxy_gcd {p q} {
   set p [expr {abs($p)}]
   set q [expr {abs($q)}]
   while {$q != 0} {
      set r [expr {$p % $q}]
      set p $q
      set q $r
   }
   return $p
}

proc ed_synth_emif_fm_0_altera_emif_arch_fm_191_faapzxy_traverse_atom_path {atom_id atom_oport_id path} {
   # Return list of {atom oterm_id} pairs by tracing the atom netlist starting from the given atom_id through the given path
   # Path consists of list of {atom_type fanin|fanout|end <port_type> <-optional>}
   set result [list]
   if {[llength $path] > 0} {
      set path_point [lindex $path 0]
      set atom_type [lindex $path_point 0]
      set next_direction [lindex $path_point 1]
      set port_type [lindex $path_point 2]
      set atom_optional [lindex $path_point 3]
      if {[get_atom_node_info -key type -node $atom_id] == $atom_type} {
         if {$next_direction == "end"} {
            if {[get_atom_port_info -key type -node $atom_id -port_id $atom_oport_id -type oport] == $port_type} {
               lappend result [list $atom_id $atom_oport_id]
            }
         } elseif {$next_direction == "atom"} {
            lappend result [list $atom_id]
         } elseif {$next_direction == "fanin"} {
            set atom_iport [get_atom_iport_by_type -node $atom_id -type $port_type]
            if {$atom_iport != -1} {
               set iport_fanin [get_atom_port_info -key fanin -node $atom_id -port_id $atom_iport -type iport]
               set source_atom [lindex $iport_fanin 0]
               set source_oterm [lindex $iport_fanin 1]
               set result [ed_synth_emif_fm_0_altera_emif_arch_fm_191_faapzxy_traverse_atom_path $source_atom $source_oterm [lrange $path 1 end]]
            } elseif {$atom_optional == "-optional"} {
               set result [ed_synth_emif_fm_0_altera_emif_arch_fm_191_faapzxy_traverse_atom_path $atom_id $atom_oport_id [lrange $path 1 end]]
            }
         } elseif {$next_direction == "fanout"} {
            set atom_oport [get_atom_oport_by_type -node $atom_id -type $port_type]
            if {$atom_oport != -1} {
               set oport_fanout [get_atom_port_info -key fanout -node $atom_id -port_id $atom_oport -type oport]
               foreach dest $oport_fanout {
                  set dest_atom [lindex $dest 0]
                  set dest_iterm [lindex $dest 1]
                  set fanout_result_list [ed_synth_emif_fm_0_altera_emif_arch_fm_191_faapzxy_traverse_atom_path $dest_atom -1 [lrange $path 1 end]]
                  foreach fanout_result $fanout_result_list {
                     if {[lsearch $result $fanout_result] == -1} {
                        lappend result $fanout_result
                     }
                  }
               }
            }
         } else {
            error "Unexpected path"
         }
      } elseif {$atom_optional == "-optional"} {
         set result [ed_synth_emif_fm_0_altera_emif_arch_fm_191_faapzxy_traverse_atom_path $atom_id $atom_oport_id [lrange $path 1 end]]
      }
   }
   return $result
}

proc ed_synth_emif_fm_0_altera_emif_arch_fm_191_faapzxy_get_operating_conditions_number {} {
   set cur_operating_condition [get_operating_conditions]
   set counter 0
   foreach_in_collection op [get_available_operating_conditions] {
      if {[string compare $cur_operating_condition $op] == 0} {
         return $counter
      }
      incr counter
   }
   return $counter
}
