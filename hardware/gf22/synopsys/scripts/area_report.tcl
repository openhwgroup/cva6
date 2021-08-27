##################################################################################
##################################################################################
##                                                                              ##
##  Version   : 1.0                                                             ##
##  Date, Day : 19-June-2008, Thursday                                          ##
##  Developer : Sumit Garg (sumitg@synopsys.com)                                ##
##  Support   : Drop me an e-mail at sumitg@synopsys.com about your feedback,   ##
##              suggestions or any related issues.                              ##
##                                                                              ##
##################################################################################
##################################################################################

set Red    "\033\[00;31m"
set Black  "\033\[0;30m"
set Blue   "\033\[0;34m"
set Green  "\033\[0;32m"
set Cyan   "\033\[0;36m"
set Red    "\033\[0;31m"
set Purple "\033\[0;35m"
set Brown  "\033\[0;33m"
set Yellow "\033\[1;33m"
set White  "\033\[1;37m"
set NC     "\033\[0m"


## Main proc starts
proc area_report { args } {
   
    set ::char  { }
    set ::level 1
    set   crlvl 0
    set maxlen  [string length "Reference Name"]
    array unset ::har
    array   set ::har ""
    parse_proc_arguments -arg ${args} options
    if {[info exists options(-levels)]} {
        set ::level $options(-levels)
    }
    
    echo ""
    echo "*************************************"
    echo " Report  : Area                      "
    echo " Design  : [current_design_name]     "  
    echo " Version : $::sh_product_version     "
    echo " Date    : [date]                    "
    echo "*************************************"
    echo ""

    set leaf_cell [sizeof_collection [get_cells -hierarchical -filter "is_hierarchical==false"]]
    set comb_cell [sizeof_collection [get_cells -hierarchical -filter "is_hierarchical==false && is_combinational==true" ]]
    set  seq_cell [sizeof_collection [get_cells -hierarchical -filter "is_hierarchical==false && is_combinational==false"]]
    #set  seq_cell [sizeof_collection [get_cells -hierarchical -filter "is_hierarchical==false && is_sequential==true"]]
    redirect -var arearpt { report_area -nosplit }
    regexp {Total cell area: +(.*?)\n.*} $arearpt match area
    regexp {Combinational area: +(.*?)\n.*} $arearpt match comb_area
    regexp {Noncombinational area: +(.*?)\n.*} $arearpt match seq_area
    set ::har([string repeat ${::char} [expr ${crlvl}*4]][current_design_name]) "${leaf_cell} ${comb_cell} ${seq_cell} ${area} ${comb_area} ${seq_area}"
    lappend ::har() "[string repeat ${::char} [expr ${crlvl}*4]][current_design_name]"

    if {${::level} > 0 } {
	incr crlvl
        set hier_cell [get_cells * -filter "is_hierarchical==true"]
	foreach_in_collection cell ${hier_cell} {
	    instance_stat ${cell} ${crlvl}
	}
    }
    foreach name $::har() {
        set len [string length ${name}]
	if {$len > $maxlen} {
	    set maxlen $len
	}
    }

    echo "[format " %-*s %*s %*s %*s %*s %*s %*s " [expr ${maxlen}+4] "Reference Name" 10 "Cell Count" 10 "Comb." 10 "Seq." 15 "Area" 12 "Comb." 12 "Seq."]"
    echo "[format " %-*s   %*s %*s %*s %*s %*s %*s " ${maxlen} [string repeat {-} ${maxlen}] 0 "" 0 "" 32 [string repeat {-} 32] 0 "" 0 "" 39 [string repeat {-} 39] ]"
    
    foreach name $::har() {
        set  tot_count [format %.0f [lindex $::har($name) 0]]
        set comb_count [format %.0f [lindex $::har($name) 1]]
        set  seq_count [format %.0f [lindex $::har($name) 2]]
	set  tot_area  [format %.2f [lindex $::har($name) 3]]
	set comb_area  [format %.2f [lindex $::har($name) 4]]
	set  seq_area  [format %.2f [lindex $::har($name) 5]]
	echo "[format " %-*s %*.0f %*.0f %*.0f %*.2f %*.2f %*.2f " [expr ${maxlen}+4] ${name} 10 ${tot_count} 10 ${comb_count} 10 ${seq_count} 15 ${tot_area} 12 ${comb_area} 12 ${seq_area} ]"
    }
    echo ""
    return 1
}
    	 
proc instance_stat { inst crlvl } {
    redirect /dev/null {set orig [current_instance .]}
    redirect /dev/null {current_instance $inst}
    set mstr_name [get_attribute -quiet [get_cells $inst] ref_name]
    set leaf_cell [sizeof_collection [get_cells -hierarchical -filter "is_hierarchical==false"]]
    set comb_cell [sizeof_collection [get_cells -hierarchical -filter "is_hierarchical==false && is_combinational==true" ]]
    set  seq_cell [sizeof_collection [get_cells -hierarchical -filter "is_hierarchical==false && is_combinational==false"]]
    #set  seq_cell [sizeof_collection [get_cells -hierarchical -filter "is_hierarchical==false && is_sequential==true"]]
    redirect -var arearpt { report_area -nosplit }
    regexp {Total cell area: +(.*?)\n.*} $arearpt match area
    regexp {Combinational area: +(.*?)\n.*} $arearpt match comb_area
    regexp {Noncombinational area: +(.*?)\n.*} $arearpt match seq_area
    set ::har([string repeat ${::char} [expr ${crlvl}*4]]${mstr_name}) "${leaf_cell} ${comb_cell} ${seq_cell} ${area} ${comb_area} ${seq_area}"
    lappend ::har() "[string repeat ${::char} [expr ${crlvl}*4]]${mstr_name}"
    incr crlvl
    if { ${crlvl} <= ${::level} } {
        set hier_cell [get_cells * -filter "is_hierarchical==true"]
        foreach_in_collection cell ${hier_cell} {
	    instance_stat ${cell} ${crlvl}
        }
    }
    redirect /dev/null {current_instance $orig}
}   
    
define_proc_attributes area_report  \
      -info "Generate an hierarchical area report" \
      -hide_body \
      -define_arg { \
      { -levels   "Levels of hierarchy to be parsed when generating area report (default: 1)" "Integer" int optional }
                  }

## script ends ##
