######################################################################################################
## File Name : Additional Option File
## Purpose   : To input additional SpyGlass options related to design read, reporting, setup, debugging etc 
## Type      : This is a tcl compatible file and can read all native tcl commands along with SpyGlass
##             commands.
## Usage     : This file is read via SpyGlass Project File(.prj).
#######################################################################################################

#### SectionA: Override the Global setup options/parameters as required by design #################### 
## Global setup file exists at '$SPYGLASS_IPKIT_DIR/setup_files/sg_global_options.tcl'
## To enable System Verilog Mode
set_option enableSV no
set_option enableSV09 yes
## To disable DW mode(Default is on)
#  set_option dw no 
## To disable module definition overriding(default is allowed) & report error 
#  set_option allow_module_override no 
## To define a new methresh value (default value set to 20000) 
#  set_option mthresh 20000
##  To define preference of reading .lib module over .v model
#  set_option prefer_tech_lib yes

######################################################################################################

#### SectionB: Debug Options ######################################################################### 
## To print the extra elaborator info to debug a crash or out-of-memory occuring during elaboration.
## O/p Generated: $wdir/spyglass_spysch/out.elab.log
#  set_option DEBUG {elaborator} 
## To debug issues(e.g crash etc) reported during HDL Parsing/Analysis. 
## O/p Generated: _spg_analyzer.debug 
#  set_option DEBUG {analysis}
## To debug information collected about the blackbox modules once after Elaboration & Synthesis  
## O/p Generated: on stdout
#  set_option DEBUG {bbox}
## To print the memory reduction details.
## O/p Generated: $wdir/spyglass_spysch/HandleMemory.dbg file 
#  set_option DEBUG {handlememory}
## To debug SGDC commands i.e how a particular command/variable has been interpreted by SpyGlass internally
## O/p Generated: $WDIR/_spg_sgdc.debug
#  set_option DEBUG {sgdc}
## To get the details of compiled technology library cells in sglib
## O/p Generated: debug_sglib.rpt and sglib_version_summary.rpt 
#  set_option DEBUG {sglib sgom}
## To get the details as how SpyGlass arrives at the final set of command 
## line options using the initial command line options provided by the user. 
## O/p Generated:spyglass_cmdline_debug.log
#  set_option enable_cmdline_debug yes 
## To disable the various sanity checks on user specified SGDC commands 
#  set_option no_sgdc_check yes
## To generate decompile information pertaining parsing of user specified SDC file 
## O/p Generated: <outdir>/$top/$top/<goal-name>/spyglass_spysch/spyglass_sdc/TCwritesdcInfo 
# set_parameter write_sdc yes
## To activate additonal information messages during SpyGlass run
## O/p Generated: at stdout and spyglass.log file 
#  set_option w yes
## To get information about all licenses that are checked out in the current SpyGlass run.
## O/p Generated: at stdout and spyglass.log
#  set_option LICENSEDEBUG yes
######################################################################################################

## SectionC: Other/Misc Options related to DesignRead, Analysis & Reporting ########################## 
## Precompiling a HDL(Verilog/VHDL) Library 
## Exmple commnd(vhdl)   : set_option libhdlfiles L1 "a.vhd b.vhd"
## Exmple commnd(verilog): set_option libhdlfiles L2 "a.v b.v"
## Exmple commnd(mixed)  : set_option libhdlfiles L3 "a.v b.vhd"

## Logical to Physical library mapping for precompiled libraries
## Example command :  set_option lib L1 /PROJECT_DIR/results/spyglass_precompile/L1_lib
######################################################################################################
set_option incdir ../core/include
set_option incdir ../common/local/util/
set_option incdir ../core/cvxif_example
#~ set_option incdir ../common/local/util
set_option incdir ../vendor/pulp-platform/axi/include
set_option incdir ../vendor/pulp-platform/common_cells/src
set_option incdir ../vendor/pulp-platform/common_cells/include/
set_option incdir ../core/cache_subsystem/hpdcache/rtl/
