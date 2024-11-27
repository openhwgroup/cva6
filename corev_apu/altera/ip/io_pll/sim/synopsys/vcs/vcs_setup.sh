
# (C) 2001-2024 Intel Corporation. All rights reserved.
# Your use of Intel Corporation's design tools, logic functions and 
# other software and tools, and its AMPP partner logic functions, and 
# any output files any of the foregoing (including device programming 
# or simulation files), and any associated documentation or information 
# are expressly subject to the terms and conditions of the Intel 
# Program License Subscription Agreement, Intel MegaCore Function 
# License Agreement, or other applicable license agreement, including, 
# without limitation, that your use is for the sole purpose of 
# programming logic devices manufactured by Intel and sold by Intel 
# or its authorized distributors. Please refer to the applicable 
# agreement for further details.

# ACDS 24.1 115 linux 2024.10.15.08:52:05

# ----------------------------------------
# vcs - auto-generated simulation script

# ----------------------------------------
# This script provides commands to simulate the following IP detected in
# your Quartus project:
#     io_pll
# 
# Intel recommends that you source this Quartus-generated IP simulation
# script from your own customized top-level script, and avoid editing this
# generated script.
# 
# To write a top-level shell script that compiles Intel simulation libraries
# and the Quartus-generated IP in your project, along with your design and
# testbench files, follow the guidelines below.
# 
# 1) Copy the shell script text from the TOP-LEVEL TEMPLATE section
# below into a new file, e.g. named "vcs_sim.sh".
# 
# 2) Copy the text from the DESIGN FILE LIST & OPTIONS TEMPLATE section into
# a separate file, e.g. named "filelist.f".
# 
# ----------------------------------------
# # TOP-LEVEL TEMPLATE - BEGIN
# #
# # TOP_LEVEL_NAME is used in the Quartus-generated IP simulation script to
# # set the top-level simulation or testbench module/entity name.
# #
# # QSYS_SIMDIR is used in the Quartus-generated IP simulation script to
# # construct paths to the files required to simulate the IP in your Quartus
# # project. By default, the IP script assumes that you are launching the
# # simulator from the IP script location. If launching from another
# # location, set QSYS_SIMDIR to the output directory you specified when you
# # generated the IP script, relative to the directory from which you launch
# # the simulator.
# #
# # Source the Quartus-generated IP simulation script and do the following:
# # - Compile the Quartus EDA simulation library and IP simulation files.
# # - Specify TOP_LEVEL_NAME and QSYS_SIMDIR.
# # - Compile the design and top-level simulation module/entity using
# #   information specified in "filelist.f".
# # - Insert "filelist.f" either before IPs using $USER_DEFINED_ELAB_OPTIONS 
# #   or after IPs using $USER_DEFINED_ELAB_OPTIONS_APPEND.
# # - Override the default USER_DEFINED_SIM_OPTIONS. For example, to run
# #   until $finish(), set to an empty string: USER_DEFINED_SIM_OPTIONS="".
# # - Run the simulation.
# #
# source <script generation output directory>/synopsys/vcs/vcs_setup.sh \
# TOP_LEVEL_NAME=<simulation top> \
# QSYS_SIMDIR=<script generation output directory> \
# USER_DEFINED_ELAB_OPTIONS="\"-f filelist.f\"" \
# USER_DEFINED_SIM_OPTIONS=<simulation options for your design>
# #
# # TOP-LEVEL TEMPLATE - END
# ----------------------------------------
# 
# ----------------------------------------
# # DESIGN FILE LIST & OPTIONS TEMPLATE - BEGIN
# #
# # Compile all design files and testbench files, including the top level.
# # (These are all the files required for simulation other than the files
# # compiled by the Quartus-generated IP simulation script)
# #
# +systemverilogext+.sv
# <design and testbench files, compile-time options, elaboration options>
# #
# # DESIGN FILE LIST & OPTIONS TEMPLATE - END
# ----------------------------------------
# 
# IP SIMULATION SCRIPT
# ----------------------------------------
# If io_pll is one of several IP cores in your
# Quartus project, you can generate a simulation script
# suitable for inclusion in your top-level simulation
# script by running the following command line:
# 
# ip-setup-simulation --quartus-project=<quartus project>
# 
# ip-setup-simulation will discover the Intel IP
# within the Quartus project, and generate a unified
# script which supports all the Intel IP within the design.
# ----------------------------------------
# ACDS 24.1 115 linux 2024.10.15.08:52:05
# ----------------------------------------
# initialize variables
TOP_LEVEL_NAME="io_pll"
QSYS_SIMDIR="./../../"
QUARTUS_INSTALL_DIR="/opt/Quartus/quartus/"
SKIP_FILE_COPY=0
SKIP_SIM=0
USER_DEFINED_ELAB_OPTIONS=""
USER_DEFINED_ELAB_OPTIONS_APPEND=""
USER_DEFINED_SIM_OPTIONS="+vcs+finish+100"
# ----------------------------------------
# overwrite variables - DO NOT MODIFY!
# This block evaluates each command line argument, typically used for 
# overwriting variables. An example usage:
#   sh <simulator>_setup.sh SKIP_SIM=1
for expression in "$@"; do
  eval $expression
  if [ $? -ne 0 ]; then
    echo "Error: This command line argument, \"$expression\", is/has an invalid expression." >&2
    exit $?
  fi
done

#-------------------------------------------
# check tclsh version no earlier than 8.5 
version=$(echo "puts [package vcompare [info tclversion] 8.5]; exit" | tclsh)
if [ $version -eq -1 ]; then 
  echo "Error: Minimum required tcl package version is 8.5." >&2 
  exit 1 
fi 
# ----------------------------------------
# initialize simulation properties - DO NOT MODIFY!
ELAB_OPTIONS=""
SIM_OPTIONS=""
if [[ `vcs -platform` != *"amd64"* && `vcs -platform` != *"suse64"* && `vcs -platform` != *"linux64"* ]]; then
  SIMULATOR_TOOL_BITNESS="bit_32"
else
  SIMULATOR_TOOL_BITNESS="bit_64"
fi
TCLSCRIPT='
set QSYS_SIMDIR [lindex $argv 1]
set SIMULATOR_TOOL_BITNESS [lindex $argv 2]
source $QSYS_SIMDIR/common/vcs_files.tcl
set LD_LIBRARY_PATH [dict create]
set LD_LIBRARY_PATH [dict merge $LD_LIBRARY_PATH [dict get [io_pll::get_env_variables $SIMULATOR_TOOL_BITNESS] "LD_LIBRARY_PATH"]]
if {[dict size $LD_LIBRARY_PATH] !=0 } {
  set LD_LIBRARY_PATH [join [dict keys $LD_LIBRARY_PATH] ":"]
  puts "LD_LIBRARY_PATH=\"$LD_LIBRARY_PATH\""
}

set ELAB_OPTIONS ""
append ELAB_OPTIONS [io_pll::get_elab_options $SIMULATOR_TOOL_BITNESS]
puts "ELAB_OPTIONS+=\"$ELAB_OPTIONS\""
set SIM_OPTIONS ""
append SIM_OPTIONS [io_pll::get_sim_options $SIMULATOR_TOOL_BITNESS]
puts "SIM_OPTIONS+=\"$SIM_OPTIONS\""
exit 0
'
cmd_output=$(
tclsh -args "$QSYS_SIMDIR" "$SIMULATOR_TOOL_BITNESS" << SCRIPT
  $TCLSCRIPT
SCRIPT
)

eval $cmd_output


# ----------------------------------------
# copy RAM/ROM files to simulation directory
TCLSCRIPT='
set QSYS_SIMDIR [lindex $argv 1]
set memory_files [list]
source $QSYS_SIMDIR/common/vcs_files.tcl
set memory_files [concat $memory_files [io_pll::get_memory_files "$QSYS_SIMDIR"]]
foreach file $memory_files { puts "$file" }
exit 0
'
cmd_output=$(
tclsh -args "$QSYS_SIMDIR" << SCRIPT
  $TCLSCRIPT
SCRIPT
)

memory_files=$cmd_output
if [ $SKIP_FILE_COPY -eq 0 ]; then
  for file in $memory_files
  do
    cp -f $file ./
  done
fi

# ----------------------------------------
# get common system verilog package design files
TCLSCRIPT='
set QSYS_SIMDIR [lindex $argv 1]
set files [dict create]
source $QSYS_SIMDIR/common/vcs_files.tcl
set files [dict merge $files [io_pll::get_common_design_files "$QSYS_SIMDIR"]]
set common_design_files [dict values $files]
foreach file $common_design_files { puts "$file" }
exit 0
'
cmd_output=$(
tclsh -args "$QSYS_SIMDIR" << SCRIPT
  $TCLSCRIPT
SCRIPT
)

common_design_files=$cmd_output

# ----------------------------------------
# get design files
TCLSCRIPT='
set QSYS_SIMDIR [lindex $argv 1]
source $QSYS_SIMDIR/common/vcs_files.tcl
if {[catch {io_pll::get_design_files "$QSYS_SIMDIR"} errorMsg]} {
 puts "Catch error: $errorMsg"
 exit 1 
}
set files [dict create]
set files [dict merge $files [io_pll::get_design_files "$QSYS_SIMDIR"]]
set design_files [dict values $files]
foreach file $design_files { puts "$file" }
exit 0
'
cmd_output=$(
tclsh -args "$QSYS_SIMDIR" << SCRIPT
  $TCLSCRIPT
SCRIPT
)

design_files=$cmd_output
if [[ "$cmd_output" =~ "Catch error" ]]; then 
  echo $cmd_output 
  exit 1 
fi 


# ----------------------------------------
# get DPI libraries
TCLSCRIPT='
set QSYS_SIMDIR [lindex $argv 1]
set libraries [dict create]
source $QSYS_SIMDIR/common/vcs_files.tcl
set libraries [dict merge $libraries [io_pll::get_dpi_libraries "$QSYS_SIMDIR"]]
set dpi_libraries [dict values $libraries]
foreach library $dpi_libraries { puts -nonewline "$library " }
exit 0
'
cmd_output=$(
tclsh -args "$QSYS_SIMDIR" << SCRIPT
  $TCLSCRIPT
SCRIPT
)

dpi_libraries=$cmd_output

if [ -n "$dpi_libraries" ]; then
  echo "Using DPI Library settings"
  LDFLAGS_LOCAL=""
  for library in $dpi_libraries; do
    library=$(readlink -m $library)
    FILENAME=${library##*/}
    LDFLAGS_LOCAL+=" -Wl,-rpath ${library%/*} -L ${library%/*} -l${FILENAME:3}"
  done
  export LDFLAGS="$LDFLAGS_LOCAL $LDFLAGS"
  ELAB_OPTIONS="$ELAB_OPTIONS -debug_access+r+w+nomemcbk"
fi

# ----------------------------------------
# add device library elaboration and simulation properties
ELAB_OPTIONS="$ELAB_OPTIONS $QUARTUS_INSTALL_DIR/eda/sim_lib/simsf_dpi.cpp +warn=noTFIPC,noRT-MTOCMUCS,noPCWM-W"

run_vcs="vcs -lca -timescale=1ps/1ps -sverilog +verilog2001ext+.v $ELAB_OPTIONS $USER_DEFINED_ELAB_OPTIONS \
  -v $QUARTUS_INSTALL_DIR/eda/sim_lib/220model.v \
  -v $QUARTUS_INSTALL_DIR/eda/sim_lib/sgate.v \
  -v $QUARTUS_INSTALL_DIR/eda/sim_lib/altera_primitives.v \
  -v $QUARTUS_INSTALL_DIR/eda/sim_lib/altera_mf.v \
  $QUARTUS_INSTALL_DIR/eda/sim_lib/altera_lnsim.sv \
  $QUARTUS_INSTALL_DIR/eda/sim_lib/tennm_atoms.sv \
  $QUARTUS_INSTALL_DIR/eda/sim_lib/synopsys/tennm_atoms_ncrypt.sv \
  $QUARTUS_INSTALL_DIR/eda/sim_lib/fmica_atoms_ncrypt.sv \
  $QUARTUS_INSTALL_DIR/eda/sim_lib/tennm_hssi_atoms.sv \
  $QUARTUS_INSTALL_DIR/eda/sim_lib/tennm_hssi_atoms_ncrypt.sv \
  $QUARTUS_INSTALL_DIR/eda/sim_lib/synopsys/cr3v0_serdes_models_ncrypt.sv \
  $QUARTUS_INSTALL_DIR/eda/sim_lib/ctp_hssi_atoms.sv \
  $QUARTUS_INSTALL_DIR/eda/sim_lib/ctp_hssi_atoms_ncrypt.sv \
  $common_design_files \
  $design_files \
  $USER_DEFINED_ELAB_OPTIONS_APPEND \
  -top $TOP_LEVEL_NAME
"
eval $run_vcs
# ----------------------------------------
# simulate
if [ $SKIP_SIM -eq 0 ]; then
  ./simv $SIM_OPTIONS $USER_DEFINED_SIM_OPTIONS
fi
