start_gui
create_project alsaqr /scratch/lvalente/project/arianissimo2/cva6/hardware/fpga/alsaqr -part xczu9eg-ffvb1156-2-e
source ./alsaqr/tcl/generated/compile.tcl
set_property top al_saqr [current_fileset]
read_xdc ./alsaqr/tcl/constraints.xdc
update_compile_order -fileset sources_1
auto_detect_xpm
synth_design
