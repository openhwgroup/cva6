start_gui
create_project alsaqr /scratch/lvalente/project/arianissimo2/cva6/hardware/fpga/alsaqr -part xczu9eg-ffvb1156-2-e
source ./alsaqr/tcl/generated/compile.tcl
set_property top alsaqr_xilinx [current_fileset]
read_xdc ./alsaqr/tcl/constraints.xdc
read_ip ./alsaqr/tcl/ips/clk_mngr/ip/xilinx_clk_mngr.xci
add_files -fileset constrs_1 -norecurse "tcl/fmc_board_$::env(BOARD).xdc"
update_compile_order -fileset sources_1
auto_detect_xpm
synth_design
