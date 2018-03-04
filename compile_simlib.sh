source /opt/Xilinx/Vivado/2015.4/settings64.sh
unset LD_LIBRARY_PATH
export SNPSLMD_LICENSE_FILE=27023@lmserv-synopsys.cl.cam.ac.uk
export VCS_HOME=/opt/synopsys/M-2017.03-SP2-5
export PATH=$VCS_HOME/bin:$PATH
rm -rf compile_simlib
sed -e "s=~=$PWD=" -e "s=@=$VCS_HOME/bin=" > compile_simlib.tcl <<EOF
#close_project
create_project -force "vcs" .
set_property "default_lib" "xil_defaultlib" [current_project]
set_property "part" "xc7a100tcsg324-1" [current_project]
set_property "simulator_language" "Mixed" [current_project]
set_property target_simulator VCS [current_project]
set_property compxlib.vcs_compiled_library_dir ~/compile_simlib [current_project]
compile_simlib -force -language all -dir {~/compile_simlib} -simulator vcs_mx -simulator_exec_path {@} -library all -family artix7
EOF
vivado -mode batch -source compile_simlib.tcl
