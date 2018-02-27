#close_project
create_project -force "vcs" .
set_property "default_lib" "xil_defaultlib" [current_project]
set_property "part" "xc7a100tcsg324-1" [current_project]
set_property "simulator_language" "Mixed" [current_project]
set_property target_simulator VCS [current_project]
set_property compxlib.vcs_compiled_library_dir /local/scratch/jrrk2/ariane/compile_simlib [current_project]
compile_simlib -force -language all -dir {/local/scratch/jrrk2/ariane/compile_simlib} -simulator vcs_mx -simulator_exec_path {/opt/synopsys/M-2017.03-SP2-5/bin} -library all -family artix7
