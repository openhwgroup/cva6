# Create project.
create_project vivado . -force -part xc7vx485tffg1157-1

# Downgrade warning about "ignoring assertions" to information.
set_msg_config -id {[Synth 8-2898]} -new_severity "info"

# Add source files to project.
add_files -norecurse -scan_for_includes [glob ./deps/*]
add_files -norecurse -scan_for_includes [glob ./src/*]

# Define top-level module.
set_property top Top [current_fileset]

# Update compile order (must do if in batch mode).
update_compile_order -fileset [current_fileset]
