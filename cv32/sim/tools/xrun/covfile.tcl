# ----------------------------------------------------------------------------------
# General coverage configuration options
# ----------------------------------------------------------------------------------

# Setting Constant Object Marking and enabling log for it
set_com -log

# Disable scoring of implicit else and default case blocks
set_implicit_block_scoring -off

# Remove empty instances from coverage hierarchy
deselect_coverage -remove_empty_instances

# Enable resilience from code changes
set_refinement_resilience 

# Improve expression coverage performance
set_optimize -vlog_prune_on 

# Set glitch strobes
set_glitch_strobe 1ps

# ----------------------------------------------------------------------------------
# Expression coverage configuration
# ----------------------------------------------------------------------------------

# Setting expression scoring for all operators (not only boolean (|| &&) and VHDL (AND OR NOR NAND)
set_expr_scoring -all

# ----------------------------------------------------------------------------------
# Toggle coverage configuration
# ----------------------------------------------------------------------------------

# Toggle coverage smart refinement (refinement for toggle with traverse hierarchy)
set_toggle_smart_refinement
