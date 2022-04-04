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
# FSM coverage configruation
# ----------------------------------------------------------------------------------

# Enable scoring state hold arcs in FSM
set_fsm_scoring -hold_transition

# ----------------------------------------------------------------------------------
# Expression coverage configuration
# ----------------------------------------------------------------------------------

# Setting expression scoring for all operators (not only boolean (|| &&) and VHDL (AND OR NOR NAND)
set_expr_coverable_operators -all
set_expr_coverable_statements -all

# ----------------------------------------------------------------------------------
# Toggle coverage configuration
# ----------------------------------------------------------------------------------

# Toggle coverage smart refinement (refinement for toggle with traverse hierarchy)
set_toggle_smart_refinement

# ----------------------------------------------------------------------------------
# Covergroup coverage configuration
# ----------------------------------------------------------------------------------
set_covergroup -new_instance_reporting

# ----------------------------------------------------------------------------------
# Instances/modules to remove from coverage
# For performance and to avoid spurious warnings, remove these modules from code coverage collection
# ----------------------------------------------------------------------------------
deselect_coverage -all -instance uvmt_cv32e40x_tb.iss_wrap...