# cva6.sv has a single clock
set clk_name clk
set clk_port_name clk
set clk_period 2000

# Use https://github.com/The-OpenROAD-Project/OpenROAD-flow-scripts/blob/master/flow/platforms/asap7/constraints.sdc
if {[llength [all_registers]] > 0} {
  source $env(PLATFORM_DIR)/constraints.sdc
} else {
  # No registers if we're creating a mock .lef file eviscerated RTL,
  # keeping only the pins.
}

