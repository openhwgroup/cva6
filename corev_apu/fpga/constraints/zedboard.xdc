set_property PACKAGE_PIN Y9 [get_ports clk_sys]
set_property IOSTANDARD LVCMOS33 [get_ports clk_sys]

## Buttons
set_property -dict {PACKAGE_PIN P16 IOSTANDARD LVCMOS33} [get_ports cpu_reset]

## To use FTDI FT2232 JTAG
set_property -dict {PACKAGE_PIN W12 IOSTANDARD LVCMOS33} [get_ports trst_n]
set_property -dict {PACKAGE_PIN AA9 IOSTANDARD LVCMOS33} [get_ports tck]
set_property -dict {PACKAGE_PIN Y10 IOSTANDARD LVCMOS33} [get_ports tdi]
set_property -dict {PACKAGE_PIN AA11 IOSTANDARD LVCMOS33} [get_ports tdo]
set_property -dict {PACKAGE_PIN Y11 IOSTANDARD LVCMOS33} [get_ports tms]

## UART
set_property -dict {PACKAGE_PIN W8 IOSTANDARD LVCMOS33} [get_ports tx]
set_property -dict {PACKAGE_PIN V10 IOSTANDARD LVCMOS33} [get_ports rx]




## JTAG
# minimize routing delay

set_max_delay -to [get_ports tdo] 20.000
set_max_delay -from [get_ports tms] 20.000
set_max_delay -from [get_ports tdi] 20.000
set_max_delay -from [get_ports trst_n] 20.000

# reset signal
set_false_path -from [get_ports trst_n]


