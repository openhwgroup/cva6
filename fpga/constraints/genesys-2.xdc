## Buttons
set_property -dict {PACKAGE_PIN R19 IOSTANDARD LVCMOS33} [get_ports cpu_resetn]

## PMOD Header JC
set_property -dict {PACKAGE_PIN AC26 IOSTANDARD LVCMOS33} [get_ports tck]
set_property -dict {PACKAGE_PIN AJ27 IOSTANDARD LVCMOS33} [get_ports tdi]
set_property -dict {PACKAGE_PIN AH30 IOSTANDARD LVCMOS33} [get_ports tdo]
set_property -dict {PACKAGE_PIN AK29 IOSTANDARD LVCMOS33} [get_ports tms]
set_property -dict {PACKAGE_PIN AD26 IOSTANDARD LVCMOS33} [get_ports trst_n]

## UART
set_property -dict {PACKAGE_PIN Y23 IOSTANDARD LVCMOS33} [get_ports tx]
set_property -dict {PACKAGE_PIN Y20 IOSTANDARD LVCMOS33} [get_ports rx]

# accept sub-optimal placement
set_property CLOCK_DEDICATED_ROUTE FALSE [get_nets tck_IBUF]

## LEDs
set_property -dict {PACKAGE_PIN T28 IOSTANDARD LVCMOS33} [get_ports {led[0]}]
set_property -dict {PACKAGE_PIN V19 IOSTANDARD LVCMOS33} [get_ports {led[1]}]
set_property -dict {PACKAGE_PIN U30 IOSTANDARD LVCMOS33} [get_ports {led[2]}]
set_property -dict {PACKAGE_PIN U29 IOSTANDARD LVCMOS33} [get_ports {led[3]}]
set_property -dict {PACKAGE_PIN V20 IOSTANDARD LVCMOS33} [get_ports {led[4]}]
set_property -dict {PACKAGE_PIN V26 IOSTANDARD LVCMOS33} [get_ports {led[5]}]
set_property -dict {PACKAGE_PIN W24 IOSTANDARD LVCMOS33} [get_ports {led[6]}]
set_property -dict {PACKAGE_PIN W23 IOSTANDARD LVCMOS33} [get_ports {led[7]}]

## Switches
set_property -dict { PACKAGE_PIN G19   IOSTANDARD LVCMOS12 } [get_ports { sw[0] }]; #IO_0_17 Sch=sw[0]
set_property -dict { PACKAGE_PIN G25   IOSTANDARD LVCMOS12 } [get_ports { sw[1] }]; #IO_25_16 Sch=sw[1]
set_property -dict { PACKAGE_PIN H24   IOSTANDARD LVCMOS12 } [get_ports { sw[2] }]; #IO_L19P_T3_16 Sch=sw[2]
set_property -dict { PACKAGE_PIN K19   IOSTANDARD LVCMOS12 } [get_ports { sw[3] }]; #IO_L6P_T0_17 Sch=sw[3]
set_property -dict { PACKAGE_PIN N19   IOSTANDARD LVCMOS12 } [get_ports { sw[4] }]; #IO_L19P_T3_A22_15 Sch=sw[4]
set_property -dict { PACKAGE_PIN P19   IOSTANDARD LVCMOS12 } [get_ports { sw[5] }]; #IO_25_15 Sch=sw[5]
set_property -dict { PACKAGE_PIN P26   IOSTANDARD LVCMOS33 } [get_ports { sw[6] }]; #IO_L10P_T1_D14_14 Sch=sw[6]
set_property -dict { PACKAGE_PIN P27   IOSTANDARD LVCMOS33 } [get_ports { sw[7] }]; #IO_L8P_T1_D11_14 Sch=sw[7]

## Fan Control
set_property -dict { PACKAGE_PIN W19   IOSTANDARD LVCMOS33 } [get_ports { fan_pwm }]; #IO_25_14 Sch=fan_pwm
#set_property -dict { PACKAGE_PIN V21   IOSTANDARD LVCMOS33 } [get_ports { FAN_TACH }]; #IO_L22P_T3_A05_D21_14 Sch=fan_tac