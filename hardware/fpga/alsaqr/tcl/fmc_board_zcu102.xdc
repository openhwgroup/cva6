#############################################################
#  _____ ____         _____      _   _   _                  #
# |_   _/ __ \       / ____|    | | | | (_)                 #
#   | || |  | |_____| (___   ___| |_| |_ _ _ __   __ _ ___  #
#   | || |  | |______\___ \ / _ \ __| __| | '_ \ / _` / __| #
#  _| || |__| |      ____) |  __/ |_| |_| | | | | (_| \__ \ #
# |_____\____/      |_____/ \___|\__|\__|_|_| |_|\__, |___/ #
#                                                 __/ |     #
#                                                |___/      #
#############################################################

## Sys clock
set_property -dict {PACKAGE_PIN F21 IOSTANDARD LVDS_25} [get_ports ref_clk_n]
set_property -dict {PACKAGE_PIN G21 IOSTANDARD LVDS_25} [get_ports ref_clk_p]

## Reset
######################################################################
# Reset mapping
######################################################################
set_property -dict {PACKAGE_PIN AM13 IOSTANDARD LVCMOS33} [get_ports pad_reset]

## PMOD 0   --- JTAG
######################################################################
# JTAG mapping
######################################################################
set_property -dict {PACKAGE_PIN A20 IOSTANDARD LVCMOS33} [get_ports pad_jtag_tms]
set_property -dict {PACKAGE_PIN B20 IOSTANDARD LVCMOS33} [get_ports pad_jtag_tdi]
set_property -dict {PACKAGE_PIN A22 IOSTANDARD LVCMOS33} [get_ports pad_jtag_tdo]
set_property -dict {PACKAGE_PIN A21 IOSTANDARD LVCMOS33} [get_ports pad_jtag_tck]
set_property -dict {PACKAGE_PIN B21 IOSTANDARD LVCMOS33} [get_ports pad_jtag_trst]


## UART
######################################################################
# UART mapping
######################################################################
set_property -dict {PACKAGE_PIN E13 IOSTANDARD LVCMOS33} [get_ports pad_uart_rx]
set_property -dict {PACKAGE_PIN F13 IOSTANDARD LVCMOS33} [get_ports pad_uart_tx]

####################################################################
# Hyper Bus
####################################################################

set_property -dict {PACKAGE_PIN M14 IOSTANDARD LVCMOS18}  [get_ports FMC_hyper_csn0]
set_property -dict {PACKAGE_PIN M15 IOSTANDARD LVCMOS18}  [get_ports FMC_hyper_csn1]
set_property -dict {PACKAGE_PIN AB4 IOSTANDARD LVCMOS18}  [get_ports FMC_hyper_ck]
set_property -dict {PACKAGE_PIN AC4 IOSTANDARD LVCMOS18}  [get_ports FMC_hyper_ckn]
set_property -dict {PACKAGE_PIN AB8 IOSTANDARD LVCMOS18}  [get_ports FMC_hyper_rwds0]
set_property -dict {PACKAGE_PIN AB3 IOSTANDARD LVCMOS18}  [get_ports FMC_hyper_dqio0]
set_property -dict {PACKAGE_PIN AC3 IOSTANDARD LVCMOS18}  [get_ports FMC_hyper_dqio1]
set_property -dict {PACKAGE_PIN W2 IOSTANDARD LVCMOS18}   [get_ports FMC_hyper_dqio2]
set_property -dict {PACKAGE_PIN W1 IOSTANDARD LVCMOS18}   [get_ports FMC_hyper_dqio3]
set_property -dict {PACKAGE_PIN Y12 IOSTANDARD LVCMOS18}  [get_ports FMC_hyper_dqio4]
set_property -dict {PACKAGE_PIN AA12 IOSTANDARD LVCMOS18} [get_ports FMC_hyper_dqio5]
set_property -dict {PACKAGE_PIN N13 IOSTANDARD LVCMOS18}  [get_ports FMC_hyper_dqio6]
set_property -dict {PACKAGE_PIN M13 IOSTANDARD LVCMOS18}  [get_ports FMC_hyper_dqio7]
set_property -dict {PACKAGE_PIN M11 IOSTANDARD LVCMOS18}  [get_ports FMC_hyper_reset]
