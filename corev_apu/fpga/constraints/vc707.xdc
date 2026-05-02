## Buttons
set_property -dict {PACKAGE_PIN AV40 IOSTANDARD LVCMOS18} [get_ports cpu_reset]

## To use FTDI FT2232 JTAG
set_property -dict { PACKAGE_PIN AV39 IOSTANDARD LVCMOS18 } [get_ports trst];
set_property -dict { PACKAGE_PIN M32 IOSTANDARD LVCMOS18 } [get_ports tck ];
set_property -dict { PACKAGE_PIN V29 IOSTANDARD LVCMOS18 } [get_ports tdi ];
set_property -dict { PACKAGE_PIN M28 IOSTANDARD LVCMOS18 } [get_ports tdo ];
set_property -dict { PACKAGE_PIN U31 IOSTANDARD LVCMOS18 } [get_ports tms ];

## UART
set_property -dict {PACKAGE_PIN AU36 IOSTANDARD LVCMOS18} [get_ports tx]
set_property -dict {PACKAGE_PIN AU33 IOSTANDARD LVCMOS18} [get_ports rx]


## LEDs
set_property -dict {PACKAGE_PIN AM39 IOSTANDARD LVCMOS18} [get_ports {led[0]}]
set_property -dict {PACKAGE_PIN AN39 IOSTANDARD LVCMOS18} [get_ports {led[1]}]
set_property -dict {PACKAGE_PIN AR37 IOSTANDARD LVCMOS18} [get_ports {led[2]}]
set_property -dict {PACKAGE_PIN AT37 IOSTANDARD LVCMOS18} [get_ports {led[3]}]
set_property -dict {PACKAGE_PIN AR35 IOSTANDARD LVCMOS18} [get_ports {led[4]}]
set_property -dict {PACKAGE_PIN AP41 IOSTANDARD LVCMOS18} [get_ports {led[5]}]
set_property -dict {PACKAGE_PIN AP42 IOSTANDARD LVCMOS18} [get_ports {led[6]}]
set_property -dict {PACKAGE_PIN AU39 IOSTANDARD LVCMOS18} [get_ports {led[7]}]

## Switches
set_property -dict {PACKAGE_PIN AV30 IOSTANDARD LVCMOS18} [get_ports {sw[0]}]
set_property -dict {PACKAGE_PIN AY33 IOSTANDARD LVCMOS18} [get_ports {sw[1]}]
set_property -dict {PACKAGE_PIN BA31 IOSTANDARD LVCMOS18} [get_ports {sw[2]}]
set_property -dict {PACKAGE_PIN BA32 IOSTANDARD LVCMOS18} [get_ports {sw[3]}]
set_property -dict {PACKAGE_PIN AW30 IOSTANDARD LVCMOS18} [get_ports {sw[4]}]
set_property -dict {PACKAGE_PIN AY30 IOSTANDARD LVCMOS18} [get_ports {sw[5]}]
set_property -dict {PACKAGE_PIN BA30 IOSTANDARD LVCMOS18} [get_ports {sw[6]}]
set_property -dict {PACKAGE_PIN BB31 IOSTANDARD LVCMOS18} [get_ports {sw[7]}]

## Fan Control
set_property -dict {PACKAGE_PIN BA37 IOSTANDARD LVCMOS18} [get_ports fan_pwm]
#set_property -dict { PACKAGE_PIN V21   IOSTANDARD LVCMOS18 } [get_ports { FAN_TACH }]; #IO_L22P_T3_A05_D21_14 Sch=fan_tac

## SGMII Ethernet (Marvell 88E1111 PHY)
## 125 MHz SGMII clock from 88E1111 to MGTREFCLK0 on bank 117
set_property PACKAGE_PIN AH8 [get_ports sgmii_refclk_p]
set_property PACKAGE_PIN AH7 [get_ports sgmii_refclk_n]
create_clock -period 8.000 -name sgmii_refclk [get_ports sgmii_refclk_p]

## SGMII serial data (GTX in bank 117)
set_property PACKAGE_PIN AN2 [get_ports sgmii_txp]
set_property PACKAGE_PIN AN1 [get_ports sgmii_txn]
set_property PACKAGE_PIN AM8 [get_ports sgmii_rxp]
set_property PACKAGE_PIN AM7 [get_ports sgmii_rxn]

## PHY reset
set_property -dict {PACKAGE_PIN AJ33 IOSTANDARD LVCMOS18} [get_ports eth_rst_n]
set_false_path -to [get_ports eth_rst_n]

## MDIO interface
set_property -dict {PACKAGE_PIN AH33 IOSTANDARD LVCMOS18} [get_ports eth_mdc]
set_property -dict {PACKAGE_PIN AK33 IOSTANDARD LVCMOS18} [get_ports eth_mdio]
set_false_path -to [get_ports eth_mdc]

## CDC: GTX userclk2 (62.5 MHz) is async to sys_clk (50 MHz)
set_clock_groups -asynchronous -group [get_clocks -include_generated_clocks sgmii_refclk]

#############################################
## SD Card
#############################################
set_property -dict {PACKAGE_PIN AN30 IOSTANDARD LVCMOS18} [get_ports spi_clk_o]
set_property -dict {PACKAGE_PIN AT30 IOSTANDARD LVCMOS18} [get_ports spi_ss]
set_property -dict {PACKAGE_PIN AR30 IOSTANDARD LVCMOS18} [get_ports spi_miso]
set_property -dict {PACKAGE_PIN AP30 IOSTANDARD LVCMOS18} [get_ports spi_mosi]
# set_property -dict { PACKAGE_PIN P28   IOSTANDARD LVCMOS18 } [get_ports { sd_cd }]; #IO_L8N_T1_D12_14 Sch=sd_cd
# set_property -dict { PACKAGE_PIN R29   IOSTANDARD LVCMOS18 } [get_ports { sd_cmd }]; #IO_L7N_T1_D10_14 Sch=sd_cmd
# set_property -dict { PACKAGE_PIN R26   IOSTANDARD LVCMOS18 } [get_ports { sd_dat[0] }]; #IO_L10N_T1_D15_14 Sch=sd_dat[0]
# set_property -dict { PACKAGE_PIN R30   IOSTANDARD LVCMOS18 } [get_ports { sd_dat[1] }]; #IO_L9P_T1_DQS_14 Sch=sd_dat[1]
# set_property -dict { PACKAGE_PIN P29   IOSTANDARD LVCMOS18 } [get_ports { sd_dat[2] }]; #IO_L7P_T1_D09_14 Sch=sd_dat[2]
# set_property -dict { PACKAGE_PIN T30   IOSTANDARD LVCMOS18 } [get_ports { sd_dat[3] }]; #IO_L9N_T1_DQS_D13_14 Sch=sd_dat[3]
# set_property -dict { PACKAGE_PIN AE24  IOSTANDARD LVCMOS18 } [get_ports { sd_reset }]; #IO_L12N_T1_MRCC_12 Sch=sd_reset
# set_property -dict { PACKAGE_PIN R28   IOSTANDARD LVCMOS18 } [get_ports { sd_clk }]; #IO_L11P_T1_SRCC_14 Sch=sd_sclk

# create_generated_clock -name sd_fast_clk -source [get_pins clk_mmcm/sd_sys_clk] -divide_by 2 [get_pins chipset_impl/piton_sd_top/sdc_controller/clock_divider0/fast_clk_reg/Q]
# create_generated_clock -name sd_slow_clk -source [get_pins clk_mmcm/sd_sys_clk] -divide_by 200 [get_pins chipset_impl/piton_sd_top/sdc_controller/clock_divider0/slow_clk_reg/Q]
# create_generated_clock -name sd_clk_out -source [get_pins sd_clk_oddr/C] -divide_by 1 -add -master_clock sd_fast_clk [get_ports sd_clk_out]
# create_generated_clock -name sd_clk_out_1 -source [get_pins sd_clk_oddr/C] -divide_by 1 -add -master_clock sd_slow_clk [get_ports sd_clk_out]

# create_clock -period 40.000 -name VIRTUAL_sd_fast_clk -waveform {0.000 20.000}
# create_clock -period 4000.000 -name VIRTUAL_sd_slow_clk -waveform {0.000 2000.000}

# set_output_delay -clock [get_clocks sd_clk_out] -min -add_delay 5.000 [get_ports {sd_dat[*]}]
# set_output_delay -clock [get_clocks sd_clk_out] -max -add_delay 15.000 [get_ports {sd_dat[*]}]
# set_output_delay -clock [get_clocks sd_clk_out_1] -min -add_delay 5.000 [get_ports {sd_dat[*]}]
# set_output_delay -clock [get_clocks sd_clk_out_1] -max -add_delay 1500.000 [get_ports {sd_dat[*]}]
# set_output_delay -clock [get_clocks sd_clk_out] -min -add_delay 5.000 [get_ports sd_cmd]
# set_output_delay -clock [get_clocks sd_clk_out] -max -add_delay 15.000 [get_ports sd_cmd]
# set_output_delay -clock [get_clocks sd_clk_out_1] -min -add_delay 5.000 [get_ports sd_cmd]
# set_output_delay -clock [get_clocks sd_clk_out_1] -max -add_delay 1500.000 [get_ports sd_cmd]
# set_input_delay -clock [get_clocks VIRTUAL_sd_fast_clk] -min -add_delay 20.000 [get_ports {sd_dat[*]}]
# set_input_delay -clock [get_clocks VIRTUAL_sd_fast_clk] -max -add_delay 35.000 [get_ports {sd_dat[*]}]
# set_input_delay -clock [get_clocks VIRTUAL_sd_slow_clk] -min -add_delay 2000.000 [get_ports {sd_dat[*]}]
# set_input_delay -clock [get_clocks VIRTUAL_sd_slow_clk] -max -add_delay 3500.000 [get_ports {sd_dat[*]}]
# set_input_delay -clock [get_clocks VIRTUAL_sd_fast_clk] -min -add_delay 20.000 [get_ports sd_cmd]
# set_input_delay -clock [get_clocks VIRTUAL_sd_fast_clk] -max -add_delay 35.000 [get_ports sd_cmd]
# set_input_delay -clock [get_clocks VIRTUAL_sd_slow_clk] -min -add_delay 2000.000 [get_ports sd_cmd]
# set_input_delay -clock [get_clocks VIRTUAL_sd_slow_clk] -max -add_delay 3500.000 [get_ports sd_cmd]
# set_clock_groups -physically_exclusive -group [get_clocks -include_generated_clocks sd_clk_out] -group [get_clocks -include_generated_clocks sd_clk_out_1]
# set_clock_groups -logically_exclusive -group [get_clocks -include_generated_clocks {VIRTUAL_sd_fast_clk sd_fast_clk}] -group [get_clocks -include_generated_clocks {sd_slow_clk VIRTUAL_sd_slow_clk}]
# set_clock_groups -asynchronous -group [get_clocks [list [get_clocks -of_objects [get_pins clk_mmcm/chipset_clk]]]] -group [get_clocks -filter { NAME =~  "*sd*" }]


# Genesys 2 has a quad SPI flash
# set_property BITSTREAM.CONFIG.SPI_BUSWIDTH 4 [current_design]

## JTAG
# minimize routing delay

set_max_delay -to   [get_ports tdo ] 20
set_max_delay -from [get_ports tms ] 20
set_max_delay -from [get_ports tdi ] 20
set_max_delay -from [get_ports trst ] 20

# reset signal
# set_false_path -from [get_ports { trst } ]
# set_false_path -from [get_pins i_ddr/u_xlnx_mig_7_ddr3_mig/u_ddr3_infrastructure/rstdiv0_sync_r1_reg_rep/C]

# Configuration bank voltage
set_property CFGBVS GND [current_design]
set_property CONFIG_VOLTAGE 1.8 [current_design]
