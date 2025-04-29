############################################################################
### VCU118 Rev2.0 XDC 12/08/2017
############################################################################

##general settings
# some constraints from the example design
set_property BITSTREAM.CONFIG.EXTMASTERCCLK_EN div-1 [current_design]
set_property BITSTREAM.CONFIG.BPI_SYNC_MODE Type1 [current_design]
set_property BITSTREAM.GENERAL.COMPRESS TRUE [current_design]
set_property CFGBVS GND [current_design]
set_property CONFIG_VOLTAGE 1.8 [current_design]
set_property CONFIG_MODE BPI16 [current_design]

##Reset
set_property -dict {PACKAGE_PIN L19 IOSTANDARD LVCMOS12} [get_ports cpu_reset]

##Clocks
#250 MHz Systemclock 1
set_property PACKAGE_PIN E12 [get_ports c0_sys_clk_p]
set_property PACKAGE_PIN D12 [get_ports c0_sys_clk_n]
set_property IOSTANDARD DIFF_SSTL12 [get_ports -filter NAME=~c0_sys_clk_*]
create_clock -period 4.000 [get_ports c0_sys_clk_p]

##switches
#set_property PACKAGE_PIN B17 [get_ports {sw[0]}]
#set_property PACKAGE_PIN G16  [get_ports {sw[1]}]
#set_property PACKAGE_PIN J16  [get_ports {sw[2]}]
#set_property PACKAGE_PIN D21  [get_ports {sw[3]}]

#set_property IOSTANDARD LVCMOS12 [get_ports -filter NAME=~sw*]
#set_false_path -from [get_ports -filter NAME=~sw*]

##LEDs
#set_property PACKAGE_PIN AT32 [get_ports {led[0]}]
#set_property PACKAGE_PIN AV34 [get_ports {led[1]}]
#set_property PACKAGE_PIN AY30 [get_ports {led[2]}]
#set_property PACKAGE_PIN BB32 [get_ports {led[3]}]
#set_property PACKAGE_PIN BF32 [get_ports {led[4]}]
#set_property PACKAGE_PIN AV36 [get_ports {led[5]}]
#set_property PACKAGE_PIN AY35 [get_ports {led[6]}]
#set_property PACKAGE_PIN BA37 [get_ports {led[7]}]

#set_property IOSTANDARD LVCMOS12 [get_ports -filter NAME=~led*]
#set_false_path -to [get_ports -filter NAME=~led*]

# JTAG
set_property -dict {PACKAGE_PIN AY13 IOSTANDARD LVCMOS18} [get_ports tck]
set_property -dict {PACKAGE_PIN AV11 IOSTANDARD LVCMOS18} [get_ports tdi]
set_property -dict {PACKAGE_PIN AW13 IOSTANDARD LVCMOS18} [get_ports tdo]
set_property -dict {PACKAGE_PIN AU11 IOSTANDARD LVCMOS18} [get_ports tms]
set_property -dict {PACKAGE_PIN AP13 IOSTANDARD LVCMOS18} [get_ports trst_n]

# Contrainte pour connecter un port à la masse (GND)
set_property -dict { PACKAGE_PIN AN16 IOSTANDARD LVCMOS18 } [get_ports { gnd_jtag }]

# Contrainte pour connecter un port à l'alimentation (VCC)
set_property -dict { PACKAGE_PIN AP16 IOSTANDARD LVCMOS18 } [get_ports { vcc_jtag }]
set_property -dict { PACKAGE_PIN AR13 IOSTANDARD LVCMOS18 } [get_ports { vcc_reset_jtag }]

# accept sub-optimal placement
set_property CLOCK_DEDICATED_ROUTE FALSE [get_nets tck_IBUF_inst/O]


#JTAG Clock
create_clock -period 100.000 -name tck -waveform {0.000 50.000} [get_ports tck]
set_input_jitter tck 1.000

#set JTAG reset as false path
set_false_path -from [get_ports trst_n]


#set DDR reset as false path
set_false_path -from [get_pins i_ddr/inst/div_clk_rst_r1_reg/C]

#RAM Calibration
#set_property C_CLK_INPUT_FREQ_HZ    300000000   [get_debug_cores dbg_hub]
#set_property C_ENABLE_CLK_DIVIDER   false       [get_debug_cores dbg_hub]
#set_property C_USER_SCAN_CHAIN      1           [get_debug_cores dbg_hub]
#connect_debug_port dbg_hub/clk [get_nets clk_1]

##SD CARD
set_property -dict {PACKAGE_PIN AV15 IOSTANDARD LVCMOS18} [get_ports spi_clk_o]
set_property -dict {PACKAGE_PIN AY14 IOSTANDARD LVCMOS18} [get_ports spi_ss]
set_property -dict {PACKAGE_PIN AW15 IOSTANDARD LVCMOS18} [get_ports spi_miso]
set_property -dict {PACKAGE_PIN AW15 IOSTANDARD  LVCMOS18} [get_ports spi_miso]
set_property -dict {PACKAGE_PIN AY15 IOSTANDARD LVCMOS18} [get_ports spi_mosi]
#set_property IOSTANDARD LVCMOS18 [get_ports -filter NAME=~spi_*]

#### UART
set_property -dict {PACKAGE_PIN AW25 IOSTANDARD LVCMOS18} [get_ports rx]
set_property -dict {PACKAGE_PIN BB21 IOSTANDARD LVCMOS18} [get_ports tx]




#set_property -dict {PACKAGE_PIN AV34 IOSTANDARD LVCMOS12 } [get_ports {c0_init_calib_complete}]; # LED0
set_property PACKAGE_PIN E13 [get_ports c0_ddr4_act_n]
set_property PACKAGE_PIN D14 [get_ports {c0_ddr4_adr[0]}]
set_property PACKAGE_PIN C12 [get_ports {c0_ddr4_adr[10]}]
set_property PACKAGE_PIN B13 [get_ports {c0_ddr4_adr[11]}]
set_property PACKAGE_PIN C13 [get_ports {c0_ddr4_adr[12]}]
set_property PACKAGE_PIN D15 [get_ports {c0_ddr4_adr[13]}]
set_property PACKAGE_PIN H14 [get_ports {c0_ddr4_adr[14]}]
set_property PACKAGE_PIN H15 [get_ports {c0_ddr4_adr[15]}]
set_property PACKAGE_PIN F15 [get_ports {c0_ddr4_adr[16]}]
set_property PACKAGE_PIN B15 [get_ports {c0_ddr4_adr[1]}]
set_property PACKAGE_PIN B16 [get_ports {c0_ddr4_adr[2]}]
set_property PACKAGE_PIN C14 [get_ports {c0_ddr4_adr[3]}]
set_property PACKAGE_PIN C15 [get_ports {c0_ddr4_adr[4]}]
set_property PACKAGE_PIN A13 [get_ports {c0_ddr4_adr[5]}]
set_property PACKAGE_PIN A14 [get_ports {c0_ddr4_adr[6]}]
set_property PACKAGE_PIN A15 [get_ports {c0_ddr4_adr[7]}]
set_property PACKAGE_PIN A16 [get_ports {c0_ddr4_adr[8]}]
set_property PACKAGE_PIN B12 [get_ports {c0_ddr4_adr[9]}]
set_property PACKAGE_PIN G15 [get_ports {c0_ddr4_ba[0]}]
set_property PACKAGE_PIN G13 [get_ports {c0_ddr4_ba[1]}]
set_property PACKAGE_PIN H13 [get_ports {c0_ddr4_bg[0]}]
set_property PACKAGE_PIN F14 [get_ports {c0_ddr4_ck_t[0]}]
set_property PACKAGE_PIN E14 [get_ports {c0_ddr4_ck_c[0]}]
set_property PACKAGE_PIN A10 [get_ports {c0_ddr4_cke[0]}]
set_property PACKAGE_PIN F13 [get_ports {c0_ddr4_cs_n[0]}]
set_property PACKAGE_PIN G11 [get_ports {c0_ddr4_dm_dbi_n[0]}]
set_property PACKAGE_PIN R18 [get_ports {c0_ddr4_dm_dbi_n[1]}]
set_property PACKAGE_PIN K17 [get_ports {c0_ddr4_dm_dbi_n[2]}]
set_property PACKAGE_PIN G18 [get_ports {c0_ddr4_dm_dbi_n[3]}]
set_property PACKAGE_PIN B18 [get_ports {c0_ddr4_dm_dbi_n[4]}]
set_property PACKAGE_PIN P20 [get_ports {c0_ddr4_dm_dbi_n[5]}]
set_property PACKAGE_PIN L23 [get_ports {c0_ddr4_dm_dbi_n[6]}]
set_property PACKAGE_PIN G22 [get_ports {c0_ddr4_dm_dbi_n[7]}]

set_property PACKAGE_PIN F11 [get_ports {c0_ddr4_dq[0]}]
set_property PACKAGE_PIN M18 [get_ports {c0_ddr4_dq[10]}]
set_property PACKAGE_PIN M17 [get_ports {c0_ddr4_dq[11]}]
set_property PACKAGE_PIN N19 [get_ports {c0_ddr4_dq[12]}]
set_property PACKAGE_PIN N18 [get_ports {c0_ddr4_dq[13]}]
set_property PACKAGE_PIN N17 [get_ports {c0_ddr4_dq[14]}]
set_property PACKAGE_PIN M16 [get_ports {c0_ddr4_dq[15]}]
set_property PACKAGE_PIN L16 [get_ports {c0_ddr4_dq[16]}]
set_property PACKAGE_PIN K16 [get_ports {c0_ddr4_dq[17]}]
set_property PACKAGE_PIN L18 [get_ports {c0_ddr4_dq[18]}]
set_property PACKAGE_PIN K18 [get_ports {c0_ddr4_dq[19]}]
set_property PACKAGE_PIN E11 [get_ports {c0_ddr4_dq[1]}]
set_property PACKAGE_PIN J17 [get_ports {c0_ddr4_dq[20]}]
set_property PACKAGE_PIN H17 [get_ports {c0_ddr4_dq[21]}]
set_property PACKAGE_PIN H19 [get_ports {c0_ddr4_dq[22]}]
set_property PACKAGE_PIN H18 [get_ports {c0_ddr4_dq[23]}]
set_property PACKAGE_PIN F19 [get_ports {c0_ddr4_dq[24]}]
set_property PACKAGE_PIN F18 [get_ports {c0_ddr4_dq[25]}]
set_property PACKAGE_PIN E19 [get_ports {c0_ddr4_dq[26]}]
set_property PACKAGE_PIN E18 [get_ports {c0_ddr4_dq[27]}]
set_property PACKAGE_PIN G20 [get_ports {c0_ddr4_dq[28]}]
set_property PACKAGE_PIN F20 [get_ports {c0_ddr4_dq[29]}]
set_property PACKAGE_PIN F10 [get_ports {c0_ddr4_dq[2]}]
set_property PACKAGE_PIN E17 [get_ports {c0_ddr4_dq[30]}]
set_property PACKAGE_PIN D16 [get_ports {c0_ddr4_dq[31]}]
set_property PACKAGE_PIN D17 [get_ports {c0_ddr4_dq[32]}]
set_property PACKAGE_PIN C17 [get_ports {c0_ddr4_dq[33]}]
set_property PACKAGE_PIN C19 [get_ports {c0_ddr4_dq[34]}]
set_property PACKAGE_PIN C18 [get_ports {c0_ddr4_dq[35]}]
set_property PACKAGE_PIN D20 [get_ports {c0_ddr4_dq[36]}]
set_property PACKAGE_PIN D19 [get_ports {c0_ddr4_dq[37]}]
set_property PACKAGE_PIN C20 [get_ports {c0_ddr4_dq[38]}]
set_property PACKAGE_PIN B20 [get_ports {c0_ddr4_dq[39]}]
set_property PACKAGE_PIN F9 [get_ports {c0_ddr4_dq[3]}]
set_property PACKAGE_PIN N23 [get_ports {c0_ddr4_dq[40]}]
set_property PACKAGE_PIN M23 [get_ports {c0_ddr4_dq[41]}]
set_property PACKAGE_PIN R21 [get_ports {c0_ddr4_dq[42]}]
set_property PACKAGE_PIN P21 [get_ports {c0_ddr4_dq[43]}]
set_property PACKAGE_PIN R22 [get_ports {c0_ddr4_dq[44]}]
set_property PACKAGE_PIN P22 [get_ports {c0_ddr4_dq[45]}]
set_property PACKAGE_PIN T23 [get_ports {c0_ddr4_dq[46]}]
set_property PACKAGE_PIN R23 [get_ports {c0_ddr4_dq[47]}]
set_property PACKAGE_PIN K24 [get_ports {c0_ddr4_dq[48]}]
set_property PACKAGE_PIN J24 [get_ports {c0_ddr4_dq[49]}]
set_property PACKAGE_PIN H12 [get_ports {c0_ddr4_dq[4]}]
set_property PACKAGE_PIN M21 [get_ports {c0_ddr4_dq[50]}]
set_property PACKAGE_PIN L21 [get_ports {c0_ddr4_dq[51]}]
set_property PACKAGE_PIN K21 [get_ports {c0_ddr4_dq[52]}]
set_property PACKAGE_PIN J21 [get_ports {c0_ddr4_dq[53]}]
set_property PACKAGE_PIN K22 [get_ports {c0_ddr4_dq[54]}]
set_property PACKAGE_PIN J22 [get_ports {c0_ddr4_dq[55]}]
set_property PACKAGE_PIN H23 [get_ports {c0_ddr4_dq[56]}]
set_property PACKAGE_PIN H22 [get_ports {c0_ddr4_dq[57]}]
set_property PACKAGE_PIN E23 [get_ports {c0_ddr4_dq[58]}]
set_property PACKAGE_PIN E22 [get_ports {c0_ddr4_dq[59]}]
set_property PACKAGE_PIN G12 [get_ports {c0_ddr4_dq[5]}]
set_property PACKAGE_PIN F21 [get_ports {c0_ddr4_dq[60]}]
set_property PACKAGE_PIN E21 [get_ports {c0_ddr4_dq[61]}]
set_property PACKAGE_PIN F24 [get_ports {c0_ddr4_dq[62]}]
set_property PACKAGE_PIN F23 [get_ports {c0_ddr4_dq[63]}]

set_property PACKAGE_PIN E9 [get_ports {c0_ddr4_dq[6]}]
set_property PACKAGE_PIN D9 [get_ports {c0_ddr4_dq[7]}]
set_property PACKAGE_PIN R19 [get_ports {c0_ddr4_dq[8]}]
set_property PACKAGE_PIN P19 [get_ports {c0_ddr4_dq[9]}]

set_property PACKAGE_PIN D11 [get_ports {c0_ddr4_dqs_t[0]}]
set_property PACKAGE_PIN D10 [get_ports {c0_ddr4_dqs_c[0]}]
set_property PACKAGE_PIN P17 [get_ports {c0_ddr4_dqs_t[1]}]
set_property PACKAGE_PIN P16 [get_ports {c0_ddr4_dqs_c[1]}]
set_property PACKAGE_PIN K19 [get_ports {c0_ddr4_dqs_t[2]}]
set_property PACKAGE_PIN J19 [get_ports {c0_ddr4_dqs_c[2]}]
set_property PACKAGE_PIN F16 [get_ports {c0_ddr4_dqs_t[3]}]
set_property PACKAGE_PIN E16 [get_ports {c0_ddr4_dqs_c[3]}]
set_property PACKAGE_PIN A19 [get_ports {c0_ddr4_dqs_t[4]}]
set_property PACKAGE_PIN A18 [get_ports {c0_ddr4_dqs_c[4]}]
set_property PACKAGE_PIN N22 [get_ports {c0_ddr4_dqs_t[5]}]
set_property PACKAGE_PIN M22 [get_ports {c0_ddr4_dqs_c[5]}]
set_property PACKAGE_PIN M20 [get_ports {c0_ddr4_dqs_t[6]}]
set_property PACKAGE_PIN L20 [get_ports {c0_ddr4_dqs_c[6]}]
set_property PACKAGE_PIN H24 [get_ports {c0_ddr4_dqs_t[7]}]
set_property PACKAGE_PIN G23 [get_ports {c0_ddr4_dqs_c[7]}]

set_property PACKAGE_PIN C8 [get_ports {c0_ddr4_odt[0]}]
set_property PACKAGE_PIN N20 [get_ports c0_ddr4_reset_n]
