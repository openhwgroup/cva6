# on board single-end clock, 100MHz
set_property PACKAGE_PIN E3 [get_ports clk_p]
set_property IOSTANDARD LVCMOS33 [get_ports clk_p]

# Reset active high SW4.1 User button South
set_property IOSTANDARD LVCMOS33 [get_ports rst_top]
set_property PACKAGE_PIN C12 [get_ports rst_top]

# UART Pins

# SD/SPI Pins
#set_property PACKAGE_PIN D2 [get_ports spi_cs]
#set_property IOSTANDARD LVCMOS33 [get_ports spi_cs]
#set_property PACKAGE_PIN B1 [get_ports spi_sclk]
#set_property IOSTANDARD LVCMOS33 [get_ports spi_sclk]
#set_property PACKAGE_PIN C1 [get_ports spi_mosi]
#set_property IOSTANDARD LVCMOS33 [get_ports spi_mosi]
#set_property PACKAGE_PIN C2 [get_ports spi_miso]
#set_property IOSTANDARD LVCMOS33 [get_ports spi_miso]
#set_property PACKAGE_PIN E2 [get_ports sd_reset]
#set_property IOSTANDARD LVCMOS33 [get_ports sd_reset]
#set_property IOSTANDARD LVCMOS33 [get_ports sd_sclk]
#set_property IOSTANDARD LVCMOS33 [get_ports sd_cmd]
#set_property IOSTANDARD LVCMOS33 [get_ports {sd_dat[0]}]
#set_property IOSTANDARD LVCMOS33 [get_ports {sd_dat[1]}]
#set_property IOSTANDARD LVCMOS33 [get_ports {sd_dat[2]}]
#set_property IOSTANDARD LVCMOS33 [get_ports {sd_dat[3]}]

#Buttons

#VGA Connector





#USB HID (PS/2)


# Flash/SPI Pins
#set_property PACKAGE_PIN L13 [get_ports flash_ss]
#set_property IOSTANDARD LVCMOS33 [get_ports flash_ss]
#set_property PACKAGE_PIN K17 [get_ports {flash_io[0]}]
#set_property IOSTANDARD LVCMOS33 [get_ports {flash_io[0]}]
#set_property PACKAGE_PIN K18 [get_ports {flash_io[1]}]
#set_property IOSTANDARD LVCMOS33 [get_ports {flash_io[1]}]
#set_property PACKAGE_PIN L14 [get_ports {flash_io[2]}]
#set_property IOSTANDARD LVCMOS33 [get_ports {flash_io[2]}]
#set_property PACKAGE_PIN M14 [get_ports {flash_io[3]}]
#set_property IOSTANDARD LVCMOS33 [get_ports {flash_io[3]}]
#
set_property PACKAGE_PIN H17 [get_ports {o_led[0]}]
set_property IOSTANDARD LVCMOS33 [get_ports {o_led[0]}]
set_property PACKAGE_PIN K15 [get_ports {o_led[1]}]
set_property IOSTANDARD LVCMOS33 [get_ports {o_led[1]}]
set_property PACKAGE_PIN J13 [get_ports {o_led[2]}]
set_property IOSTANDARD LVCMOS33 [get_ports {o_led[2]}]
set_property PACKAGE_PIN N14 [get_ports {o_led[3]}]
set_property IOSTANDARD LVCMOS33 [get_ports {o_led[3]}]
set_property PACKAGE_PIN R18 [get_ports {o_led[4]}]
set_property IOSTANDARD LVCMOS33 [get_ports {o_led[4]}]
set_property PACKAGE_PIN V17 [get_ports {o_led[5]}]
set_property IOSTANDARD LVCMOS33 [get_ports {o_led[5]}]
set_property PACKAGE_PIN U17 [get_ports {o_led[6]}]
set_property IOSTANDARD LVCMOS33 [get_ports {o_led[6]}]
set_property PACKAGE_PIN U16 [get_ports {o_led[7]}]
set_property IOSTANDARD LVCMOS33 [get_ports {o_led[7]}]
set_property PACKAGE_PIN V16 [get_ports {o_led[8]}]
set_property IOSTANDARD LVCMOS33 [get_ports {o_led[8]}]
set_property PACKAGE_PIN T15 [get_ports {o_led[9]}]
set_property IOSTANDARD LVCMOS33 [get_ports {o_led[9]}]
set_property PACKAGE_PIN U14 [get_ports {o_led[10]}]
set_property IOSTANDARD LVCMOS33 [get_ports {o_led[10]}]
set_property PACKAGE_PIN T16 [get_ports {o_led[11]}]
set_property IOSTANDARD LVCMOS33 [get_ports {o_led[11]}]
set_property PACKAGE_PIN V15 [get_ports {o_led[12]}]
set_property IOSTANDARD LVCMOS33 [get_ports {o_led[12]}]
set_property PACKAGE_PIN V14 [get_ports {o_led[13]}]
set_property IOSTANDARD LVCMOS33 [get_ports {o_led[13]}]
set_property PACKAGE_PIN V12 [get_ports {o_led[14]}]
set_property IOSTANDARD LVCMOS33 [get_ports {o_led[14]}]
set_property PACKAGE_PIN V11 [get_ports {o_led[15]}]
set_property IOSTANDARD LVCMOS33 [get_ports {o_led[15]}]
## Switches
set_property PACKAGE_PIN J15 [get_ports {i_dip[0]}]
set_property IOSTANDARD LVCMOS33 [get_ports {i_dip[0]}]
set_property PACKAGE_PIN L16 [get_ports {i_dip[1]}]
set_property IOSTANDARD LVCMOS33 [get_ports {i_dip[1]}]
set_property PACKAGE_PIN M13 [get_ports {i_dip[2]}]
set_property IOSTANDARD LVCMOS33 [get_ports {i_dip[2]}]
set_property PACKAGE_PIN R15 [get_ports {i_dip[3]}]
set_property IOSTANDARD LVCMOS33 [get_ports {i_dip[3]}]
set_property PACKAGE_PIN R17 [get_ports {i_dip[4]}]
set_property IOSTANDARD LVCMOS33 [get_ports {i_dip[4]}]
set_property PACKAGE_PIN T18 [get_ports {i_dip[5]}]
set_property IOSTANDARD LVCMOS33 [get_ports {i_dip[5]}]
set_property PACKAGE_PIN U18 [get_ports {i_dip[6]}]
set_property IOSTANDARD LVCMOS33 [get_ports {i_dip[6]}]
set_property PACKAGE_PIN R13 [get_ports {i_dip[7]}]
set_property IOSTANDARD LVCMOS33 [get_ports {i_dip[7]}]
## SW8 and SW9 are in the same bank of the DDR2 interface, which requires 1.8 V
set_property PACKAGE_PIN T8 [get_ports {i_dip[8]}]
set_property IOSTANDARD LVCMOS18 [get_ports {i_dip[8]}]
set_property PACKAGE_PIN U8 [get_ports {i_dip[9]}]
set_property IOSTANDARD LVCMOS18 [get_ports {i_dip[9]}]
set_property PACKAGE_PIN R16 [get_ports {i_dip[10]}]
set_property IOSTANDARD LVCMOS33 [get_ports {i_dip[10]}]
set_property PACKAGE_PIN T13 [get_ports {i_dip[11]}]
set_property IOSTANDARD LVCMOS33 [get_ports {i_dip[11]}]
set_property PACKAGE_PIN H6 [get_ports {i_dip[12]}]
set_property IOSTANDARD LVCMOS33 [get_ports {i_dip[12]}]
set_property PACKAGE_PIN U12 [get_ports {i_dip[13]}]
set_property IOSTANDARD LVCMOS33 [get_ports {i_dip[13]}]
set_property PACKAGE_PIN U11 [get_ports {i_dip[14]}]
set_property IOSTANDARD LVCMOS33 [get_ports {i_dip[14]}]
set_property PACKAGE_PIN V10 [get_ports {i_dip[15]}]
set_property IOSTANDARD LVCMOS33 [get_ports {i_dip[15]}]

##SMSC Ethernet PHY

set_property CONFIG_MODE SPIx4 [current_design]
set_property BITSTREAM.CONFIG.SPI_BUSWIDTH 4 [current_design]

