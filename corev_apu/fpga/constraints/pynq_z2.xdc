##################################################################################
## PYNQZ2 Master XDC                                                            ##
##################################################################################
## JTAG
# Controlled by PS (AXI-mapped)

## Clock
set_property -dict {PACKAGE_PIN H16  IOSTANDARD LVCMOS33} [get_ports sys_clock ];

## Reset -> btn0
set_property -dict {PACKAGE_PIN D19  IOSTANDARD LVCMOS33} [get_ports ext_reset ];

## UART (on PMOD A, lower connector)
# Not needed
#set_property -dict {PACKAGE_PIN U18  IOSTANDARD LVCMOS33} [get_ports uart_ctsn  ] # ~CTS -> ~RTS JA3_P
set_property -dict {PACKAGE_PIN U19  IOSTANDARD LVCMOS33} [get_ports uart_txd   ]; # module RXD -> FPGA TXD  JA3_N
set_property -dict {PACKAGE_PIN W18  IOSTANDARD LVCMOS33} [get_ports uart_rxd   ]; # module TXD -> FPGA RXD  JA4_P
# Also not needed
#set_property -dict {PACKAGE_PIN W19   IOSTANDARD LVCMOS33} [get_ports uart_rtsn  ] # ~RTS -> ~CTS JA4_N

## SD card
# SPI mode,
# Wired on PMODB
# Requires an adapter https://digilent.com/shop/pmod-microsd-microsd-card-slot/
set_property -dict {PACKAGE_PIN T10 IOSTANDARD LVCMOS33} [get_ports spi_clk_o ]; # Adapter Pin 4 -> JB2_N
set_property -dict {PACKAGE_PIN T11 IOSTANDARD LVCMOS33} [get_ports spi_miso ] ; # Adapter Pin 3 -> JB2_P
set_property -dict {PACKAGE_PIN Y14 IOSTANDARD LVCMOS33} [get_ports spi_mosi ] ; # Adapter Pin 2 -> JB1_N
set_property -dict {PACKAGE_PIN W14 IOSTANDARD LVCMOS33} [get_ports spi_ss ]   ; # Adapter Pin 1 -> JB1_P

### Switches
#set_property -dict {PACKAGE_PIN M20 IOSTANDARD LVCMOS33} [get_ports {sws_2bits_tri_i[0]}]
#set_property -dict {PACKAGE_PIN M19 IOSTANDARD LVCMOS33} [get_ports {sws_2bits_tri_i[1]}]
#
### Audio
#set_property -dict {PACKAGE_PIN U9 IOSTANDARD LVCMOS33} [get_ports IIC_1_scl_io]
#set_property PULLUP true [get_ports IIC_1_scl_io];
#set_property -dict {PACKAGE_PIN T9 IOSTANDARD LVCMOS33} [get_ports IIC_1_sda_io]
#set_property PULLUP true [get_ports IIC_1_sda_io];
#set_property -dict { PACKAGE_PIN U5   IOSTANDARD LVCMOS33 } [get_ports audio_clk_10MHz];
#set_property -dict { PACKAGE_PIN R18   IOSTANDARD LVCMOS33 } [get_ports bclk];
#set_property -dict { PACKAGE_PIN T17   IOSTANDARD LVCMOS33 } [get_ports lrclk];
#set_property -dict { PACKAGE_PIN G18   IOSTANDARD LVCMOS33 } [get_ports sdata_o];
#set_property -dict { PACKAGE_PIN F17   IOSTANDARD LVCMOS33 } [get_ports sdata_i];
#set_property -dict { PACKAGE_PIN M17   IOSTANDARD LVCMOS33 } [get_ports {codec_addr[0]}]
#set_property -dict { PACKAGE_PIN M18   IOSTANDARD LVCMOS33 } [get_ports {codec_addr[1]}]
#
### Buttons
#set_property -dict {PACKAGE_PIN D19 IOSTANDARD LVCMOS33} [get_ports {btns_4bits_tri_i[0]}]
#set_property -dict {PACKAGE_PIN D20 IOSTANDARD LVCMOS33} [get_ports {btns_4bits_tri_i[1]}]
#set_property -dict {PACKAGE_PIN L20 IOSTANDARD LVCMOS33} [get_ports {btns_4bits_tri_i[2]}]
#set_property -dict {PACKAGE_PIN L19 IOSTANDARD LVCMOS33} [get_ports {btns_4bits_tri_i[3]}]
#
### LEDs
#set_property -dict {PACKAGE_PIN R14 IOSTANDARD LVCMOS33} [get_ports {leds_4bits_tri_o[0]}]
#set_property -dict {PACKAGE_PIN P14 IOSTANDARD LVCMOS33} [get_ports {leds_4bits_tri_o[1]}]
#set_property -dict {PACKAGE_PIN N16 IOSTANDARD LVCMOS33} [get_ports {leds_4bits_tri_o[2]}]
#set_property -dict {PACKAGE_PIN M14 IOSTANDARD LVCMOS33} [get_ports {leds_4bits_tri_o[3]}]
#
### RGBLEDs
#set_property -dict { PACKAGE_PIN L15   IOSTANDARD LVCMOS33 } [get_ports { rgbleds_6bits_tri_o[0] }];
#set_property -dict { PACKAGE_PIN G17   IOSTANDARD LVCMOS33 } [get_ports { rgbleds_6bits_tri_o[1] }];
#set_property -dict { PACKAGE_PIN N15   IOSTANDARD LVCMOS33 } [get_ports { rgbleds_6bits_tri_o[2] }];
#set_property -dict { PACKAGE_PIN G14   IOSTANDARD LVCMOS33 } [get_ports { rgbleds_6bits_tri_o[3] }];
#set_property -dict { PACKAGE_PIN L14   IOSTANDARD LVCMOS33 } [get_ports { rgbleds_6bits_tri_o[4] }];
#set_property -dict { PACKAGE_PIN M15   IOSTANDARD LVCMOS33 } [get_ports { rgbleds_6bits_tri_o[5] }];
#
### Pmoda
### RPi GPIO 7-0 are shared with pmoda_rpi_gpio_tri_io[7:0]
#set_property -dict {PACKAGE_PIN Y19 IOSTANDARD LVCMOS33} [get_ports {pmoda_rpi_gpio_tri_io[1]}]
#set_property -dict {PACKAGE_PIN Y18 IOSTANDARD LVCMOS33} [get_ports {pmoda_rpi_gpio_tri_io[0]}]
#set_property -dict {PACKAGE_PIN Y17 IOSTANDARD LVCMOS33} [get_ports {pmoda_rpi_gpio_tri_io[3]}]
#set_property -dict {PACKAGE_PIN Y16 IOSTANDARD LVCMOS33} [get_ports {pmoda_rpi_gpio_tri_io[2]}]
#set_property -dict {PACKAGE_PIN U19 IOSTANDARD LVCMOS33} [get_ports {pmoda_rpi_gpio_tri_io[5]}]
#set_property -dict {PACKAGE_PIN U18 IOSTANDARD LVCMOS33} [get_ports {pmoda_rpi_gpio_tri_io[4]}]
#set_property -dict {PACKAGE_PIN W19 IOSTANDARD LVCMOS33} [get_ports {pmoda_rpi_gpio_tri_io[7]}]
#set_property -dict {PACKAGE_PIN W18 IOSTANDARD LVCMOS33} [get_ports {pmoda_rpi_gpio_tri_io[6]}]
#set_property PULLUP true [get_ports {pmoda_rpi_gpio_tri_io[2]}]
#set_property PULLUP true [get_ports {pmoda_rpi_gpio_tri_io[3]}]
#set_property PULLUP true [get_ports {pmoda_rpi_gpio_tri_io[6]}]
#set_property PULLUP true [get_ports {pmoda_rpi_gpio_tri_io[7]}]
#
### Pmodb
#set_property -dict {PACKAGE_PIN Y14 IOSTANDARD LVCMOS33} [get_ports {pmodb_gpio_tri_io[1]}]
#set_property -dict {PACKAGE_PIN W14 IOSTANDARD LVCMOS33} [get_ports {pmodb_gpio_tri_io[0]}]
#set_property -dict {PACKAGE_PIN T10 IOSTANDARD LVCMOS33} [get_ports {pmodb_gpio_tri_io[3]}]
#set_property -dict {PACKAGE_PIN T11 IOSTANDARD LVCMOS33} [get_ports {pmodb_gpio_tri_io[2]}]
#set_property -dict {PACKAGE_PIN W16 IOSTANDARD LVCMOS33} [get_ports {pmodb_gpio_tri_io[5]}]
#set_property -dict {PACKAGE_PIN V16 IOSTANDARD LVCMOS33} [get_ports {pmodb_gpio_tri_io[4]}]
#set_property -dict {PACKAGE_PIN W13 IOSTANDARD LVCMOS33} [get_ports {pmodb_gpio_tri_io[7]}]
#set_property -dict {PACKAGE_PIN V12 IOSTANDARD LVCMOS33} [get_ports {pmodb_gpio_tri_io[6]}]
#set_property PULLUP true [get_ports {pmodb_gpio_tri_io[2]}]
#set_property PULLUP true [get_ports {pmodb_gpio_tri_io[3]}]
#set_property PULLUP true [get_ports {pmodb_gpio_tri_io[6]}]
#set_property PULLUP true [get_ports {pmodb_gpio_tri_io[7]}]
#
### Arduino GPIO
#set_property -dict {PACKAGE_PIN T14 IOSTANDARD LVCMOS33} [get_ports {arduino_gpio_tri_io[0]}]
#set_property -dict {PACKAGE_PIN U12 IOSTANDARD LVCMOS33} [get_ports {arduino_gpio_tri_io[1]}]
#set_property -dict {PACKAGE_PIN U13 IOSTANDARD LVCMOS33} [get_ports {arduino_gpio_tri_io[2]}]
#set_property -dict {PACKAGE_PIN V13 IOSTANDARD LVCMOS33} [get_ports {arduino_gpio_tri_io[3]}]
#set_property -dict {PACKAGE_PIN V15 IOSTANDARD LVCMOS33} [get_ports {arduino_gpio_tri_io[4]}]
#set_property -dict {PACKAGE_PIN T15 IOSTANDARD LVCMOS33} [get_ports {arduino_gpio_tri_io[5]}]
#set_property -dict {PACKAGE_PIN R16 IOSTANDARD LVCMOS33} [get_ports {arduino_gpio_tri_io[6]}]
#set_property -dict {PACKAGE_PIN U17 IOSTANDARD LVCMOS33} [get_ports {arduino_gpio_tri_io[7]}]
#set_property -dict {PACKAGE_PIN V17 IOSTANDARD LVCMOS33} [get_ports {arduino_gpio_tri_io[8]}]
#set_property -dict {PACKAGE_PIN V18 IOSTANDARD LVCMOS33} [get_ports {arduino_gpio_tri_io[9]}]
#set_property -dict {PACKAGE_PIN T16 IOSTANDARD LVCMOS33} [get_ports {arduino_gpio_tri_io[10]}]
#set_property -dict {PACKAGE_PIN R17 IOSTANDARD LVCMOS33} [get_ports {arduino_gpio_tri_io[11]}]
#set_property -dict {PACKAGE_PIN P18 IOSTANDARD LVCMOS33} [get_ports {arduino_gpio_tri_io[12]}]
#set_property -dict {PACKAGE_PIN N17 IOSTANDARD LVCMOS33} [get_ports {arduino_gpio_tri_io[13]}]
#set_property -dict {PACKAGE_PIN Y11 IOSTANDARD LVCMOS33} [get_ports {arduino_gpio_tri_io[14]}]
#set_property -dict {PACKAGE_PIN Y12 IOSTANDARD LVCMOS33} [get_ports {arduino_gpio_tri_io[15]}]
#set_property -dict {PACKAGE_PIN W11 IOSTANDARD LVCMOS33} [get_ports {arduino_gpio_tri_io[16]}]
#set_property -dict {PACKAGE_PIN V11 IOSTANDARD LVCMOS33} [get_ports {arduino_gpio_tri_io[17]}]
#set_property -dict {PACKAGE_PIN T5  IOSTANDARD LVCMOS33} [get_ports {arduino_gpio_tri_io[18]}]
#set_property -dict {PACKAGE_PIN U10 IOSTANDARD LVCMOS33} [get_ports {arduino_gpio_tri_io[19]}]
#
### Arduino direct I2C
#set_property -dict {PACKAGE_PIN P15 IOSTANDARD LVCMOS33} [get_ports arduino_direct_iic_scl_io]
#set_property -dict {PACKAGE_PIN P16 IOSTANDARD LVCMOS33} [get_ports arduino_direct_iic_sda_io]
#set_property PULLUP true [get_ports arduino_direct_iic_scl_io]
#set_property PULLUP true [get_ports arduino_direct_iic_sda_io]
#
### Arduino direct SPI
#set_property -dict {PACKAGE_PIN W15 IOSTANDARD LVCMOS33} [get_ports arduino_direct_spi_io1_io]
#set_property -dict {PACKAGE_PIN T12 IOSTANDARD LVCMOS33} [get_ports arduino_direct_spi_io0_io]
#set_property -dict {PACKAGE_PIN H15 IOSTANDARD LVCMOS33} [get_ports arduino_direct_spi_sck_io]
#set_property -dict {PACKAGE_PIN F16 IOSTANDARD LVCMOS33} [get_ports arduino_direct_spi_ss_io]
#
### Arduino analog channels
#set_property -dict {PACKAGE_PIN D18 IOSTANDARD LVCMOS33} [get_ports Vaux1_v_n]
#set_property -dict {PACKAGE_PIN E17 IOSTANDARD LVCMOS33} [get_ports Vaux1_v_p]
#set_property -dict {PACKAGE_PIN E19 IOSTANDARD LVCMOS33} [get_ports Vaux9_v_n]
#set_property -dict {PACKAGE_PIN E18 IOSTANDARD LVCMOS33} [get_ports Vaux9_v_p]
#set_property -dict {PACKAGE_PIN J14 IOSTANDARD LVCMOS33} [get_ports Vaux6_v_n]
#set_property -dict {PACKAGE_PIN K14 IOSTANDARD LVCMOS33} [get_ports Vaux6_v_p]
#set_property -dict {PACKAGE_PIN J16 IOSTANDARD LVCMOS33} [get_ports Vaux15_v_n]
#set_property -dict {PACKAGE_PIN K16 IOSTANDARD LVCMOS33} [get_ports Vaux15_v_p]
#set_property -dict {PACKAGE_PIN H20 IOSTANDARD LVCMOS33} [get_ports Vaux5_v_n]
#set_property -dict {PACKAGE_PIN J20 IOSTANDARD LVCMOS33} [get_ports Vaux5_v_p]
#set_property -dict {PACKAGE_PIN G20 IOSTANDARD LVCMOS33} [get_ports Vaux13_v_n]
#set_property -dict {PACKAGE_PIN G19 IOSTANDARD LVCMOS33} [get_ports Vaux13_v_p]
#
### HDMI signals
#create_clock -period 8.334 -waveform {0.000 4.167} [get_ports hdmi_in_clk_p]
#
### HDMI RX
#set_property -dict {PACKAGE_PIN P19 IOSTANDARD TMDS_33} [get_ports hdmi_in_clk_n]
#set_property -dict {PACKAGE_PIN N18 IOSTANDARD TMDS_33} [get_ports hdmi_in_clk_p]
#set_property -dict {PACKAGE_PIN W20 IOSTANDARD TMDS_33} [get_ports {hdmi_in_data_n[0]}]
#set_property -dict {PACKAGE_PIN V20 IOSTANDARD TMDS_33} [get_ports {hdmi_in_data_p[0]}]
#set_property -dict {PACKAGE_PIN U20 IOSTANDARD TMDS_33} [get_ports {hdmi_in_data_n[1]}]
#set_property -dict {PACKAGE_PIN T20 IOSTANDARD TMDS_33} [get_ports {hdmi_in_data_p[1]}]
#set_property -dict {PACKAGE_PIN P20 IOSTANDARD TMDS_33} [get_ports {hdmi_in_data_n[2]}]
#set_property -dict {PACKAGE_PIN N20 IOSTANDARD TMDS_33} [get_ports {hdmi_in_data_p[2]}]
#set_property -dict {PACKAGE_PIN T19 IOSTANDARD LVCMOS33} [get_ports {hdmi_in_hpd[0]}]
#set_property -dict {PACKAGE_PIN U14 IOSTANDARD LVCMOS33} [get_ports hdmi_in_ddc_scl_io]
#set_property -dict {PACKAGE_PIN U15 IOSTANDARD LVCMOS33} [get_ports hdmi_in_ddc_sda_io]
#
### HDMI TX
#set_property -dict {PACKAGE_PIN L17 IOSTANDARD TMDS_33} [get_ports hdmi_out_clk_n]
#set_property -dict {PACKAGE_PIN L16 IOSTANDARD TMDS_33} [get_ports hdmi_out_clk_p]
#set_property -dict {PACKAGE_PIN K18 IOSTANDARD TMDS_33} [get_ports {hdmi_out_data_n[0]}]
#set_property -dict {PACKAGE_PIN K17 IOSTANDARD TMDS_33} [get_ports {hdmi_out_data_p[0]}]
#set_property -dict {PACKAGE_PIN J19 IOSTANDARD TMDS_33} [get_ports {hdmi_out_data_n[1]}]
#set_property -dict {PACKAGE_PIN K19 IOSTANDARD TMDS_33} [get_ports {hdmi_out_data_p[1]}]
#set_property -dict {PACKAGE_PIN H18 IOSTANDARD TMDS_33} [get_ports {hdmi_out_data_n[2]}]
#set_property -dict {PACKAGE_PIN J18 IOSTANDARD TMDS_33} [get_ports {hdmi_out_data_p[2]}]
#set_property -dict {PACKAGE_PIN R19 IOSTANDARD LVCMOS33} [get_ports {hdmi_out_hpd[0]}]
#
### Raspberry PI
###  RPI_IDE Pin#   |   RP Connector  | Schematic Name | Dual Functionality
###        1        |      3v3        |     NA
###        3        |      GPIO2      |     JA4_P      |    I2C1_SDA
###        5        |      GPIO3      |     JA4_N      |    I2C1_SCL
###        7        |      GPIO4      |     JA1_P      |    GCLK0
###        9        |      GROUND     |     NA
###        11       |      GPIO17     |     RP_IO17_R
###        13       |      GPIO27     |     RP_IO27_R
###        15       |      GPIO22     |     RP_IO22_R
###        17       |      3v3        |     NA
###        19       |      GPIO10     |     RP_IO10_R   |    SPIO0_MOSI
###        21       |      GPIO9      |     RP_IO09_R   |    SPIO0_MISO
###        23       |      GPIO11     |     RP_IO11_R   |    SPIO0_SCLK
###        25       |      GROUND     |     NA
###        27       |      GPIO0      |     JA2_P       |    I2C0_SDA ID EEPROM
###        29       |      GPIO5      |     JA1_N       |    GCLK1
###        31       |      GPIO6      |     JA3_P       |    GCLK2
###        33       |      GPIO13     |     RP_IO13_R   |    PWM1
###        35       |      GPIO19     |     RP_IO19_R   |    SPIO1_MISO
###        37       |      GPIO26     |     RP_IO26_R
###        39       |      GROUND     |     NA
#
###        2        |      5V         |     NA
###        4        |      5V         |     NA
###        6        |      GROUND     |     NA
###        8        |      GPIO14     |     RP_IO14_R   |    UART0_TXD
###        10       |      GPIO15     |     RP_IO15_R   |    UART0_RXD
###        12       |      GPIO18     |     RP_IO18_R   |    PCM_CLK
###        14       |      GROUND     |     NA
###        16       |      GPIO23     |     RP_IO23_R
###        18       |      GPIO24     |     RP_IO24_R
###        20       |      GROUND     |     NA
###        22       |      GPIO25     |     RP_IO25_R
###        24       |      GPIO8      |     RP_IO08_R   |    SPIO0_CE0_N
###        26       |      GPIO7      |     JA3_N       |    SPIO0_CE1_N
###        28       |      GPIO1      |     JA2_N       |    I2C0_SDC ID EEPROM
###        30       |      GROUND     |     NA
###        32       |      GPIO12     |     RP_IO12_R   |    PWM0
###        34       |      GROUND     |     NA
###        36       |      GPIO16     |     RP_IO16_R   |    SPIO1_CE2_N
###        38       |      GPIO20     |     RP_IO20_R   |    SPIO1_MOSI
###        40       |      GPIO21     |     RP_IO21_R   |    SPIO1_SCLK
### RPi GPIO 27-8 are mapped to rpi_gpio_tri_io[19:0]
#set_property -dict { PACKAGE_PIN F19   IOSTANDARD LVCMOS33 } [get_ports { rpi_gpio_tri_io[0]  }];
#set_property -dict { PACKAGE_PIN V10   IOSTANDARD LVCMOS33 } [get_ports { rpi_gpio_tri_io[1]  }];
#set_property -dict { PACKAGE_PIN V8    IOSTANDARD LVCMOS33 } [get_ports { rpi_gpio_tri_io[2] }];
#set_property -dict { PACKAGE_PIN W10   IOSTANDARD LVCMOS33 } [get_ports { rpi_gpio_tri_io[3] }];
#set_property -dict { PACKAGE_PIN B20   IOSTANDARD LVCMOS33 } [get_ports { rpi_gpio_tri_io[4] }];
#set_property -dict { PACKAGE_PIN W8    IOSTANDARD LVCMOS33 } [get_ports { rpi_gpio_tri_io[5] }];
#set_property -dict { PACKAGE_PIN V6    IOSTANDARD LVCMOS33 } [get_ports { rpi_gpio_tri_io[6] }];
#set_property -dict { PACKAGE_PIN Y6    IOSTANDARD LVCMOS33 } [get_ports { rpi_gpio_tri_io[7] }];
#set_property -dict { PACKAGE_PIN B19   IOSTANDARD LVCMOS33 } [get_ports { rpi_gpio_tri_io[8] }];
#set_property -dict { PACKAGE_PIN U7    IOSTANDARD LVCMOS33 } [get_ports { rpi_gpio_tri_io[9] }];
#set_property -dict { PACKAGE_PIN C20   IOSTANDARD LVCMOS33 } [get_ports { rpi_gpio_tri_io[10] }];
#set_property -dict { PACKAGE_PIN Y8    IOSTANDARD LVCMOS33 } [get_ports { rpi_gpio_tri_io[11] }];
#set_property -dict { PACKAGE_PIN A20   IOSTANDARD LVCMOS33 } [get_ports { rpi_gpio_tri_io[12] }];
#set_property -dict { PACKAGE_PIN Y9    IOSTANDARD LVCMOS33 } [get_ports { rpi_gpio_tri_io[13] }];
#set_property -dict { PACKAGE_PIN U8    IOSTANDARD LVCMOS33 } [get_ports { rpi_gpio_tri_io[14] }];
#set_property -dict { PACKAGE_PIN W6    IOSTANDARD LVCMOS33 } [get_ports { rpi_gpio_tri_io[15] }];
#set_property -dict { PACKAGE_PIN Y7    IOSTANDARD LVCMOS33 } [get_ports { rpi_gpio_tri_io[16] }];
#set_property -dict { PACKAGE_PIN F20   IOSTANDARD LVCMOS33 } [get_ports { rpi_gpio_tri_io[17] }];
#set_property -dict { PACKAGE_PIN W9    IOSTANDARD LVCMOS33 } [get_ports { rpi_gpio_tri_io[18] }];
#set_property -dict { PACKAGE_PIN V7    IOSTANDARD LVCMOS33 } [get_ports { rpi_gpio_tri_io[19] }];
