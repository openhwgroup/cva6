##################################################################################
## ZCU104 Rev1.0 Master XDC                                                     ##
##################################################################################
## JTAG
# Controlled by PS (AXI-mapped)

## UART (on PL-side UART2)
#set_property -dict { PACKAGE_PIN A20  IOSTANDARD LVCMOS18 } [get_ports UART_txd        ];
#set_property -dict { PACKAGE_PIN C19  IOSTANDARD LVCMOS18 } [get_ports UART_rxd        ];

## LEDs
#set_property -dict { PACKAGE_PIN D5   IOSTANDARD LVCMOS33 } [get_ports { led[0] }];
#set_property -dict { PACKAGE_PIN D6   IOSTANDARD LVCMOS33 } [get_ports { led[1] }];
#set_property -dict { PACKAGE_PIN A5   IOSTANDARD LVCMOS33 } [get_ports { led[2] }];
#set_property -dict { PACKAGE_PIN B5   IOSTANDARD LVCMOS33 } [get_ports { led[3] }];

## Switches
#set_property -dict { PACKAGE_PIN E4   IOSTANDARD LVCMOS33 } [get_ports { sw[0]  }];
#set_property -dict { PACKAGE_PIN D4   IOSTANDARD LVCMOS33 } [get_ports { sw[1]  }];
#set_property -dict { PACKAGE_PIN F5   IOSTANDARD LVCMOS33 } [get_ports { sw[2]  }];
#set_property -dict { PACKAGE_PIN F4   IOSTANDARD LVCMOS33 } [get_ports { sw[3]  }];

## Fan Control
# Controlled by PS

## Ethernet
# Controlled by PS

## SD card
# SPI mode,
# Wired on PMOD0
# Requires an adapter https://digilent.com/shop/pmod-microsd-microsd-card-slot/
set_property -dict {PACKAGE_PIN H7 IOSTANDARD LVCMOS33} [get_ports spi_clk_o ]; # Adapter Pin 4 -> Pin J55.1 -> PMOD0_3
set_property -dict {PACKAGE_PIN G7 IOSTANDARD LVCMOS33} [get_ports spi_miso ]; # Adapter Pin 3 -> Pin J55.5 -> PMOD0_2
set_property -dict {PACKAGE_PIN H8 IOSTANDARD LVCMOS33} [get_ports spi_mosi ]; # Adapter Pin 2 -> Pin J55.3 -> PMOD0_1
set_property -dict {PACKAGE_PIN G8 IOSTANDARD LVCMOS33} [get_ports spi_ss ]; # Adapter Pin 1 -> Pin J55.1 -> PMOD0_0

### DDR4
## Clock
# Set in BD
#set_property PACKAGE_PIN AH17     [get_ports clk_300mhz_clk_n] ; # Bank  64 VCCO - VCC1V2   - IO_L13N_T2L_N1_GC_QBC_64
#set_property IOSTANDARD  DIFF_SSTL12_DCI [get_ports clk_300mhz_clk_n] ; # Bank  64 VCCO - VCC1V2   - IO_L13N_T2L_N1_GC_QBC_64
#set_property PACKAGE_PIN AH18     [get_ports clk_300mhz_clk_p] ; # Bank  64 VCCO - VCC1V2   - IO_L13P_T2L_N0_GC_QBC_64
#set_property IOSTANDARD  DIFF_SSTL12_DCI [get_ports clk_300mhz_clk_p] ; # Bank  64 VCCO - VCC1V2   - IO_L13P_T2L_N0_GC_QBC_64
## Pinout
# Not set in BD (custom RAM)
set_property PACKAGE_PIN AC13     [get_ports { c0_ddr4_dq[32] }] ; # Bank  66 VCCO - VCC1V2   - IO_L24N_T3U_N11_66
set_property IOSTANDARD  POD12_DCI    [get_ports { c0_ddr4_dq[32] }] ; # Bank  66 VCCO - VCC1V2   - IO_L24N_T3U_N11_66
set_property PACKAGE_PIN AB13     [get_ports { c0_ddr4_dq[33] }] ; # Bank  66 VCCO - VCC1V2   - IO_L24P_T3U_N10_66
set_property IOSTANDARD  POD12_DCI    [get_ports { c0_ddr4_dq[33] }] ; # Bank  66 VCCO - VCC1V2   - IO_L24P_T3U_N10_66
set_property PACKAGE_PIN AF12     [get_ports { c0_ddr4_dq[34] }] ; # Bank  66 VCCO - VCC1V2   - IO_L23N_T3U_N9_66
set_property IOSTANDARD  POD12_DCI    [get_ports { c0_ddr4_dq[34] }] ; # Bank  66 VCCO - VCC1V2   - IO_L23N_T3U_N9_66
set_property PACKAGE_PIN AE12     [get_ports { c0_ddr4_dq[35] }] ; # Bank  66 VCCO - VCC1V2   - IO_L23P_T3U_N8_66
set_property IOSTANDARD  POD12_DCI    [get_ports { c0_ddr4_dq[35] }] ; # Bank  66 VCCO - VCC1V2   - IO_L23P_T3U_N8_66
set_property PACKAGE_PIN AD12     [get_ports { c0_ddr4_dqs_c[4] }] ; # Bank  66 VCCO - VCC1V2   - IO_L22N_T3U_N7_DBC_AD0N_66
set_property IOSTANDARD  DIFF_POD12_DCI [get_ports { c0_ddr4_dqs_c[4] }] ; # Bank  66 VCCO - VCC1V2   - IO_L22N_T3U_N7_DBC_AD0N_66
set_property PACKAGE_PIN AC12     [get_ports { c0_ddr4_dqs_t[4] }] ; # Bank  66 VCCO - VCC1V2   - IO_L22P_T3U_N6_DBC_AD0P_66
set_property IOSTANDARD  DIFF_POD12_DCI [get_ports { c0_ddr4_dqs_t[4] }] ; # Bank  66 VCCO - VCC1V2   - IO_L22P_T3U_N6_DBC_AD0P_66
set_property PACKAGE_PIN AF13     [get_ports { c0_ddr4_dq[36] }] ; # Bank  66 VCCO - VCC1V2   - IO_L21N_T3L_N5_AD8N_66
set_property IOSTANDARD  POD12_DCI    [get_ports { c0_ddr4_dq[36] }] ; # Bank  66 VCCO - VCC1V2   - IO_L21N_T3L_N5_AD8N_66
set_property PACKAGE_PIN AE13     [get_ports { c0_ddr4_dq[37] }] ; # Bank  66 VCCO - VCC1V2   - IO_L21P_T3L_N4_AD8P_66
set_property IOSTANDARD  POD12_DCI    [get_ports { c0_ddr4_dq[37] }] ; # Bank  66 VCCO - VCC1V2   - IO_L21P_T3L_N4_AD8P_66
set_property PACKAGE_PIN AE14     [get_ports { c0_ddr4_dq[38] }] ; # Bank  66 VCCO - VCC1V2   - IO_L20N_T3L_N3_AD1N_66
set_property IOSTANDARD  POD12_DCI    [get_ports { c0_ddr4_dq[38] }] ; # Bank  66 VCCO - VCC1V2   - IO_L20N_T3L_N3_AD1N_66
set_property PACKAGE_PIN AD14     [get_ports { c0_ddr4_dq[39] }] ; # Bank  66 VCCO - VCC1V2   - IO_L20P_T3L_N2_AD1P_66
set_property IOSTANDARD  POD12_DCI    [get_ports { c0_ddr4_dq[39] }] ; # Bank  66 VCCO - VCC1V2   - IO_L20P_T3L_N2_AD1P_66
set_property PACKAGE_PIN AF11     [get_ports { c0_ddr4_dm_n[4] }] ; # Bank  66 VCCO - VCC1V2   - IO_L19P_T3L_N0_DBC_AD9P_66
set_property IOSTANDARD  POD12_DCI    [get_ports { c0_ddr4_dm_n[4] }] ; # Bank  66 VCCO - VCC1V2   - IO_L19P_T3L_N0_DBC_AD9P_66
set_property PACKAGE_PIN AG8      [get_ports { c0_ddr4_dq[40] }] ; # Bank  66 VCCO - VCC1V2   - IO_L18N_T2U_N11_AD2N_66
set_property IOSTANDARD  POD12_DCI    [get_ports { c0_ddr4_dq[40] }] ; # Bank  66 VCCO - VCC1V2   - IO_L18N_T2U_N11_AD2N_66
set_property PACKAGE_PIN AF8      [get_ports { c0_ddr4_dq[41] }] ; # Bank  66 VCCO - VCC1V2   - IO_L18P_T2U_N10_AD2P_66
set_property IOSTANDARD  POD12_DCI    [get_ports { c0_ddr4_dq[41] }] ; # Bank  66 VCCO - VCC1V2   - IO_L18P_T2U_N10_AD2P_66
set_property PACKAGE_PIN AG10     [get_ports { c0_ddr4_dq[42] }] ; # Bank  66 VCCO - VCC1V2   - IO_L17N_T2U_N9_AD10N_66
set_property IOSTANDARD  POD12_DCI    [get_ports { c0_ddr4_dq[42] }] ; # Bank  66 VCCO - VCC1V2   - IO_L17N_T2U_N9_AD10N_66
set_property PACKAGE_PIN AG11     [get_ports { c0_ddr4_dq[43] }] ; # Bank  66 VCCO - VCC1V2   - IO_L17P_T2U_N8_AD10P_66
set_property IOSTANDARD  POD12_DCI    [get_ports { c0_ddr4_dq[43] }] ; # Bank  66 VCCO - VCC1V2   - IO_L17P_T2U_N8_AD10P_66
set_property PACKAGE_PIN AH9      [get_ports { c0_ddr4_dqs_c[5] }] ; # Bank  66 VCCO - VCC1V2   - IO_L16N_T2U_N7_QBC_AD3N_66
set_property IOSTANDARD  DIFF_POD12_DCI [get_ports { c0_ddr4_dqs_c[5] }] ; # Bank  66 VCCO - VCC1V2   - IO_L16N_T2U_N7_QBC_AD3N_66
set_property PACKAGE_PIN AG9      [get_ports { c0_ddr4_dqs_t[5] }] ; # Bank  66 VCCO - VCC1V2   - IO_L16P_T2U_N6_QBC_AD3P_66
set_property IOSTANDARD  DIFF_POD12_DCI [get_ports { c0_ddr4_dqs_t[5] }] ; # Bank  66 VCCO - VCC1V2   - IO_L16P_T2U_N6_QBC_AD3P_66
set_property PACKAGE_PIN AH13     [get_ports { c0_ddr4_dq[44] }] ; # Bank  66 VCCO - VCC1V2   - IO_L15N_T2L_N5_AD11N_66
set_property IOSTANDARD  POD12_DCI    [get_ports { c0_ddr4_dq[44] }] ; # Bank  66 VCCO - VCC1V2   - IO_L15N_T2L_N5_AD11N_66
set_property PACKAGE_PIN AG13     [get_ports { c0_ddr4_dq[45] }] ; # Bank  66 VCCO - VCC1V2   - IO_L15P_T2L_N4_AD11P_66
set_property IOSTANDARD  POD12_DCI    [get_ports { c0_ddr4_dq[45] }] ; # Bank  66 VCCO - VCC1V2   - IO_L15P_T2L_N4_AD11P_66
set_property PACKAGE_PIN AJ11     [get_ports { c0_ddr4_dq[46] }] ; # Bank  66 VCCO - VCC1V2   - IO_L14N_T2L_N3_GC_66
set_property IOSTANDARD  POD12_DCI    [get_ports { c0_ddr4_dq[46] }] ; # Bank  66 VCCO - VCC1V2   - IO_L14N_T2L_N3_GC_66
set_property PACKAGE_PIN AH11     [get_ports { c0_ddr4_dq[47] }] ; # Bank  66 VCCO - VCC1V2   - IO_L14P_T2L_N2_GC_66
set_property IOSTANDARD  POD12_DCI    [get_ports { c0_ddr4_dq[47] }] ; # Bank  66 VCCO - VCC1V2   - IO_L14P_T2L_N2_GC_66
set_property PACKAGE_PIN AH12     [get_ports { c0_ddr4_dm_n[5] }] ; # Bank  66 VCCO - VCC1V2   - IO_L13P_T2L_N0_GC_QBC_66
set_property IOSTANDARD  POD12_DCI    [get_ports { c0_ddr4_dm_n[5] }] ; # Bank  66 VCCO - VCC1V2   - IO_L13P_T2L_N0_GC_QBC_66
set_property PACKAGE_PIN AK9      [get_ports { c0_ddr4_dq[48] }] ; # Bank  66 VCCO - VCC1V2   - IO_L12N_T1U_N11_GC_66
set_property IOSTANDARD  POD12_DCI    [get_ports { c0_ddr4_dq[48] }] ; # Bank  66 VCCO - VCC1V2   - IO_L12N_T1U_N11_GC_66
set_property PACKAGE_PIN AJ9      [get_ports { c0_ddr4_dq[49] }] ; # Bank  66 VCCO - VCC1V2   - IO_L12P_T1U_N10_GC_66
set_property IOSTANDARD  POD12_DCI    [get_ports { c0_ddr4_dq[49] }] ; # Bank  66 VCCO - VCC1V2   - IO_L12P_T1U_N10_GC_66
set_property PACKAGE_PIN AK10     [get_ports { c0_ddr4_dq[50] }] ; # Bank  66 VCCO - VCC1V2   - IO_L11N_T1U_N9_GC_66
set_property IOSTANDARD  POD12_DCI    [get_ports { c0_ddr4_dq[50] }] ; # Bank  66 VCCO - VCC1V2   - IO_L11N_T1U_N9_GC_66
set_property PACKAGE_PIN AJ10     [get_ports { c0_ddr4_dq[51] }] ; # Bank  66 VCCO - VCC1V2   - IO_L11P_T1U_N8_GC_66
set_property IOSTANDARD  POD12_DCI    [get_ports { c0_ddr4_dq[51] }] ; # Bank  66 VCCO - VCC1V2   - IO_L11P_T1U_N8_GC_66
set_property PACKAGE_PIN AL8      [get_ports { c0_ddr4_dqs_c[6] }] ; # Bank  66 VCCO - VCC1V2   - IO_L10N_T1U_N7_QBC_AD4N_66
set_property IOSTANDARD  DIFF_POD12_DCI [get_ports { c0_ddr4_dqs_c[6] }] ; # Bank  66 VCCO - VCC1V2   - IO_L10N_T1U_N7_QBC_AD4N_66
set_property PACKAGE_PIN AK8      [get_ports { c0_ddr4_dqs_t[6] }] ; # Bank  66 VCCO - VCC1V2   - IO_L10P_T1U_N6_QBC_AD4P_66
set_property IOSTANDARD  DIFF_POD12_DCI [get_ports { c0_ddr4_dqs_t[6] }] ; # Bank  66 VCCO - VCC1V2   - IO_L10P_T1U_N6_QBC_AD4P_66
set_property PACKAGE_PIN AL12     [get_ports { c0_ddr4_dq[52] }] ; # Bank  66 VCCO - VCC1V2   - IO_L9N_T1L_N5_AD12N_66
set_property IOSTANDARD  POD12_DCI    [get_ports { c0_ddr4_dq[52] }] ; # Bank  66 VCCO - VCC1V2   - IO_L9N_T1L_N5_AD12N_66
set_property PACKAGE_PIN AK12     [get_ports { c0_ddr4_dq[53] }] ; # Bank  66 VCCO - VCC1V2   - IO_L9P_T1L_N4_AD12P_66
set_property IOSTANDARD  POD12_DCI    [get_ports { c0_ddr4_dq[53] }] ; # Bank  66 VCCO - VCC1V2   - IO_L9P_T1L_N4_AD12P_66
set_property PACKAGE_PIN AL10     [get_ports { c0_ddr4_dq[54] }] ; # Bank  66 VCCO - VCC1V2   - IO_L8N_T1L_N3_AD5N_66
set_property IOSTANDARD  POD12_DCI    [get_ports { c0_ddr4_dq[54] }] ; # Bank  66 VCCO - VCC1V2   - IO_L8N_T1L_N3_AD5N_66
set_property PACKAGE_PIN AL11     [get_ports { c0_ddr4_dq[55] }] ; # Bank  66 VCCO - VCC1V2   - IO_L8P_T1L_N2_AD5P_66
set_property IOSTANDARD  POD12_DCI    [get_ports { c0_ddr4_dq[55] }] ; # Bank  66 VCCO - VCC1V2   - IO_L8P_T1L_N2_AD5P_66
set_property PACKAGE_PIN AK13     [get_ports { c0_ddr4_dm_n[6] }] ; # Bank  66 VCCO - VCC1V2   - IO_L7P_T1L_N0_QBC_AD13P_66
set_property IOSTANDARD  POD12_DCI    [get_ports { c0_ddr4_dm_n[6] }] ; # Bank  66 VCCO - VCC1V2   - IO_L7P_T1L_N0_QBC_AD13P_66
set_property PACKAGE_PIN AM8      [get_ports { c0_ddr4_dq[56] }] ; # Bank  66 VCCO - VCC1V2   - IO_L6N_T0U_N11_AD6N_66
set_property IOSTANDARD  POD12_DCI    [get_ports { c0_ddr4_dq[56] }] ; # Bank  66 VCCO - VCC1V2   - IO_L6N_T0U_N11_AD6N_66
set_property PACKAGE_PIN AM9      [get_ports { c0_ddr4_dq[57] }] ; # Bank  66 VCCO - VCC1V2   - IO_L6P_T0U_N10_AD6P_66
set_property IOSTANDARD  POD12_DCI    [get_ports { c0_ddr4_dq[57] }] ; # Bank  66 VCCO - VCC1V2   - IO_L6P_T0U_N10_AD6P_66
set_property PACKAGE_PIN AM10     [get_ports { c0_ddr4_dq[58] }] ; # Bank  66 VCCO - VCC1V2   - IO_L5N_T0U_N9_AD14N_66
set_property IOSTANDARD  POD12_DCI    [get_ports { c0_ddr4_dq[58] }] ; # Bank  66 VCCO - VCC1V2   - IO_L5N_T0U_N9_AD14N_66
set_property PACKAGE_PIN AM11     [get_ports { c0_ddr4_dq[59] }] ; # Bank  66 VCCO - VCC1V2   - IO_L5P_T0U_N8_AD14P_66
set_property IOSTANDARD  POD12_DCI    [get_ports { c0_ddr4_dq[59] }] ; # Bank  66 VCCO - VCC1V2   - IO_L5P_T0U_N8_AD14P_66
set_property PACKAGE_PIN AN8      [get_ports { c0_ddr4_dqs_c[7] }] ; # Bank  66 VCCO - VCC1V2   - IO_L4N_T0U_N7_DBC_AD7N_66
set_property IOSTANDARD  DIFF_POD12_DCI [get_ports { c0_ddr4_dqs_c[7] }] ; # Bank  66 VCCO - VCC1V2   - IO_L4N_T0U_N7_DBC_AD7N_66
set_property PACKAGE_PIN AN9      [get_ports { c0_ddr4_dqs_t[7] }] ; # Bank  66 VCCO - VCC1V2   - IO_L4P_T0U_N6_DBC_AD7P_66
set_property IOSTANDARD  DIFF_POD12_DCI [get_ports { c0_ddr4_dqs_t[7] }] ; # Bank  66 VCCO - VCC1V2   - IO_L4P_T0U_N6_DBC_AD7P_66
set_property PACKAGE_PIN AP11     [get_ports { c0_ddr4_dq[60] }] ; # Bank  66 VCCO - VCC1V2   - IO_L3N_T0L_N5_AD15N_66
set_property IOSTANDARD  POD12_DCI    [get_ports { c0_ddr4_dq[60] }] ; # Bank  66 VCCO - VCC1V2   - IO_L3N_T0L_N5_AD15N_66
set_property PACKAGE_PIN AN11     [get_ports { c0_ddr4_dq[61] }] ; # Bank  66 VCCO - VCC1V2   - IO_L3P_T0L_N4_AD15P_66
set_property IOSTANDARD  POD12_DCI    [get_ports { c0_ddr4_dq[61] }] ; # Bank  66 VCCO - VCC1V2   - IO_L3P_T0L_N4_AD15P_66
set_property PACKAGE_PIN AP9      [get_ports { c0_ddr4_dq[62] }] ; # Bank  66 VCCO - VCC1V2   - IO_L2N_T0L_N3_66
set_property IOSTANDARD  POD12_DCI    [get_ports { c0_ddr4_dq[62] }] ; # Bank  66 VCCO - VCC1V2   - IO_L2N_T0L_N3_66
set_property PACKAGE_PIN AP10     [get_ports { c0_ddr4_dq[63] }] ; # Bank  66 VCCO - VCC1V2   - IO_L2P_T0L_N2_66
set_property IOSTANDARD  POD12_DCI    [get_ports { c0_ddr4_dq[63] }] ; # Bank  66 VCCO - VCC1V2   - IO_L2P_T0L_N2_66
set_property PACKAGE_PIN AN12     [get_ports { c0_ddr4_dm_n[7] }] ; # Bank  66 VCCO - VCC1V2   - IO_L1P_T0L_N0_DBC_66
set_property IOSTANDARD  POD12_DCI    [get_ports { c0_ddr4_dm_n[7] }] ; # Bank  66 VCCO - VCC1V2   - IO_L1P_T0L_N0_DBC_66
set_property PACKAGE_PIN AA20     [get_ports { c0_ddr4_dq[8] }] ; # Bank  65 VCCO - VCC1V2   - IO_L24N_T3U_N11_PERSTN0_65
set_property IOSTANDARD  POD12_DCI   [get_ports { c0_ddr4_dq[8] }] ; # Bank  65 VCCO - VCC1V2   - IO_L24N_T3U_N11_PERSTN0_65
set_property PACKAGE_PIN AA19     [get_ports { c0_ddr4_dq[9] }] ; # Bank  65 VCCO - VCC1V2   - IO_L24P_T3U_N10_PERSTN1_I2C_SDA_65
set_property IOSTANDARD  POD12_DCI    [get_ports { c0_ddr4_dq[9] }] ; # Bank  65 VCCO - VCC1V2   - IO_L24P_T3U_N10_PERSTN1_I2C_SDA_65
set_property PACKAGE_PIN AD19     [get_ports { c0_ddr4_dq[10] }] ; # Bank  65 VCCO - VCC1V2   - IO_L23N_T3U_N9_65
set_property IOSTANDARD  POD12_DCI    [get_ports { c0_ddr4_dq[10] }] ; # Bank  65 VCCO - VCC1V2   - IO_L23N_T3U_N9_65
set_property PACKAGE_PIN AC18     [get_ports { c0_ddr4_dq[11] }] ; # Bank  65 VCCO - VCC1V2   - IO_L23P_T3U_N8_I2C_SCLK_65
set_property IOSTANDARD  POD12_DCI    [get_ports { c0_ddr4_dq[11] }] ; # Bank  65 VCCO - VCC1V2   - IO_L23P_T3U_N8_I2C_SCLK_65
set_property PACKAGE_PIN AB18     [get_ports { c0_ddr4_dqs_c[1] }] ; # Bank  65 VCCO - VCC1V2   - IO_L22N_T3U_N7_DBC_AD0N_65
set_property IOSTANDARD  DIFF_POD12_DCI [get_ports { c0_ddr4_dqs_c[1] }] ; # Bank  65 VCCO - VCC1V2   - IO_L22N_T3U_N7_DBC_AD0N_65
set_property PACKAGE_PIN AA18     [get_ports { c0_ddr4_dqs_t[1] }] ; # Bank  65 VCCO - VCC1V2   - IO_L22P_T3U_N6_DBC_AD0P_65
set_property IOSTANDARD  DIFF_POD12_DCI [get_ports { c0_ddr4_dqs_t[1] }] ; # Bank  65 VCCO - VCC1V2   - IO_L22P_T3U_N6_DBC_AD0P_65
set_property PACKAGE_PIN AE20     [get_ports { c0_ddr4_dq[12] }] ; # Bank  65 VCCO - VCC1V2   - IO_L21N_T3L_N5_AD8N_65
set_property IOSTANDARD  POD12_DCI    [get_ports { c0_ddr4_dq[12] }] ; # Bank  65 VCCO - VCC1V2   - IO_L21N_T3L_N5_AD8N_65
set_property PACKAGE_PIN AD20     [get_ports { c0_ddr4_dq[13] }] ; # Bank  65 VCCO - VCC1V2   - IO_L21P_T3L_N4_AD8P_65
set_property IOSTANDARD  POD12_DCI    [get_ports { c0_ddr4_dq[13] }] ; # Bank  65 VCCO - VCC1V2   - IO_L21P_T3L_N4_AD8P_65
set_property PACKAGE_PIN AC19     [get_ports { c0_ddr4_dq[14] }] ; # Bank  65 VCCO - VCC1V2   - IO_L20N_T3L_N3_AD1N_65
set_property IOSTANDARD  POD12_DCI    [get_ports { c0_ddr4_dq[14] }] ; # Bank  65 VCCO - VCC1V2   - IO_L20N_T3L_N3_AD1N_65
set_property PACKAGE_PIN AB19     [get_ports { c0_ddr4_dq[15] }] ; # Bank  65 VCCO - VCC1V2   - IO_L20P_T3L_N2_AD1P_65
set_property IOSTANDARD  POD12_DCI    [get_ports { c0_ddr4_dq[15] }] ; # Bank  65 VCCO - VCC1V2   - IO_L20P_T3L_N2_AD1P_65
set_property PACKAGE_PIN AE18     [get_ports { c0_ddr4_dm_n[1] }] ; # Bank  65 VCCO - VCC1V2   - IO_L19P_T3L_N0_DBC_AD9P_65
set_property IOSTANDARD  POD12_DCI    [get_ports { c0_ddr4_dm_n[1] }] ; # Bank  65 VCCO - VCC1V2   - IO_L19P_T3L_N0_DBC_AD9P_65
set_property PACKAGE_PIN AE24     [get_ports { c0_ddr4_dq[0] }] ; # Bank  65 VCCO - VCC1V2   - IO_L18N_T2U_N11_AD2N_65
set_property IOSTANDARD  POD12_DCI    [get_ports { c0_ddr4_dq[0] }] ; # Bank  65 VCCO - VCC1V2   - IO_L18N_T2U_N11_AD2N_65
set_property PACKAGE_PIN AE23     [get_ports { c0_ddr4_dq[1] }] ; # Bank  65 VCCO - VCC1V2   - IO_L18P_T2U_N10_AD2P_65
set_property IOSTANDARD  POD12_DCI    [get_ports { c0_ddr4_dq[1] }] ; # Bank  65 VCCO - VCC1V2   - IO_L18P_T2U_N10_AD2P_65
set_property PACKAGE_PIN AF22     [get_ports { c0_ddr4_dq[2] }] ; # Bank  65 VCCO - VCC1V2   - IO_L17N_T2U_N9_AD10N_65
set_property IOSTANDARD  POD12_DCI    [get_ports { c0_ddr4_dq[2] }] ; # Bank  65 VCCO - VCC1V2   - IO_L17N_T2U_N9_AD10N_65
set_property PACKAGE_PIN AF21     [get_ports { c0_ddr4_dq[3] }] ; # Bank  65 VCCO - VCC1V2   - IO_L17P_T2U_N8_AD10P_65
set_property IOSTANDARD  POD12_DCI    [get_ports { c0_ddr4_dq[3] }] ; # Bank  65 VCCO - VCC1V2   - IO_L17P_T2U_N8_AD10P_65
set_property PACKAGE_PIN AG23     [get_ports { c0_ddr4_dqs_c[0] }] ; # Bank  65 VCCO - VCC1V2   - IO_L16N_T2U_N7_QBC_AD3N_65
set_property IOSTANDARD  DIFF_POD12_DCI [get_ports { c0_ddr4_dqs_c[0] }] ; # Bank  65 VCCO - VCC1V2   - IO_L16N_T2U_N7_QBC_AD3N_65
set_property PACKAGE_PIN AF23     [get_ports { c0_ddr4_dqs_t[0] }] ; # Bank  65 VCCO - VCC1V2   - IO_L16P_T2U_N6_QBC_AD3P_65
set_property IOSTANDARD  DIFF_POD12_DCI [get_ports { c0_ddr4_dqs_t[0] }] ; # Bank  65 VCCO - VCC1V2   - IO_L16P_T2U_N6_QBC_AD3P_65
set_property PACKAGE_PIN AG20     [get_ports { c0_ddr4_dq[4] }] ; # Bank  65 VCCO - VCC1V2   - IO_L15N_T2L_N5_AD11N_65
set_property IOSTANDARD  POD12_DCI    [get_ports { c0_ddr4_dq[4] }] ; # Bank  65 VCCO - VCC1V2   - IO_L15N_T2L_N5_AD11N_65
set_property PACKAGE_PIN AG19     [get_ports { c0_ddr4_dq[5] }] ; # Bank  65 VCCO - VCC1V2   - IO_L15P_T2L_N4_AD11P_65
set_property IOSTANDARD  POD12_DCI    [get_ports { c0_ddr4_dq[5] }] ; # Bank  65 VCCO - VCC1V2   - IO_L15P_T2L_N4_AD11P_65
set_property PACKAGE_PIN AH21     [get_ports { c0_ddr4_dq[6] }] ; # Bank  65 VCCO - VCC1V2   - IO_L14N_T2L_N3_GC_65
set_property IOSTANDARD  POD12_DCI    [get_ports { c0_ddr4_dq[6] }] ; # Bank  65 VCCO - VCC1V2   - IO_L14N_T2L_N3_GC_65
set_property PACKAGE_PIN AG21     [get_ports { c0_ddr4_dq[7] }] ; # Bank  65 VCCO - VCC1V2   - IO_L14P_T2L_N2_GC_65
set_property IOSTANDARD  POD12_DCI    [get_ports { c0_ddr4_dq[7] }] ; # Bank  65 VCCO - VCC1V2   - IO_L14P_T2L_N2_GC_65
set_property PACKAGE_PIN AH22     [get_ports { c0_ddr4_dm_n[0] }] ; # Bank  65 VCCO - VCC1V2   - IO_L13P_T2L_N0_GC_QBC_65
set_property IOSTANDARD  POD12_DCI    [get_ports { c0_ddr4_dm_n[0] }] ; # Bank  65 VCCO - VCC1V2   - IO_L13P_T2L_N0_GC_QBC_65
set_property PACKAGE_PIN AJ22     [get_ports { c0_ddr4_dq[16] }] ; # Bank  65 VCCO - VCC1V2   - IO_L12N_T1U_N11_GC_65
set_property IOSTANDARD  POD12_DCI    [get_ports { c0_ddr4_dq[16] }] ; # Bank  65 VCCO - VCC1V2   - IO_L12N_T1U_N11_GC_65
set_property PACKAGE_PIN AJ21     [get_ports { c0_ddr4_dq[17] }] ; # Bank  65 VCCO - VCC1V2   - IO_L12P_T1U_N10_GC_65
set_property IOSTANDARD  POD12_DCI    [get_ports { c0_ddr4_dq[17] }] ; # Bank  65 VCCO - VCC1V2   - IO_L12P_T1U_N10_GC_65
set_property PACKAGE_PIN AK20     [get_ports { c0_ddr4_dq[18] }] ; # Bank  65 VCCO - VCC1V2   - IO_L11N_T1U_N9_GC_65
set_property IOSTANDARD  POD12_DCI    [get_ports { c0_ddr4_dq[18] }] ; # Bank  65 VCCO - VCC1V2   - IO_L11N_T1U_N9_GC_65
set_property PACKAGE_PIN AJ20     [get_ports { c0_ddr4_dq[19] }] ; # Bank  65 VCCO - VCC1V2   - IO_L11P_T1U_N8_GC_65
set_property IOSTANDARD  POD12_DCI    [get_ports { c0_ddr4_dq[19] }] ; # Bank  65 VCCO - VCC1V2   - IO_L11P_T1U_N8_GC_65
set_property PACKAGE_PIN AK23     [get_ports { c0_ddr4_dqs_c[2] }] ; # Bank  65 VCCO - VCC1V2   - IO_L10N_T1U_N7_QBC_AD4N_65
set_property IOSTANDARD  DIFF_POD12_DCI [get_ports { c0_ddr4_dqs_c[2] }] ; # Bank  65 VCCO - VCC1V2   - IO_L10N_T1U_N7_QBC_AD4N_65
set_property PACKAGE_PIN AK22     [get_ports { c0_ddr4_dqs_t[2] }] ; # Bank  65 VCCO - VCC1V2   - IO_L10P_T1U_N6_QBC_AD4P_65
set_property IOSTANDARD  DIFF_POD12_DCI [get_ports { c0_ddr4_dqs_t[2] }] ; # Bank  65 VCCO - VCC1V2   - IO_L10P_T1U_N6_QBC_AD4P_65
set_property PACKAGE_PIN AK19     [get_ports { c0_ddr4_dq[20] }] ; # Bank  65 VCCO - VCC1V2   - IO_L9N_T1L_N5_AD12N_65
set_property IOSTANDARD  POD12_DCI    [get_ports { c0_ddr4_dq[20] }] ; # Bank  65 VCCO - VCC1V2   - IO_L9N_T1L_N5_AD12N_65
set_property PACKAGE_PIN AJ19     [get_ports { c0_ddr4_dq[21] }] ; # Bank  65 VCCO - VCC1V2   - IO_L9P_T1L_N4_AD12P_65
set_property IOSTANDARD  POD12_DCI    [get_ports { c0_ddr4_dq[21] }] ; # Bank  65 VCCO - VCC1V2   - IO_L9P_T1L_N4_AD12P_65
set_property PACKAGE_PIN AL23     [get_ports { c0_ddr4_dq[22] }] ; # Bank  65 VCCO - VCC1V2   - IO_L8N_T1L_N3_AD5N_65
set_property IOSTANDARD  POD12_DCI    [get_ports { c0_ddr4_dq[22] }] ; # Bank  65 VCCO - VCC1V2   - IO_L8N_T1L_N3_AD5N_65
set_property PACKAGE_PIN AL22     [get_ports { c0_ddr4_dq[23] }] ; # Bank  65 VCCO - VCC1V2   - IO_L8P_T1L_N2_AD5P_65
set_property IOSTANDARD  POD12_DCI    [get_ports { c0_ddr4_dq[23] }] ; # Bank  65 VCCO - VCC1V2   - IO_L8P_T1L_N2_AD5P_65
set_property PACKAGE_PIN AL20     [get_ports { c0_ddr4_dm_n[2] }] ; # Bank  65 VCCO - VCC1V2   - IO_L7P_T1L_N0_QBC_AD13P_65
set_property IOSTANDARD  POD12_DCI    [get_ports { c0_ddr4_dm_n[2] }] ; # Bank  65 VCCO - VCC1V2   - IO_L7P_T1L_N0_QBC_AD13P_65
set_property PACKAGE_PIN AN23     [get_ports { c0_ddr4_dq[24] }] ; # Bank  65 VCCO - VCC1V2   - IO_L6N_T0U_N11_AD6N_65
set_property IOSTANDARD  POD12_DCI    [get_ports { c0_ddr4_dq[24] }] ; # Bank  65 VCCO - VCC1V2   - IO_L6N_T0U_N11_AD6N_65
set_property PACKAGE_PIN AM23     [get_ports { c0_ddr4_dq[25] }] ; # Bank  65 VCCO - VCC1V2   - IO_L6P_T0U_N10_AD6P_65
set_property IOSTANDARD  POD12_DCI    [get_ports { c0_ddr4_dq[25] }] ; # Bank  65 VCCO - VCC1V2   - IO_L6P_T0U_N10_AD6P_65
set_property PACKAGE_PIN AP23     [get_ports { c0_ddr4_dq[26] }] ; # Bank  65 VCCO - VCC1V2   - IO_L5N_T0U_N9_AD14N_65
set_property IOSTANDARD  POD12_DCI    [get_ports { c0_ddr4_dq[26] }] ; # Bank  65 VCCO - VCC1V2   - IO_L5N_T0U_N9_AD14N_65
set_property PACKAGE_PIN AN22     [get_ports { c0_ddr4_dq[27] }] ; # Bank  65 VCCO - VCC1V2   - IO_L5P_T0U_N8_AD14P_65
set_property IOSTANDARD  POD12_DCI    [get_ports { c0_ddr4_dq[27] }] ; # Bank  65 VCCO - VCC1V2   - IO_L5P_T0U_N8_AD14P_65
set_property PACKAGE_PIN AN21     [get_ports { c0_ddr4_dqs_c[3] }] ; # Bank  65 VCCO - VCC1V2   - IO_L4N_T0U_N7_DBC_AD7N_65
set_property IOSTANDARD  DIFF_POD12_DCI [get_ports { c0_ddr4_dqs_c[3] }] ; # Bank  65 VCCO - VCC1V2   - IO_L4N_T0U_N7_DBC_AD7N_65
set_property PACKAGE_PIN AM21     [get_ports { c0_ddr4_dqs_t[3] }] ; # Bank  65 VCCO - VCC1V2   - IO_L4P_T0U_N6_DBC_AD7P_SMBALERT_65
set_property IOSTANDARD  DIFF_POD12_DCI [get_ports { c0_ddr4_dqs_t[3] }] ; # Bank  65 VCCO - VCC1V2   - IO_L4P_T0U_N6_DBC_AD7P_SMBALERT_65
set_property PACKAGE_PIN AP22     [get_ports { c0_ddr4_dq[28] }] ; # Bank  65 VCCO - VCC1V2   - IO_L3N_T0L_N5_AD15N_65
set_property IOSTANDARD  POD12_DCI    [get_ports { c0_ddr4_dq[28] }] ; # Bank  65 VCCO - VCC1V2   - IO_L3N_T0L_N5_AD15N_65
set_property PACKAGE_PIN AP21     [get_ports { c0_ddr4_dq[29] }] ; # Bank  65 VCCO - VCC1V2   - IO_L3P_T0L_N4_AD15P_65
set_property IOSTANDARD  POD12_DCI    [get_ports { c0_ddr4_dq[29] }] ; # Bank  65 VCCO - VCC1V2   - IO_L3P_T0L_N4_AD15P_65
set_property PACKAGE_PIN AN19     [get_ports { c0_ddr4_dq[30] }] ; # Bank  65 VCCO - VCC1V2   - IO_L2N_T0L_N3_65
set_property IOSTANDARD  POD12_DCI    [get_ports { c0_ddr4_dq[30] }] ; # Bank  65 VCCO - VCC1V2   - IO_L2N_T0L_N3_65
set_property PACKAGE_PIN AM19     [get_ports { c0_ddr4_dq[31] }] ; # Bank  65 VCCO - VCC1V2   - IO_L2P_T0L_N2_65
set_property IOSTANDARD  POD12_DCI    [get_ports { c0_ddr4_dq[31] }] ; # Bank  65 VCCO - VCC1V2   - IO_L2P_T0L_N2_65
set_property PACKAGE_PIN AP19     [get_ports { c0_ddr4_dm_n[3] }] ; # Bank  65 VCCO - VCC1V2   - IO_L1P_T0L_N0_DBC_65
set_property IOSTANDARD  POD12_DCI    [get_ports { c0_ddr4_dm_n[3] }] ; # Bank  65 VCCO - VCC1V2   - IO_L1P_T0L_N0_DBC_65
set_property PACKAGE_PIN AD17     [get_ports { c0_ddr4_cke }] ; # Bank  64 VCCO - VCC1V2   - IO_L24P_T3U_N10_64
set_property IOSTANDARD  SSTL12_DCI   [get_ports { c0_ddr4_cke }] ; # Bank  64 VCCO - VCC1V2   - IO_L24P_T3U_N10_64
set_property PACKAGE_PIN AB14     [get_ports { c0_ddr4_reset_n }] ; # Bank  64 VCCO - VCC1V2   - IO_L23N_T3U_N9_64
set_property IOSTANDARD  LVCMOS12 [get_ports { c0_ddr4_reset_n }] ; # Bank  64 VCCO - VCC1V2   - IO_L23N_T3U_N9_64
set_property PACKAGE_PIN AA14     [get_ports { c0_ddr4_adr[15] }] ; # Bank  64 VCCO - VCC1V2   - IO_L23P_T3U_N8_64
set_property IOSTANDARD  SSTL12_DCI   [get_ports { c0_ddr4_adr[15] }] ; # Bank  64 VCCO - VCC1V2   - IO_L23P_T3U_N8_64
set_property PACKAGE_PIN AA15     [get_ports { c0_ddr4_cs_n }] ; # Bank  64 VCCO - VCC1V2   - IO_L22N_T3U_N7_DBC_AD0N_64
set_property IOSTANDARD  SSTL12_DCI   [get_ports { c0_ddr4_cs_n }] ; # Bank  64 VCCO - VCC1V2   - IO_L22N_T3U_N7_DBC_AD0N_64
set_property PACKAGE_PIN AA16     [get_ports { c0_ddr4_adr[14] }] ; # Bank  64 VCCO - VCC1V2   - IO_L22P_T3U_N6_DBC_AD0P_64
set_property IOSTANDARD  SSTL12_DCI   [get_ports { c0_ddr4_adr[14] }] ; # Bank  64 VCCO - VCC1V2   - IO_L22P_T3U_N6_DBC_AD0P_64
set_property PACKAGE_PIN AB16     [get_ports { c0_ddr4_bg[1] }] ; # Bank  64 VCCO - VCC1V2   - IO_L21P_T3L_N4_AD8P_64
set_property IOSTANDARD  SSTL12_DCI   [get_ports { c0_ddr4_bg[1] }] ; # Bank  64 VCCO - VCC1V2   - IO_L21P_T3L_N4_AD8P_64
set_property PACKAGE_PIN AC16     [get_ports { c0_ddr4_bg[0] }] ; # Bank  64 VCCO - VCC1V2   - IO_L20N_T3L_N3_AD1N_64
set_property IOSTANDARD  SSTL12_DCI   [get_ports { c0_ddr4_bg[0] }] ; # Bank  64 VCCO - VCC1V2   - IO_L20N_T3L_N3_AD1N_64
set_property PACKAGE_PIN AC17     [get_ports { c0_ddr4_act_n }] ; # Bank  64 VCCO - VCC1V2   - IO_L20P_T3L_N2_AD1P_64
set_property IOSTANDARD  SSTL12_DCI   [get_ports { c0_ddr4_act_n }] ; # Bank  64 VCCO - VCC1V2   - IO_L20P_T3L_N2_AD1P_64
set_property PACKAGE_PIN AE15     [get_ports { c0_ddr4_odt }] ; # Bank  64 VCCO - VCC1V2   - IO_L19N_T3L_N1_DBC_AD9N_64
set_property IOSTANDARD  SSTL12_DCI   [get_ports { c0_ddr4_odt }] ; # Bank  64 VCCO - VCC1V2   - IO_L19N_T3L_N1_DBC_AD9N_64
set_property PACKAGE_PIN AD15     [get_ports { c0_ddr4_adr[16] }] ; # Bank  64 VCCO - VCC1V2   - IO_L19P_T3L_N0_DBC_AD9P_64
set_property IOSTANDARD  SSTL12_DCI   [get_ports { c0_ddr4_adr[16] }] ; # Bank  64 VCCO - VCC1V2   - IO_L19P_T3L_N0_DBC_AD9P_64
set_property PACKAGE_PIN AH16     [get_ports { c0_ddr4_adr[0] }] ; # Bank  64 VCCO - VCC1V2   - IO_T2U_N12_64
set_property IOSTANDARD  SSTL12_DCI   [get_ports { c0_ddr4_adr[0] }] ; # Bank  64 VCCO - VCC1V2   - IO_T2U_N12_64
set_property PACKAGE_PIN AG14     [get_ports { c0_ddr4_adr[1] }] ; # Bank  64 VCCO - VCC1V2   - IO_L18N_T2U_N11_AD2N_64
set_property IOSTANDARD  SSTL12_DCI   [get_ports { c0_ddr4_adr[1] }] ; # Bank  64 VCCO - VCC1V2   - IO_L18N_T2U_N11_AD2N_64
set_property PACKAGE_PIN AG15     [get_ports { c0_ddr4_adr[2] }] ; # Bank  64 VCCO - VCC1V2   - IO_L18P_T2U_N10_AD2P_64
set_property IOSTANDARD  SSTL12_DCI   [get_ports { c0_ddr4_adr[2] }] ; # Bank  64 VCCO - VCC1V2   - IO_L18P_T2U_N10_AD2P_64
set_property PACKAGE_PIN AF15     [get_ports { c0_ddr4_adr[3] }] ; # Bank  64 VCCO - VCC1V2   - IO_L17N_T2U_N9_AD10N_64
set_property IOSTANDARD  SSTL12_DCI   [get_ports { c0_ddr4_adr[3] }] ; # Bank  64 VCCO - VCC1V2   - IO_L17N_T2U_N9_AD10N_64
set_property PACKAGE_PIN AF16     [get_ports { c0_ddr4_adr[4] }] ; # Bank  64 VCCO - VCC1V2   - IO_L17P_T2U_N8_AD10P_64
set_property IOSTANDARD  SSTL12_DCI   [get_ports { c0_ddr4_adr[4] }] ; # Bank  64 VCCO - VCC1V2   - IO_L17P_T2U_N8_AD10P_64
set_property PACKAGE_PIN AJ14     [get_ports { c0_ddr4_adr[5] }] ; # Bank  64 VCCO - VCC1V2   - IO_L16N_T2U_N7_QBC_AD3N_64
set_property IOSTANDARD  SSTL12_DCI   [get_ports { c0_ddr4_adr[5] }] ; # Bank  64 VCCO - VCC1V2   - IO_L16N_T2U_N7_QBC_AD3N_64
set_property PACKAGE_PIN AH14     [get_ports { c0_ddr4_adr[6] }] ; # Bank  64 VCCO - VCC1V2   - IO_L16P_T2U_N6_QBC_AD3P_64
set_property IOSTANDARD  SSTL12_DCI   [get_ports { c0_ddr4_adr[6] }] ; # Bank  64 VCCO - VCC1V2   - IO_L16P_T2U_N6_QBC_AD3P_64
set_property PACKAGE_PIN AF17     [get_ports { c0_ddr4_adr[7] }] ; # Bank  64 VCCO - VCC1V2   - IO_L15N_T2L_N5_AD11N_64
set_property IOSTANDARD  SSTL12_DCI   [get_ports { c0_ddr4_adr[7] }] ; # Bank  64 VCCO - VCC1V2   - IO_L15N_T2L_N5_AD11N_64
set_property PACKAGE_PIN AG18     [get_ports { c0_ddr4_ck_c }] ; # Bank  64 VCCO - VCC1V2   - IO_L14N_T2L_N3_GC_64
set_property IOSTANDARD  DIFF_SSTL12_DCI [get_ports { c0_ddr4_ck_c }] ; # Bank  64 VCCO - VCC1V2   - IO_L14N_T2L_N3_GC_64
set_property PACKAGE_PIN AF18     [get_ports { c0_ddr4_ck_t }] ; # Bank  64 VCCO - VCC1V2   - IO_L14P_T2L_N2_GC_64
set_property IOSTANDARD  DIFF_SSTL12_DCI [get_ports { c0_ddr4_ck_t }] ; # Bank  64 VCCO - VCC1V2   - IO_L14P_T2L_N2_GC_64
#set_property PACKAGE_PIN AJ15     [get_ports { c0_ddr4_CK1_C }] ; # Bank  64 VCCO - VCC1V2   - IO_L12N_T1U_N11_GC_64
#set_property IOSTANDARD  DIFF_POD12_DCI [get_ports { c0_ddr4_CK1_C }] ; # Bank  64 VCCO - VCC1V2   - IO_L12N_T1U_N11_GC_64
#set_property PACKAGE_PIN AJ16     [get_ports { c0_ddr4_CK1_T }] ; # Bank  64 VCCO - VCC1V2   - IO_L12P_T1U_N10_GC_64
#set_property IOSTANDARD  DIFF_POD12_DCI [get_ports { c0_ddr4_CK1_T }] ; # Bank  64 VCCO - VCC1V2   - IO_L12P_T1U_N10_GC_64
set_property PACKAGE_PIN AK17     [get_ports { c0_ddr4_adr[8] }] ; # Bank  64 VCCO - VCC1V2   - IO_L11N_T1U_N9_GC_64
set_property IOSTANDARD  SSTL12_DCI   [get_ports { c0_ddr4_adr[8] }] ; # Bank  64 VCCO - VCC1V2   - IO_L11N_T1U_N9_GC_64
set_property PACKAGE_PIN AJ17     [get_ports { c0_ddr4_adr[9] }] ; # Bank  64 VCCO - VCC1V2   - IO_L11P_T1U_N8_GC_64
set_property IOSTANDARD  SSTL12_DCI   [get_ports { c0_ddr4_adr[9] }] ; # Bank  64 VCCO - VCC1V2   - IO_L11P_T1U_N8_GC_64
set_property PACKAGE_PIN AK14     [get_ports { c0_ddr4_adr[10] }] ; # Bank  64 VCCO - VCC1V2   - IO_L10N_T1U_N7_QBC_AD4N_64
set_property IOSTANDARD  SSTL12_DCI   [get_ports { c0_ddr4_adr[10] }] ; # Bank  64 VCCO - VCC1V2   - IO_L10N_T1U_N7_QBC_AD4N_64
set_property PACKAGE_PIN AK15     [get_ports { c0_ddr4_adr[11] }] ; # Bank  64 VCCO - VCC1V2   - IO_L10P_T1U_N6_QBC_AD4P_64
set_property IOSTANDARD  SSTL12_DCI   [get_ports { c0_ddr4_adr[11] }] ; # Bank  64 VCCO - VCC1V2   - IO_L10P_T1U_N6_QBC_AD4P_64
set_property PACKAGE_PIN AL18     [get_ports { c0_ddr4_adr[12] }] ; # Bank  64 VCCO - VCC1V2   - IO_L9N_T1L_N5_AD12N_64
set_property IOSTANDARD  SSTL12_DCI   [get_ports { c0_ddr4_adr[12] }] ; # Bank  64 VCCO - VCC1V2   - IO_L9N_T1L_N5_AD12N_64
set_property PACKAGE_PIN AK18     [get_ports { c0_ddr4_adr[13] }] ; # Bank  64 VCCO - VCC1V2   - IO_L9P_T1L_N4_AD12P_64
set_property IOSTANDARD  SSTL12_DCI   [get_ports { c0_ddr4_adr[13] }] ; # Bank  64 VCCO - VCC1V2   - IO_L9P_T1L_N4_AD12P_64
set_property PACKAGE_PIN AL15     [get_ports { c0_ddr4_ba[0] }] ; # Bank  64 VCCO - VCC1V2   - IO_L8N_T1L_N3_AD5N_64
set_property IOSTANDARD  SSTL12_DCI   [get_ports { c0_ddr4_ba[0] }] ; # Bank  64 VCCO - VCC1V2   - IO_L8N_T1L_N3_AD5N_64
set_property PACKAGE_PIN AL16     [get_ports { c0_ddr4_ba[1] }] ; # Bank  64 VCCO - VCC1V2   - IO_L8P_T1L_N2_AD5P_64
set_property IOSTANDARD  SSTL12_DCI   [get_ports { c0_ddr4_ba[1] }] ; # Bank  64 VCCO - VCC1V2   - IO_L8P_T1L_N2_AD5P_64
#set_property PACKAGE_PIN AM15     [get_ports { c0_ddr4_CKE1 }] ; # Bank  64 VCCO - VCC1V2   - IO_L7N_T1L_N1_QBC_AD13N_64
#set_property IOSTANDARD  SSTL12_DCI   [get_ports { c0_ddr4_CKE1 }] ; # Bank  64 VCCO - VCC1V2   - IO_L7N_T1L_N1_QBC_AD13N_64
#set_property PACKAGE_PIN AM16     [get_ports { c0_ddr4_ODT1 }] ; # Bank  64 VCCO - VCC1V2   - IO_L7P_T1L_N0_QBC_AD13P_64
#set_property IOSTANDARD  SSTL12_DCI   [get_ports { c0_ddr4_ODT1 }] ; # Bank  64 VCCO - VCC1V2   - IO_L7P_T1L_N0_QBC_AD13P_64
#set_property PACKAGE_PIN AL17     [get_ports { c0_ddr4_CS1_B }] ; # Bank  64 VCCO - VCC1V2   - IO_T1U_N12_64
#set_property IOSTANDARD  SSTL12_DCI   [get_ports { c0_ddr4_CS1_B }] ; # Bank  64 VCCO - VCC1V2   - IO_T1U_N12_64

## Default xdc configuration
#Other net   PACKAGE_PIN V17      - SYSMON_DXN                Bank   0 - DXN
#Other net   PACKAGE_PIN V18      - SYSMON_DXP                Bank   0 - DXP
#Other net   PACKAGE_PIN R17      - SYSMON_AGND               Bank   0 - GNDADC
#Other net   PACKAGE_PIN AA12     - 3N5824                    Bank   0 - POR_OVERRIDE
#Other net   PACKAGE_PIN AA13     - 3N5822                    Bank   0 - PUDC_B
#Other net   PACKAGE_PIN R18      - FPGA_SYSMON_AVCC          Bank   0 - VCCADC
#Other net   PACKAGE_PIN U17      - SYSMON_VN_R               Bank   0 - VN
#Other net   PACKAGE_PIN T18      - SYSMON_VP_R               Bank   0 - VP
#Other net   PACKAGE_PIN T17      - SYSMON_AGND               Bank   0 - VREFN
#Other net   PACKAGE_PIN U18      - SYSMON_AGND               Bank   0 - VREFP
#set_property PACKAGE_PIN B21      [get_ports "5N7582"] ;# Bank  28 VCCO - VCC1V8   - IO_L24N_T3U_N11_28
#set_property IOSTANDARD  LVCMOSxx [get_ports "5N7582"] ;# Bank  28 VCCO - VCC1V8   - IO_L24N_T3U_N11_28
#set_property PACKAGE_PIN B20      [get_ports "5N7577"] ;# Bank  28 VCCO - VCC1V8   - IO_L24P_T3U_N10_28
#set_property IOSTANDARD  LVCMOSxx [get_ports "5N7577"] ;# Bank  28 VCCO - VCC1V8   - IO_L24P_T3U_N10_28
#set_property PACKAGE_PIN A23      [get_ports "5N7578"] ;# Bank  28 VCCO - VCC1V8   - IO_L23N_T3U_N9_28
#set_property IOSTANDARD  LVCMOSxx [get_ports "5N7578"] ;# Bank  28 VCCO - VCC1V8   - IO_L23N_T3U_N9_28
#set_property PACKAGE_PIN A22      [get_ports "5N7569"] ;# Bank  28 VCCO - VCC1V8   - IO_L23P_T3U_N8_28
#set_property IOSTANDARD  LVCMOSxx [get_ports "5N7569"] ;# Bank  28 VCCO - VCC1V8   - IO_L23P_T3U_N8_28
#set_property PACKAGE_PIN B19      [get_ports "5N7570"] ;# Bank  28 VCCO - VCC1V8   - IO_L22N_T3U_N7_DBC_AD0N_28
#set_property IOSTANDARD  LVCMOSxx [get_ports "5N7570"] ;# Bank  28 VCCO - VCC1V8   - IO_L22N_T3U_N7_DBC_AD0N_28
#set_property PACKAGE_PIN B18      [get_ports "5N7565"] ;# Bank  28 VCCO - VCC1V8   - IO_L22P_T3U_N6_DBC_AD0P_28
#set_property IOSTANDARD  LVCMOSxx [get_ports "5N7565"] ;# Bank  28 VCCO - VCC1V8   - IO_L22P_T3U_N6_DBC_AD0P_28
#set_property PACKAGE_PIN A21      [get_ports "5N7709"] ;# Bank  28 VCCO - VCC1V8   - IO_L21N_T3L_N5_AD8N_28
#set_property IOSTANDARD  LVCMOSxx [get_ports "5N7709"] ;# Bank  28 VCCO - VCC1V8   - IO_L21N_T3L_N5_AD8N_28
#set_property PACKAGE_PIN A20      [get_ports "UART2_TXD_FPGA_RXD"] ;# Bank  28 VCCO - VCC1V8   - IO_L21P_T3L_N4_AD8P_28
#set_property IOSTANDARD  LVCMOS18 [get_ports "UART2_TXD_FPGA_RXD"] ;# Bank  28 VCCO - VCC1V8   - IO_L21P_T3L_N4_AD8P_28
#set_property PACKAGE_PIN C19      [get_ports "UART2_RXD_FPGA_TXD"] ;# Bank  28 VCCO - VCC1V8   - IO_L20N_T3L_N3_AD1N_28
#set_property IOSTANDARD  LVCMOS18 [get_ports "UART2_RXD_FPGA_TXD"] ;# Bank  28 VCCO - VCC1V8   - IO_L20N_T3L_N3_AD1N_28
#set_property PACKAGE_PIN C18      [get_ports "UART2_RTS_B"] ;# Bank  28 VCCO - VCC1V8   - IO_L20P_T3L_N2_AD1P_28
#set_property IOSTANDARD  LVCMOS18 [get_ports "UART2_RTS_B"] ;# Bank  28 VCCO - VCC1V8   - IO_L20P_T3L_N2_AD1P_28
#set_property PACKAGE_PIN A19      [get_ports "UART2_CTS_B"] ;# Bank  28 VCCO - VCC1V8   - IO_L19N_T3L_N1_DBC_AD9N_28
#set_property IOSTANDARD  LVCMOS18 [get_ports "UART2_CTS_B"] ;# Bank  28 VCCO - VCC1V8   - IO_L19N_T3L_N1_DBC_AD9N_28
#set_property PACKAGE_PIN A18      [get_ports "5N7704"] ;# Bank  28 VCCO - VCC1V8   - IO_L19P_T3L_N0_DBC_AD9P_28
#set_property IOSTANDARD  LVCMOSxx [get_ports "5N7704"] ;# Bank  28 VCCO - VCC1V8   - IO_L19P_T3L_N0_DBC_AD9P_28
#set_property PACKAGE_PIN B23      [get_ports "5N7581"] ;# Bank  28 VCCO - VCC1V8   - IO_T3U_N12_28
#set_property IOSTANDARD  LVCMOSxx [get_ports "5N7581"] ;# Bank  28 VCCO - VCC1V8   - IO_T3U_N12_28
#set_property PACKAGE_PIN F25      [get_ports "5N7703"] ;# Bank  28 VCCO - VCC1V8   - IO_T2U_N12_28
#set_property IOSTANDARD  LVCMOSxx [get_ports "5N7703"] ;# Bank  28 VCCO - VCC1V8   - IO_T2U_N12_28
#set_property PACKAGE_PIN G26      [get_ports "5N7702"] ;# Bank  28 VCCO - VCC1V8   - IO_L18N_T2U_N11_AD2N_28
#set_property IOSTANDARD  LVCMOSxx [get_ports "5N7702"] ;# Bank  28 VCCO - VCC1V8   - IO_L18N_T2U_N11_AD2N_28
#set_property PACKAGE_PIN G25      [get_ports "5N7694"] ;# Bank  28 VCCO - VCC1V8   - IO_L18P_T2U_N10_AD2P_28
#set_property IOSTANDARD  LVCMOSxx [get_ports "5N7694"] ;# Bank  28 VCCO - VCC1V8   - IO_L18P_T2U_N10_AD2P_28
#set_property PACKAGE_PIN C23      [get_ports "5N7693"] ;# Bank  28 VCCO - VCC1V8   - IO_L17N_T2U_N9_AD10N_28
#set_property IOSTANDARD  LVCMOSxx [get_ports "5N7693"] ;# Bank  28 VCCO - VCC1V8   - IO_L17N_T2U_N9_AD10N_28
#set_property PACKAGE_PIN D22      [get_ports "5N7690"] ;# Bank  28 VCCO - VCC1V8   - IO_L17P_T2U_N8_AD10P_28
#set_property IOSTANDARD  LVCMOSxx [get_ports "5N7690"] ;# Bank  28 VCCO - VCC1V8   - IO_L17P_T2U_N8_AD10P_28
#set_property PACKAGE_PIN D24      [get_ports "5N7688"] ;# Bank  28 VCCO - VCC1V8   - IO_L16N_T2U_N7_QBC_AD3N_28
#set_property IOSTANDARD  LVCMOSxx [get_ports "5N7688"] ;# Bank  28 VCCO - VCC1V8   - IO_L16N_T2U_N7_QBC_AD3N_28
#set_property PACKAGE_PIN E24      [get_ports "5N7682"] ;# Bank  28 VCCO - VCC1V8   - IO_L16P_T2U_N6_QBC_AD3P_28
#set_property IOSTANDARD  LVCMOSxx [get_ports "5N7682"] ;# Bank  28 VCCO - VCC1V8   - IO_L16P_T2U_N6_QBC_AD3P_28
#set_property PACKAGE_PIN C22      [get_ports "5N7681"] ;# Bank  28 VCCO - VCC1V8   - IO_L15N_T2L_N5_AD11N_28
#set_property IOSTANDARD  LVCMOSxx [get_ports "5N7681"] ;# Bank  28 VCCO - VCC1V8   - IO_L15N_T2L_N5_AD11N_28
#set_property PACKAGE_PIN C21      [get_ports "5N7678"] ;# Bank  28 VCCO - VCC1V8   - IO_L15P_T2L_N4_AD11P_28
#set_property IOSTANDARD  LVCMOSxx [get_ports "5N7678"] ;# Bank  28 VCCO - VCC1V8   - IO_L15P_T2L_N4_AD11P_28
#set_property PACKAGE_PIN G24      [get_ports "5N7676"] ;# Bank  28 VCCO - VCC1V8   - IO_L14N_T2L_N3_GC_28
#set_property IOSTANDARD  LVCMOSxx [get_ports "5N7676"] ;# Bank  28 VCCO - VCC1V8   - IO_L14N_T2L_N3_GC_28
#set_property PACKAGE_PIN G23      [get_ports "5N7672"] ;# Bank  28 VCCO - VCC1V8   - IO_L14P_T2L_N2_GC_28
#set_property IOSTANDARD  LVCMOSxx [get_ports "5N7672"] ;# Bank  28 VCCO - VCC1V8   - IO_L14P_T2L_N2_GC_28
#set_property PACKAGE_PIN E23      [get_ports "CLK_125_N"] ;# Bank  28 VCCO - VCC1V8   - IO_L13N_T2L_N1_GC_QBC_28
#set_property IOSTANDARD  LVDS     [get_ports "CLK_125_N"] ;# Bank  28 VCCO - VCC1V8   - IO_L13N_T2L_N1_GC_QBC_28
#set_property PACKAGE_PIN F23      [get_ports "CLK_125_P"] ;# Bank  28 VCCO - VCC1V8   - IO_L13P_T2L_N0_GC_QBC_28
#set_property IOSTANDARD  LVDS     [get_ports "CLK_125_P"] ;# Bank  28 VCCO - VCC1V8   - IO_L13P_T2L_N0_GC_QBC_28
#set_property PACKAGE_PIN F21      [get_ports "HDMI_TX_LVDS_OUT_N"] ;# Bank  28 VCCO - VCC1V8   - IO_L12N_T1U_N11_GC_28
#set_property IOSTANDARD  LVDS     [get_ports "HDMI_TX_LVDS_OUT_N"] ;# Bank  28 VCCO - VCC1V8   - IO_L12N_T1U_N11_GC_28
#set_property PACKAGE_PIN G21      [get_ports "HDMI_TX_LVDS_OUT_P"] ;# Bank  28 VCCO - VCC1V8   - IO_L12P_T1U_N10_GC_28
#set_property IOSTANDARD  LVDS     [get_ports "HDMI_TX_LVDS_OUT_P"] ;# Bank  28 VCCO - VCC1V8   - IO_L12P_T1U_N10_GC_28
#set_property PACKAGE_PIN E22      [get_ports "HDMI_REC_CLOCK_N"] ;# Bank  28 VCCO - VCC1V8   - IO_L11N_T1U_N9_GC_28
#set_property IOSTANDARD  LVDS     [get_ports "HDMI_REC_CLOCK_N"] ;# Bank  28 VCCO - VCC1V8   - IO_L11N_T1U_N9_GC_28
#set_property PACKAGE_PIN F22      [get_ports "HDMI_REC_CLOCK_P"] ;# Bank  28 VCCO - VCC1V8   - IO_L11P_T1U_N8_GC_28
#set_property IOSTANDARD  LVDS     [get_ports "HDMI_REC_CLOCK_P"] ;# Bank  28 VCCO - VCC1V8   - IO_L11P_T1U_N8_GC_28
#set_property PACKAGE_PIN F20      [get_ports "5N7532"] ;# Bank  28 VCCO - VCC1V8   - IO_L10N_T1U_N7_QBC_AD4N_28
#set_property IOSTANDARD  LVCMOSxx [get_ports "5N7532"] ;# Bank  28 VCCO - VCC1V8   - IO_L10N_T1U_N7_QBC_AD4N_28
#set_property PACKAGE_PIN G20      [get_ports "5N7533"] ;# Bank  28 VCCO - VCC1V8   - IO_L10P_T1U_N6_QBC_AD4P_28
#set_property IOSTANDARD  LVCMOSxx [get_ports "5N7533"] ;# Bank  28 VCCO - VCC1V8   - IO_L10P_T1U_N6_QBC_AD4P_28
#set_property PACKAGE_PIN D21      [get_ports "5N7524"] ;# Bank  28 VCCO - VCC1V8   - IO_L9N_T1L_N5_AD12N_28
#set_property IOSTANDARD  LVCMOSxx [get_ports "5N7524"] ;# Bank  28 VCCO - VCC1V8   - IO_L9N_T1L_N5_AD12N_28
#set_property PACKAGE_PIN D20      [get_ports "5N7525"] ;# Bank  28 VCCO - VCC1V8   - IO_L9P_T1L_N4_AD12P_28
#set_property IOSTANDARD  LVCMOSxx [get_ports "5N7525"] ;# Bank  28 VCCO - VCC1V8   - IO_L9P_T1L_N4_AD12P_28
#set_property PACKAGE_PIN H22      [get_ports "5N7520"] ;# Bank  28 VCCO - VCC1V8   - IO_L8N_T1L_N3_AD5N_28
#set_property IOSTANDARD  LVCMOSxx [get_ports "5N7520"] ;# Bank  28 VCCO - VCC1V8   - IO_L8N_T1L_N3_AD5N_28
#set_property PACKAGE_PIN H21      [get_ports "5N7521"] ;# Bank  28 VCCO - VCC1V8   - IO_L8P_T1L_N2_AD5P_28
#set_property IOSTANDARD  LVCMOSxx [get_ports "5N7521"] ;# Bank  28 VCCO - VCC1V8   - IO_L8P_T1L_N2_AD5P_28
#set_property PACKAGE_PIN D19      [get_ports "5N7512"] ;# Bank  28 VCCO - VCC1V8   - IO_L7N_T1L_N1_QBC_AD13N_28
#set_property IOSTANDARD  LVCMOSxx [get_ports "5N7512"] ;# Bank  28 VCCO - VCC1V8   - IO_L7N_T1L_N1_QBC_AD13N_28
#set_property PACKAGE_PIN E19      [get_ports "5N7513"] ;# Bank  28 VCCO - VCC1V8   - IO_L7P_T1L_N0_QBC_AD13P_28
#set_property IOSTANDARD  LVCMOSxx [get_ports "5N7513"] ;# Bank  28 VCCO - VCC1V8   - IO_L7P_T1L_N0_QBC_AD13P_28
#set_property PACKAGE_PIN E20      [get_ports "5N7726"] ;# Bank  28 VCCO - VCC1V8   - IO_T1U_N12_28
#set_property IOSTANDARD  LVCMOSxx [get_ports "5N7726"] ;# Bank  28 VCCO - VCC1V8   - IO_T1U_N12_28
#set_property PACKAGE_PIN H23      [get_ports "5N7508"] ;# Bank  28 VCCO - VCC1V8   - IO_T0U_N12_VRP_28
#set_property IOSTANDARD  LVCMOSxx [get_ports "5N7508"] ;# Bank  28 VCCO - VCC1V8   - IO_T0U_N12_VRP_28
#set_property PACKAGE_PIN H24      [get_ports "5N7509"] ;# Bank  28 VCCO - VCC1V8   - IO_L6N_T0U_N11_AD6N_28
#set_property IOSTANDARD  LVCMOSxx [get_ports "5N7509"] ;# Bank  28 VCCO - VCC1V8   - IO_L6N_T0U_N11_AD6N_28
#set_property PACKAGE_PIN J24      [get_ports "5N7500"] ;# Bank  28 VCCO - VCC1V8   - IO_L6P_T0U_N10_AD6P_28
#set_property IOSTANDARD  LVCMOSxx [get_ports "5N7500"] ;# Bank  28 VCCO - VCC1V8   - IO_L6P_T0U_N10_AD6P_28
#set_property PACKAGE_PIN H26      [get_ports "5N7501"] ;# Bank  28 VCCO - VCC1V8   - IO_L5N_T0U_N9_AD14N_28
#set_property IOSTANDARD  LVCMOSxx [get_ports "5N7501"] ;# Bank  28 VCCO - VCC1V8   - IO_L5N_T0U_N9_AD14N_28
#set_property PACKAGE_PIN J25      [get_ports "5N7496"] ;# Bank  28 VCCO - VCC1V8   - IO_L5P_T0U_N8_AD14P_28
#set_property IOSTANDARD  LVCMOSxx [get_ports "5N7496"] ;# Bank  28 VCCO - VCC1V8   - IO_L5P_T0U_N8_AD14P_28
#set_property PACKAGE_PIN K23      [get_ports "5N7497"] ;# Bank  28 VCCO - VCC1V8   - IO_L4N_T0U_N7_DBC_AD7N_28
#set_property IOSTANDARD  LVCMOSxx [get_ports "5N7497"] ;# Bank  28 VCCO - VCC1V8   - IO_L4N_T0U_N7_DBC_AD7N_28
#set_property PACKAGE_PIN K22      [get_ports "5N7488"] ;# Bank  28 VCCO - VCC1V8   - IO_L4P_T0U_N6_DBC_AD7P_28
#set_property IOSTANDARD  LVCMOSxx [get_ports "5N7488"] ;# Bank  28 VCCO - VCC1V8   - IO_L4P_T0U_N6_DBC_AD7P_28
#set_property PACKAGE_PIN J22      [get_ports "5N7489"] ;# Bank  28 VCCO - VCC1V8   - IO_L3N_T0L_N5_AD15N_28
#set_property IOSTANDARD  LVCMOSxx [get_ports "5N7489"] ;# Bank  28 VCCO - VCC1V8   - IO_L3N_T0L_N5_AD15N_28
#set_property PACKAGE_PIN J21      [get_ports "5N7484"] ;# Bank  28 VCCO - VCC1V8   - IO_L3P_T0L_N4_AD15P_28
#set_property IOSTANDARD  LVCMOSxx [get_ports "5N7484"] ;# Bank  28 VCCO - VCC1V8   - IO_L3P_T0L_N4_AD15P_28
#set_property PACKAGE_PIN K24      [get_ports "5N7485"] ;# Bank  28 VCCO - VCC1V8   - IO_L2N_T0L_N3_28
#set_property IOSTANDARD  LVCMOSxx [get_ports "5N7485"] ;# Bank  28 VCCO - VCC1V8   - IO_L2N_T0L_N3_28
#set_property PACKAGE_PIN L23      [get_ports "5N7476"] ;# Bank  28 VCCO - VCC1V8   - IO_L2P_T0L_N2_28
#set_property IOSTANDARD  LVCMOSxx [get_ports "5N7476"] ;# Bank  28 VCCO - VCC1V8   - IO_L2P_T0L_N2_28
#set_property PACKAGE_PIN L22      [get_ports "5N7477"] ;# Bank  28 VCCO - VCC1V8   - IO_L1N_T0L_N1_DBC_28
#set_property IOSTANDARD  LVCMOSxx [get_ports "5N7477"] ;# Bank  28 VCCO - VCC1V8   - IO_L1N_T0L_N1_DBC_28
#set_property PACKAGE_PIN L21      [get_ports "5N7472"] ;# Bank  28 VCCO - VCC1V8   - IO_L1P_T0L_N0_DBC_28
#set_property IOSTANDARD  LVCMOSxx [get_ports "5N7472"] ;# Bank  28 VCCO - VCC1V8   - IO_L1P_T0L_N0_DBC_28
#Other net   PACKAGE_PIN M23      - 5N7631                    Bank  28 - VREF_28
#set_property PACKAGE_PIN A11      [get_ports "FMC_LPC_LA23_N"] ;# Bank  68 VCCO - VADJ_FMC - IO_L24N_T3U_N11_68
#set_property IOSTANDARD  LVDS     [get_ports "FMC_LPC_LA23_N"] ;# Bank  68 VCCO - VADJ_FMC - IO_L24N_T3U_N11_68
#set_property PACKAGE_PIN B11      [get_ports "FMC_LPC_LA23_P"] ;# Bank  68 VCCO - VADJ_FMC - IO_L24P_T3U_N10_68
#set_property IOSTANDARD  LVDS     [get_ports "FMC_LPC_LA23_P"] ;# Bank  68 VCCO - VADJ_FMC - IO_L24P_T3U_N10_68
#set_property PACKAGE_PIN A7       [get_ports "FMC_LPC_LA27_N"] ;# Bank  68 VCCO - VADJ_FMC - IO_L23N_T3U_N9_68
#set_property IOSTANDARD  LVDS     [get_ports "FMC_LPC_LA27_N"] ;# Bank  68 VCCO - VADJ_FMC - IO_L23N_T3U_N9_68
#set_property PACKAGE_PIN A8       [get_ports "FMC_LPC_LA27_P"] ;# Bank  68 VCCO - VADJ_FMC - IO_L23P_T3U_N8_68
#set_property IOSTANDARD  LVDS     [get_ports "FMC_LPC_LA27_P"] ;# Bank  68 VCCO - VADJ_FMC - IO_L23P_T3U_N8_68
#set_property PACKAGE_PIN A10      [get_ports "FMC_LPC_LA21_N"] ;# Bank  68 VCCO - VADJ_FMC - IO_L22N_T3U_N7_DBC_AD0N_68
#set_property IOSTANDARD  LVDS     [get_ports "FMC_LPC_LA21_N"] ;# Bank  68 VCCO - VADJ_FMC - IO_L22N_T3U_N7_DBC_AD0N_68
#set_property PACKAGE_PIN B10      [get_ports "FMC_LPC_LA21_P"] ;# Bank  68 VCCO - VADJ_FMC - IO_L22P_T3U_N6_DBC_AD0P_68
#set_property IOSTANDARD  LVDS     [get_ports "FMC_LPC_LA21_P"] ;# Bank  68 VCCO - VADJ_FMC - IO_L22P_T3U_N6_DBC_AD0P_68
#set_property PACKAGE_PIN A6       [get_ports "FMC_LPC_LA24_N"] ;# Bank  68 VCCO - VADJ_FMC - IO_L21N_T3L_N5_AD8N_68
#set_property IOSTANDARD  LVDS     [get_ports "FMC_LPC_LA24_N"] ;# Bank  68 VCCO - VADJ_FMC - IO_L21N_T3L_N5_AD8N_68
#set_property PACKAGE_PIN B6       [get_ports "FMC_LPC_LA24_P"] ;# Bank  68 VCCO - VADJ_FMC - IO_L21P_T3L_N4_AD8P_68
#set_property IOSTANDARD  LVDS     [get_ports "FMC_LPC_LA24_P"] ;# Bank  68 VCCO - VADJ_FMC - IO_L21P_T3L_N4_AD8P_68
#set_property PACKAGE_PIN B8       [get_ports "FMC_LPC_LA26_N"] ;# Bank  68 VCCO - VADJ_FMC - IO_L20N_T3L_N3_AD1N_68
#set_property IOSTANDARD  LVDS     [get_ports "FMC_LPC_LA26_N"] ;# Bank  68 VCCO - VADJ_FMC - IO_L20N_T3L_N3_AD1N_68
#set_property PACKAGE_PIN B9       [get_ports "FMC_LPC_LA26_P"] ;# Bank  68 VCCO - VADJ_FMC - IO_L20P_T3L_N2_AD1P_68
#set_property IOSTANDARD  LVDS     [get_ports "FMC_LPC_LA26_P"] ;# Bank  68 VCCO - VADJ_FMC - IO_L20P_T3L_N2_AD1P_68
#set_property PACKAGE_PIN C6       [get_ports "FMC_LPC_LA25_N"] ;# Bank  68 VCCO - VADJ_FMC - IO_L19N_T3L_N1_DBC_AD9N_68
#set_property IOSTANDARD  LVDS     [get_ports "FMC_LPC_LA25_N"] ;# Bank  68 VCCO - VADJ_FMC - IO_L19N_T3L_N1_DBC_AD9N_68
#set_property PACKAGE_PIN C7       [get_ports "FMC_LPC_LA25_P"] ;# Bank  68 VCCO - VADJ_FMC - IO_L19P_T3L_N0_DBC_AD9P_68
#set_property IOSTANDARD  LVDS     [get_ports "FMC_LPC_LA25_P"] ;# Bank  68 VCCO - VADJ_FMC - IO_L19P_T3L_N0_DBC_AD9P_68
#set_property PACKAGE_PIN A9       [get_ports "4N9784"] ;# Bank  68 VCCO - VADJ_FMC - IO_T3U_N12_68
#set_property IOSTANDARD  LVCMOSxx [get_ports "4N9784"] ;# Bank  68 VCCO - VADJ_FMC - IO_T3U_N12_68
#set_property PACKAGE_PIN G13      [get_ports "4N9781"] ;# Bank  68 VCCO - VADJ_FMC - IO_T2U_N12_68
#set_property IOSTANDARD  LVCMOSxx [get_ports "4N9781"] ;# Bank  68 VCCO - VADJ_FMC - IO_T2U_N12_68
#set_property PACKAGE_PIN C11      [get_ports "FMC_LPC_LA19_N"] ;# Bank  68 VCCO - VADJ_FMC - IO_L18N_T2U_N11_AD2N_68
#set_property IOSTANDARD  LVDS     [get_ports "FMC_LPC_LA19_N"] ;# Bank  68 VCCO - VADJ_FMC - IO_L18N_T2U_N11_AD2N_68
#set_property PACKAGE_PIN D12      [get_ports "FMC_LPC_LA19_P"] ;# Bank  68 VCCO - VADJ_FMC - IO_L18P_T2U_N10_AD2P_68
#set_property IOSTANDARD  LVDS     [get_ports "FMC_LPC_LA19_P"] ;# Bank  68 VCCO - VADJ_FMC - IO_L18P_T2U_N10_AD2P_68
#set_property PACKAGE_PIN E12      [get_ports "FMC_LPC_LA20_N"] ;# Bank  68 VCCO - VADJ_FMC - IO_L17N_T2U_N9_AD10N_68
#set_property IOSTANDARD  LVDS     [get_ports "FMC_LPC_LA20_N"] ;# Bank  68 VCCO - VADJ_FMC - IO_L17N_T2U_N9_AD10N_68
#set_property PACKAGE_PIN F12      [get_ports "FMC_LPC_LA20_P"] ;# Bank  68 VCCO - VADJ_FMC - IO_L17P_T2U_N8_AD10P_68
#set_property IOSTANDARD  LVDS     [get_ports "FMC_LPC_LA20_P"] ;# Bank  68 VCCO - VADJ_FMC - IO_L17P_T2U_N8_AD10P_68
#set_property PACKAGE_PIN D10      [get_ports "FMC_LPC_LA18_CC_N"] ;# Bank  68 VCCO - VADJ_FMC - IO_L16N_T2U_N7_QBC_AD3N_68
#set_property IOSTANDARD  LVDS     [get_ports "FMC_LPC_LA18_CC_N"] ;# Bank  68 VCCO - VADJ_FMC - IO_L16N_T2U_N7_QBC_AD3N_68
#set_property PACKAGE_PIN D11      [get_ports "FMC_LPC_LA18_CC_P"] ;# Bank  68 VCCO - VADJ_FMC - IO_L16P_T2U_N6_QBC_AD3P_68
#set_property IOSTANDARD  LVDS     [get_ports "FMC_LPC_LA18_CC_P"] ;# Bank  68 VCCO - VADJ_FMC - IO_L16P_T2U_N6_QBC_AD3P_68
#set_property PACKAGE_PIN H12      [get_ports "FMC_LPC_LA22_N"] ;# Bank  68 VCCO - VADJ_FMC - IO_L15N_T2L_N5_AD11N_68
#set_property IOSTANDARD  LVDS     [get_ports "FMC_LPC_LA22_N"] ;# Bank  68 VCCO - VADJ_FMC - IO_L15N_T2L_N5_AD11N_68
#set_property PACKAGE_PIN H13      [get_ports "FMC_LPC_LA22_P"] ;# Bank  68 VCCO - VADJ_FMC - IO_L15P_T2L_N4_AD11P_68
#set_property IOSTANDARD  LVDS     [get_ports "FMC_LPC_LA22_P"] ;# Bank  68 VCCO - VADJ_FMC - IO_L15P_T2L_N4_AD11P_68
#set_property PACKAGE_PIN E10      [get_ports "FMC_LPC_LA17_CC_N"] ;# Bank  68 VCCO - VADJ_FMC - IO_L14N_T2L_N3_GC_68
#set_property IOSTANDARD  LVDS     [get_ports "FMC_LPC_LA17_CC_N"] ;# Bank  68 VCCO - VADJ_FMC - IO_L14N_T2L_N3_GC_68
#set_property PACKAGE_PIN F11      [get_ports "FMC_LPC_LA17_CC_P"] ;# Bank  68 VCCO - VADJ_FMC - IO_L14P_T2L_N2_GC_68
#set_property IOSTANDARD  LVDS     [get_ports "FMC_LPC_LA17_CC_P"] ;# Bank  68 VCCO - VADJ_FMC - IO_L14P_T2L_N2_GC_68
#set_property PACKAGE_PIN G11      [get_ports "4N9820"] ;# Bank  68 VCCO - VADJ_FMC - IO_L13N_T2L_N1_GC_QBC_68
#set_property IOSTANDARD  LVCMOSxx [get_ports "4N9820"] ;# Bank  68 VCCO - VADJ_FMC - IO_L13N_T2L_N1_GC_QBC_68
#set_property PACKAGE_PIN H11      [get_ports "4N9817"] ;# Bank  68 VCCO - VADJ_FMC - IO_L13P_T2L_N0_GC_QBC_68
#set_property IOSTANDARD  LVCMOSxx [get_ports "4N9817"] ;# Bank  68 VCCO - VADJ_FMC - IO_L13P_T2L_N0_GC_QBC_68
#set_property PACKAGE_PIN F10      [get_ports "FMC_LPC_CLK1_M2C_N"] ;# Bank  68 VCCO - VADJ_FMC - IO_L12N_T1U_N11_GC_68
#set_property IOSTANDARD  LVDS     [get_ports "FMC_LPC_CLK1_M2C_N"] ;# Bank  68 VCCO - VADJ_FMC - IO_L12N_T1U_N11_GC_68
#set_property PACKAGE_PIN G10      [get_ports "FMC_LPC_CLK1_M2C_P"] ;# Bank  68 VCCO - VADJ_FMC - IO_L12P_T1U_N10_GC_68
#set_property IOSTANDARD  LVDS     [get_ports "FMC_LPC_CLK1_M2C_P"] ;# Bank  68 VCCO - VADJ_FMC - IO_L12P_T1U_N10_GC_68
#set_property PACKAGE_PIN G9       [get_ports "4N9823"] ;# Bank  68 VCCO - VADJ_FMC - IO_L11N_T1U_N9_GC_68
#set_property IOSTANDARD  LVCMOSxx [get_ports "4N9823"] ;# Bank  68 VCCO - VADJ_FMC - IO_L11N_T1U_N9_GC_68
#set_property PACKAGE_PIN H9       [get_ports "4N9826"] ;# Bank  68 VCCO - VADJ_FMC - IO_L11P_T1U_N8_GC_68
#set_property IOSTANDARD  LVCMOSxx [get_ports "4N9826"] ;# Bank  68 VCCO - VADJ_FMC - IO_L11P_T1U_N8_GC_68
#set_property PACKAGE_PIN D9       [get_ports "FMC_LPC_LA30_N"] ;# Bank  68 VCCO - VADJ_FMC - IO_L10N_T1U_N7_QBC_AD4N_68
#set_property IOSTANDARD  LVDS     [get_ports "FMC_LPC_LA30_N"] ;# Bank  68 VCCO - VADJ_FMC - IO_L10N_T1U_N7_QBC_AD4N_68
#set_property PACKAGE_PIN E9       [get_ports "FMC_LPC_LA30_P"] ;# Bank  68 VCCO - VADJ_FMC - IO_L10P_T1U_N6_QBC_AD4P_68
#set_property IOSTANDARD  LVDS     [get_ports "FMC_LPC_LA30_P"] ;# Bank  68 VCCO - VADJ_FMC - IO_L10P_T1U_N6_QBC_AD4P_68
#set_property PACKAGE_PIN E8       [get_ports "FMC_LPC_LA32_N"] ;# Bank  68 VCCO - VADJ_FMC - IO_L9N_T1L_N5_AD12N_68
#set_property IOSTANDARD  LVDS     [get_ports "FMC_LPC_LA32_N"] ;# Bank  68 VCCO - VADJ_FMC - IO_L9N_T1L_N5_AD12N_68
#set_property PACKAGE_PIN F8       [get_ports "FMC_LPC_LA32_P"] ;# Bank  68 VCCO - VADJ_FMC - IO_L9P_T1L_N4_AD12P_68
#set_property IOSTANDARD  LVDS     [get_ports "FMC_LPC_LA32_P"] ;# Bank  68 VCCO - VADJ_FMC - IO_L9P_T1L_N4_AD12P_68
#set_property PACKAGE_PIN C8       [get_ports "FMC_LPC_LA33_N"] ;# Bank  68 VCCO - VADJ_FMC - IO_L8N_T1L_N3_AD5N_68
#set_property IOSTANDARD  LVDS     [get_ports "FMC_LPC_LA33_N"] ;# Bank  68 VCCO - VADJ_FMC - IO_L8N_T1L_N3_AD5N_68
#set_property PACKAGE_PIN C9       [get_ports "FMC_LPC_LA33_P"] ;# Bank  68 VCCO - VADJ_FMC - IO_L8P_T1L_N2_AD5P_68
#set_property IOSTANDARD  LVDS     [get_ports "FMC_LPC_LA33_P"] ;# Bank  68 VCCO - VADJ_FMC - IO_L8P_T1L_N2_AD5P_68
#set_property PACKAGE_PIN E7       [get_ports "FMC_LPC_LA31_N"] ;# Bank  68 VCCO - VADJ_FMC - IO_L7N_T1L_N1_QBC_AD13N_68
#set_property IOSTANDARD  LVDS     [get_ports "FMC_LPC_LA31_N"] ;# Bank  68 VCCO - VADJ_FMC - IO_L7N_T1L_N1_QBC_AD13N_68
#set_property PACKAGE_PIN F7       [get_ports "FMC_LPC_LA31_P"] ;# Bank  68 VCCO - VADJ_FMC - IO_L7P_T1L_N0_QBC_AD13P_68
#set_property IOSTANDARD  LVDS     [get_ports "FMC_LPC_LA31_P"] ;# Bank  68 VCCO - VADJ_FMC - IO_L7P_T1L_N0_QBC_AD13P_68
#set_property PACKAGE_PIN D7       [get_ports "4N9778"] ;# Bank  68 VCCO - VADJ_FMC - IO_T1U_N12_68
#set_property IOSTANDARD  LVCMOSxx [get_ports "4N9778"] ;# Bank  68 VCCO - VADJ_FMC - IO_T1U_N12_68
#set_property PACKAGE_PIN H14      [get_ports "VRP_68"] ;# Bank  68 VCCO - VADJ_FMC - IO_T0U_N12_VRP_68
#set_property IOSTANDARD  LVCMOSxx [get_ports "VRP_68"] ;# Bank  68 VCCO - VADJ_FMC - IO_T0U_N12_VRP_68
#set_property PACKAGE_PIN K13      [get_ports "4N9759"] ;# Bank  68 VCCO - VADJ_FMC - IO_L6N_T0U_N11_AD6N_68
#set_property IOSTANDARD  LVCMOSxx [get_ports "4N9759"] ;# Bank  68 VCCO - VADJ_FMC - IO_L6N_T0U_N11_AD6N_68
#set_property PACKAGE_PIN L14      [get_ports "4N9760"] ;# Bank  68 VCCO - VADJ_FMC - IO_L6P_T0U_N10_AD6P_68
#set_property IOSTANDARD  LVCMOSxx [get_ports "4N9760"] ;# Bank  68 VCCO - VADJ_FMC - IO_L6P_T0U_N10_AD6P_68
#set_property PACKAGE_PIN J14      [get_ports "4N9755"] ;# Bank  68 VCCO - VADJ_FMC - IO_L5N_T0U_N9_AD14N_68
#set_property IOSTANDARD  LVCMOSxx [get_ports "4N9755"] ;# Bank  68 VCCO - VADJ_FMC - IO_L5N_T0U_N9_AD14N_68
#set_property PACKAGE_PIN K14      [get_ports "4N9756"] ;# Bank  68 VCCO - VADJ_FMC - IO_L5P_T0U_N8_AD14P_68
#set_property IOSTANDARD  LVCMOSxx [get_ports "4N9756"] ;# Bank  68 VCCO - VADJ_FMC - IO_L5P_T0U_N8_AD14P_68
#set_property PACKAGE_PIN J11      [get_ports "4N9771"] ;# Bank  68 VCCO - VADJ_FMC - IO_L4N_T0U_N7_DBC_AD7N_68
#set_property IOSTANDARD  LVCMOSxx [get_ports "4N9771"] ;# Bank  68 VCCO - VADJ_FMC - IO_L4N_T0U_N7_DBC_AD7N_68
#set_property PACKAGE_PIN K12      [get_ports "4N9772"] ;# Bank  68 VCCO - VADJ_FMC - IO_L4P_T0U_N6_DBC_AD7P_68
#set_property IOSTANDARD  LVCMOSxx [get_ports "4N9772"] ;# Bank  68 VCCO - VADJ_FMC - IO_L4P_T0U_N6_DBC_AD7P_68
#set_property PACKAGE_PIN L11      [get_ports "4N9767"] ;# Bank  68 VCCO - VADJ_FMC - IO_L3N_T0L_N5_AD15N_68
#set_property IOSTANDARD  LVCMOSxx [get_ports "4N9767"] ;# Bank  68 VCCO - VADJ_FMC - IO_L3N_T0L_N5_AD15N_68
#set_property PACKAGE_PIN L12      [get_ports "4N9768"] ;# Bank  68 VCCO - VADJ_FMC - IO_L3P_T0L_N4_AD15P_68
#set_property IOSTANDARD  LVCMOSxx [get_ports "4N9768"] ;# Bank  68 VCCO - VADJ_FMC - IO_L3P_T0L_N4_AD15P_68
#set_property PACKAGE_PIN J10      [get_ports "FMC_LPC_LA29_N"] ;# Bank  68 VCCO - VADJ_FMC - IO_L2N_T0L_N3_68
#set_property IOSTANDARD  LVDS     [get_ports "FMC_LPC_LA29_N"] ;# Bank  68 VCCO - VADJ_FMC - IO_L2N_T0L_N3_68
#set_property PACKAGE_PIN K10      [get_ports "FMC_LPC_LA29_P"] ;# Bank  68 VCCO - VADJ_FMC - IO_L2P_T0L_N2_68
#set_property IOSTANDARD  LVDS     [get_ports "FMC_LPC_LA29_P"] ;# Bank  68 VCCO - VADJ_FMC - IO_L2P_T0L_N2_68
#set_property PACKAGE_PIN L13      [get_ports "FMC_LPC_LA28_N"] ;# Bank  68 VCCO - VADJ_FMC - IO_L1N_T0L_N1_DBC_68
#set_property IOSTANDARD  LVDS     [get_ports "FMC_LPC_LA28_N"] ;# Bank  68 VCCO - VADJ_FMC - IO_L1N_T0L_N1_DBC_68
#set_property PACKAGE_PIN M13      [get_ports "FMC_LPC_LA28_P"] ;# Bank  68 VCCO - VADJ_FMC - IO_L1P_T0L_N0_DBC_68
#set_property IOSTANDARD  LVDS     [get_ports "FMC_LPC_LA28_P"] ;# Bank  68 VCCO - VADJ_FMC - IO_L1P_T0L_N0_DBC_68
#Other net   PACKAGE_PIN J12      - 4N9503                    Bank  68 - VREF_68
#set_property PACKAGE_PIN L16      [get_ports "FMC_LPC_LA04_N"] ;# Bank  67 VCCO - VADJ_FMC - IO_L24N_T3U_N11_67
#set_property IOSTANDARD  LVDS     [get_ports "FMC_LPC_LA04_N"] ;# Bank  67 VCCO - VADJ_FMC - IO_L24N_T3U_N11_67
#set_property PACKAGE_PIN L17      [get_ports "FMC_LPC_LA04_P"] ;# Bank  67 VCCO - VADJ_FMC - IO_L24P_T3U_N10_67
#set_property IOSTANDARD  LVDS     [get_ports "FMC_LPC_LA04_P"] ;# Bank  67 VCCO - VADJ_FMC - IO_L24P_T3U_N10_67
#set_property PACKAGE_PIN K18      [get_ports "FMC_LPC_LA03_N"] ;# Bank  67 VCCO - VADJ_FMC - IO_L23N_T3U_N9_67
#set_property IOSTANDARD  LVDS     [get_ports "FMC_LPC_LA03_N"] ;# Bank  67 VCCO - VADJ_FMC - IO_L23N_T3U_N9_67
#set_property PACKAGE_PIN K19      [get_ports "FMC_LPC_LA03_P"] ;# Bank  67 VCCO - VADJ_FMC - IO_L23P_T3U_N8_67
#set_property IOSTANDARD  LVDS     [get_ports "FMC_LPC_LA03_P"] ;# Bank  67 VCCO - VADJ_FMC - IO_L23P_T3U_N8_67
#set_property PACKAGE_PIN K15      [get_ports "FMC_LPC_LA10_N"] ;# Bank  67 VCCO - VADJ_FMC - IO_L22N_T3U_N7_DBC_AD0N_67
#set_property IOSTANDARD  LVDS     [get_ports "FMC_LPC_LA10_N"] ;# Bank  67 VCCO - VADJ_FMC - IO_L22N_T3U_N7_DBC_AD0N_67
#set_property PACKAGE_PIN L15      [get_ports "FMC_LPC_LA10_P"] ;# Bank  67 VCCO - VADJ_FMC - IO_L22P_T3U_N6_DBC_AD0P_67
#set_property IOSTANDARD  LVDS     [get_ports "FMC_LPC_LA10_P"] ;# Bank  67 VCCO - VADJ_FMC - IO_L22P_T3U_N6_DBC_AD0P_67
#set_property PACKAGE_PIN J17      [get_ports "FMC_LPC_LA05_N"] ;# Bank  67 VCCO - VADJ_FMC - IO_L21N_T3L_N5_AD8N_67
#set_property IOSTANDARD  LVDS     [get_ports "FMC_LPC_LA05_N"] ;# Bank  67 VCCO - VADJ_FMC - IO_L21N_T3L_N5_AD8N_67
#set_property PACKAGE_PIN K17      [get_ports "FMC_LPC_LA05_P"] ;# Bank  67 VCCO - VADJ_FMC - IO_L21P_T3L_N4_AD8P_67
#set_property IOSTANDARD  LVDS     [get_ports "FMC_LPC_LA05_P"] ;# Bank  67 VCCO - VADJ_FMC - IO_L21P_T3L_N4_AD8P_67
#set_property PACKAGE_PIN J15      [get_ports "FMC_LPC_LA07_N"] ;# Bank  67 VCCO - VADJ_FMC - IO_L20N_T3L_N3_AD1N_67
#set_property IOSTANDARD  LVDS     [get_ports "FMC_LPC_LA07_N"] ;# Bank  67 VCCO - VADJ_FMC - IO_L20N_T3L_N3_AD1N_67
#set_property PACKAGE_PIN J16      [get_ports "FMC_LPC_LA07_P"] ;# Bank  67 VCCO - VADJ_FMC - IO_L20P_T3L_N2_AD1P_67
#set_property IOSTANDARD  LVDS     [get_ports "FMC_LPC_LA07_P"] ;# Bank  67 VCCO - VADJ_FMC - IO_L20P_T3L_N2_AD1P_67
#set_property PACKAGE_PIN K20      [get_ports "FMC_LPC_LA02_N"] ;# Bank  67 VCCO - VADJ_FMC - IO_L19N_T3L_N1_DBC_AD9N_67
#set_property IOSTANDARD  LVDS     [get_ports "FMC_LPC_LA02_N"] ;# Bank  67 VCCO - VADJ_FMC - IO_L19N_T3L_N1_DBC_AD9N_67
#set_property PACKAGE_PIN L20      [get_ports "FMC_LPC_LA02_P"] ;# Bank  67 VCCO - VADJ_FMC - IO_L19P_T3L_N0_DBC_AD9P_67
#set_property IOSTANDARD  LVDS     [get_ports "FMC_LPC_LA02_P"] ;# Bank  67 VCCO - VADJ_FMC - IO_L19P_T3L_N0_DBC_AD9P_67
#set_property PACKAGE_PIN J20      [get_ports "7N10213"] ;# Bank  67 VCCO - VADJ_FMC - IO_T3U_N12_67
#set_property IOSTANDARD  LVCMOSxx [get_ports "7N10213"] ;# Bank  67 VCCO - VADJ_FMC - IO_T3U_N12_67
#set_property PACKAGE_PIN J19      [get_ports "7N10210"] ;# Bank  67 VCCO - VADJ_FMC - IO_T2U_N12_67
#set_property IOSTANDARD  LVCMOSxx [get_ports "7N10210"] ;# Bank  67 VCCO - VADJ_FMC - IO_T2U_N12_67
#set_property PACKAGE_PIN G16      [get_ports "FMC_LPC_LA09_N"] ;# Bank  67 VCCO - VADJ_FMC - IO_L18N_T2U_N11_AD2N_67
#set_property IOSTANDARD  LVDS     [get_ports "FMC_LPC_LA09_N"] ;# Bank  67 VCCO - VADJ_FMC - IO_L18N_T2U_N11_AD2N_67
#set_property PACKAGE_PIN H16      [get_ports "FMC_LPC_LA09_P"] ;# Bank  67 VCCO - VADJ_FMC - IO_L18P_T2U_N10_AD2P_67
#set_property IOSTANDARD  LVDS     [get_ports "FMC_LPC_LA09_P"] ;# Bank  67 VCCO - VADJ_FMC - IO_L18P_T2U_N10_AD2P_67
#set_property PACKAGE_PIN F18      [get_ports "FMC_LPC_LA12_N"] ;# Bank  67 VCCO - VADJ_FMC - IO_L17N_T2U_N9_AD10N_67
#set_property IOSTANDARD  LVDS     [get_ports "FMC_LPC_LA12_N"] ;# Bank  67 VCCO - VADJ_FMC - IO_L17N_T2U_N9_AD10N_67
#set_property PACKAGE_PIN G18      [get_ports "FMC_LPC_LA12_P"] ;# Bank  67 VCCO - VADJ_FMC - IO_L17P_T2U_N8_AD10P_67
#set_property IOSTANDARD  LVDS     [get_ports "FMC_LPC_LA12_P"] ;# Bank  67 VCCO - VADJ_FMC - IO_L17P_T2U_N8_AD10P_67
#set_property PACKAGE_PIN H17      [get_ports "FMC_LPC_LA01_CC_N"] ;# Bank  67 VCCO - VADJ_FMC - IO_L16N_T2U_N7_QBC_AD3N_67
#set_property IOSTANDARD  LVDS     [get_ports "FMC_LPC_LA01_CC_N"] ;# Bank  67 VCCO - VADJ_FMC - IO_L16N_T2U_N7_QBC_AD3N_67
#set_property PACKAGE_PIN H18      [get_ports "FMC_LPC_LA01_CC_P"] ;# Bank  67 VCCO - VADJ_FMC - IO_L16P_T2U_N6_QBC_AD3P_67
#set_property IOSTANDARD  LVDS     [get_ports "FMC_LPC_LA01_CC_P"] ;# Bank  67 VCCO - VADJ_FMC - IO_L16P_T2U_N6_QBC_AD3P_67
#set_property PACKAGE_PIN G19      [get_ports "FMC_LPC_LA06_N"] ;# Bank  67 VCCO - VADJ_FMC - IO_L15N_T2L_N5_AD11N_67
#set_property IOSTANDARD  LVDS     [get_ports "FMC_LPC_LA06_N"] ;# Bank  67 VCCO - VADJ_FMC - IO_L15N_T2L_N5_AD11N_67
#set_property PACKAGE_PIN H19      [get_ports "FMC_LPC_LA06_P"] ;# Bank  67 VCCO - VADJ_FMC - IO_L15P_T2L_N4_AD11P_67
#set_property IOSTANDARD  LVDS     [get_ports "FMC_LPC_LA06_P"] ;# Bank  67 VCCO - VADJ_FMC - IO_L15P_T2L_N4_AD11P_67
#set_property PACKAGE_PIN F15      [get_ports "FMC_LPC_LA13_N"] ;# Bank  67 VCCO - VADJ_FMC - IO_L14N_T2L_N3_GC_67
#set_property IOSTANDARD  LVDS     [get_ports "FMC_LPC_LA13_N"] ;# Bank  67 VCCO - VADJ_FMC - IO_L14N_T2L_N3_GC_67
#set_property PACKAGE_PIN G15      [get_ports "FMC_LPC_LA13_P"] ;# Bank  67 VCCO - VADJ_FMC - IO_L14P_T2L_N2_GC_67
#set_property IOSTANDARD  LVDS     [get_ports "FMC_LPC_LA13_P"] ;# Bank  67 VCCO - VADJ_FMC - IO_L14P_T2L_N2_GC_67
#set_property PACKAGE_PIN F16      [get_ports "FMC_LPC_LA00_CC_N"] ;# Bank  67 VCCO - VADJ_FMC - IO_L13N_T2L_N1_GC_QBC_67
#set_property IOSTANDARD  LVDS     [get_ports "FMC_LPC_LA00_CC_N"] ;# Bank  67 VCCO - VADJ_FMC - IO_L13N_T2L_N1_GC_QBC_67
#set_property PACKAGE_PIN F17      [get_ports "FMC_LPC_LA00_CC_P"] ;# Bank  67 VCCO - VADJ_FMC - IO_L13P_T2L_N0_GC_QBC_67
#set_property IOSTANDARD  LVDS     [get_ports "FMC_LPC_LA00_CC_P"] ;# Bank  67 VCCO - VADJ_FMC - IO_L13P_T2L_N0_GC_QBC_67
#set_property PACKAGE_PIN E14      [get_ports "FMC_LPC_CLK0_M2C_N"] ;# Bank  67 VCCO - VADJ_FMC - IO_L12N_T1U_N11_GC_67
#set_property IOSTANDARD  LVDS     [get_ports "FMC_LPC_CLK0_M2C_N"] ;# Bank  67 VCCO - VADJ_FMC - IO_L12N_T1U_N11_GC_67
#set_property PACKAGE_PIN E15      [get_ports "FMC_LPC_CLK0_M2C_P"] ;# Bank  67 VCCO - VADJ_FMC - IO_L12P_T1U_N10_GC_67
#set_property IOSTANDARD  LVDS     [get_ports "FMC_LPC_CLK0_M2C_P"] ;# Bank  67 VCCO - VADJ_FMC - IO_L12P_T1U_N10_GC_67
#set_property PACKAGE_PIN D14      [get_ports "7N10403"] ;# Bank  67 VCCO - VADJ_FMC - IO_L11N_T1U_N9_GC_67
#set_property IOSTANDARD  LVCMOSxx [get_ports "7N10403"] ;# Bank  67 VCCO - VADJ_FMC - IO_L11N_T1U_N9_GC_67
#set_property PACKAGE_PIN D15      [get_ports "7N10406"] ;# Bank  67 VCCO - VADJ_FMC - IO_L11P_T1U_N8_GC_67
#set_property IOSTANDARD  LVCMOSxx [get_ports "7N10406"] ;# Bank  67 VCCO - VADJ_FMC - IO_L11P_T1U_N8_GC_67
#set_property PACKAGE_PIN F13      [get_ports "7N10612"] ;# Bank  67 VCCO - VADJ_FMC - IO_L10N_T1U_N7_QBC_AD4N_67
#set_property IOSTANDARD  LVCMOSxx [get_ports "7N10612"] ;# Bank  67 VCCO - VADJ_FMC - IO_L10N_T1U_N7_QBC_AD4N_67
#set_property PACKAGE_PIN G14      [get_ports "7N10614"] ;# Bank  67 VCCO - VADJ_FMC - IO_L10P_T1U_N6_QBC_AD4P_67
#set_property IOSTANDARD  LVCMOSxx [get_ports "7N10614"] ;# Bank  67 VCCO - VADJ_FMC - IO_L10P_T1U_N6_QBC_AD4P_67
#set_property PACKAGE_PIN E17      [get_ports "FMC_LPC_LA08_N"] ;# Bank  67 VCCO - VADJ_FMC - IO_L9N_T1L_N5_AD12N_67
#set_property IOSTANDARD  LVDS     [get_ports "FMC_LPC_LA08_N"] ;# Bank  67 VCCO - VADJ_FMC - IO_L9N_T1L_N5_AD12N_67
#set_property PACKAGE_PIN E18      [get_ports "FMC_LPC_LA08_P"] ;# Bank  67 VCCO - VADJ_FMC - IO_L9P_T1L_N4_AD12P_67
#set_property IOSTANDARD  LVDS     [get_ports "FMC_LPC_LA08_P"] ;# Bank  67 VCCO - VADJ_FMC - IO_L9P_T1L_N4_AD12P_67
#set_property PACKAGE_PIN C17      [get_ports "FMC_LPC_LA16_N"] ;# Bank  67 VCCO - VADJ_FMC - IO_L8N_T1L_N3_AD5N_67
#set_property IOSTANDARD  LVDS     [get_ports "FMC_LPC_LA16_N"] ;# Bank  67 VCCO - VADJ_FMC - IO_L8N_T1L_N3_AD5N_67
#set_property PACKAGE_PIN D17      [get_ports "FMC_LPC_LA16_P"] ;# Bank  67 VCCO - VADJ_FMC - IO_L8P_T1L_N2_AD5P_67
#set_property IOSTANDARD  LVDS     [get_ports "FMC_LPC_LA16_P"] ;# Bank  67 VCCO - VADJ_FMC - IO_L8P_T1L_N2_AD5P_67
#set_property PACKAGE_PIN C16      [get_ports "FMC_LPC_LA15_N"] ;# Bank  67 VCCO - VADJ_FMC - IO_L7N_T1L_N1_QBC_AD13N_67
#set_property IOSTANDARD  LVDS     [get_ports "FMC_LPC_LA15_N"] ;# Bank  67 VCCO - VADJ_FMC - IO_L7N_T1L_N1_QBC_AD13N_67
#set_property PACKAGE_PIN D16      [get_ports "FMC_LPC_LA15_P"] ;# Bank  67 VCCO - VADJ_FMC - IO_L7P_T1L_N0_QBC_AD13P_67
#set_property IOSTANDARD  LVDS     [get_ports "FMC_LPC_LA15_P"] ;# Bank  67 VCCO - VADJ_FMC - IO_L7P_T1L_N0_QBC_AD13P_67
#set_property PACKAGE_PIN E13      [get_ports "7N10207"] ;# Bank  67 VCCO - VADJ_FMC - IO_T1U_N12_67
#set_property IOSTANDARD  LVCMOSxx [get_ports "7N10207"] ;# Bank  67 VCCO - VADJ_FMC - IO_T1U_N12_67
#set_property PACKAGE_PIN C14      [get_ports "7N10204"] ;# Bank  67 VCCO - VADJ_FMC - IO_T0U_N12_VRP_67
#set_property IOSTANDARD  LVCMOSxx [get_ports "7N10204"] ;# Bank  67 VCCO - VADJ_FMC - IO_T0U_N12_VRP_67
#set_property PACKAGE_PIN C12      [get_ports "FMC_LPC_LA14_N"] ;# Bank  67 VCCO - VADJ_FMC - IO_L6N_T0U_N11_AD6N_67
#set_property IOSTANDARD  LVDS     [get_ports "FMC_LPC_LA14_N"] ;# Bank  67 VCCO - VADJ_FMC - IO_L6N_T0U_N11_AD6N_67
#set_property PACKAGE_PIN C13      [get_ports "FMC_LPC_LA14_P"] ;# Bank  67 VCCO - VADJ_FMC - IO_L6P_T0U_N10_AD6P_67
#set_property IOSTANDARD  LVDS     [get_ports "FMC_LPC_LA14_P"] ;# Bank  67 VCCO - VADJ_FMC - IO_L6P_T0U_N10_AD6P_67
#set_property PACKAGE_PIN A12      [get_ports "FMC_LPC_LA11_N"] ;# Bank  67 VCCO - VADJ_FMC - IO_L5N_T0U_N9_AD14N_67
#set_property IOSTANDARD  LVDS     [get_ports "FMC_LPC_LA11_N"] ;# Bank  67 VCCO - VADJ_FMC - IO_L5N_T0U_N9_AD14N_67
#set_property PACKAGE_PIN A13      [get_ports "FMC_LPC_LA11_P"] ;# Bank  67 VCCO - VADJ_FMC - IO_L5P_T0U_N8_AD14P_67
#set_property IOSTANDARD  LVDS     [get_ports "FMC_LPC_LA11_P"] ;# Bank  67 VCCO - VADJ_FMC - IO_L5P_T0U_N8_AD14P_67
#set_property PACKAGE_PIN B13      [get_ports "7N10197"] ;# Bank  67 VCCO - VADJ_FMC - IO_L4N_T0U_N7_DBC_AD7N_67
#set_property IOSTANDARD  LVCMOSxx [get_ports "7N10197"] ;# Bank  67 VCCO - VADJ_FMC - IO_L4N_T0U_N7_DBC_AD7N_67
#set_property PACKAGE_PIN B14      [get_ports "7N10198"] ;# Bank  67 VCCO - VADJ_FMC - IO_L4P_T0U_N6_DBC_AD7P_67
#set_property IOSTANDARD  LVCMOSxx [get_ports "7N10198"] ;# Bank  67 VCCO - VADJ_FMC - IO_L4P_T0U_N6_DBC_AD7P_67
#set_property PACKAGE_PIN A14      [get_ports "7N10193"] ;# Bank  67 VCCO - VADJ_FMC - IO_L3N_T0L_N5_AD15N_67
#set_property IOSTANDARD  LVCMOSxx [get_ports "7N10193"] ;# Bank  67 VCCO - VADJ_FMC - IO_L3N_T0L_N5_AD15N_67
#set_property PACKAGE_PIN A15      [get_ports "7N10194"] ;# Bank  67 VCCO - VADJ_FMC - IO_L3P_T0L_N4_AD15P_67
#set_property IOSTANDARD  LVCMOSxx [get_ports "7N10194"] ;# Bank  67 VCCO - VADJ_FMC - IO_L3P_T0L_N4_AD15P_67
#set_property PACKAGE_PIN B15      [get_ports "7N10185"] ;# Bank  67 VCCO - VADJ_FMC - IO_L2N_T0L_N3_67
#set_property IOSTANDARD  LVCMOSxx [get_ports "7N10185"] ;# Bank  67 VCCO - VADJ_FMC - IO_L2N_T0L_N3_67
#set_property PACKAGE_PIN B16      [get_ports "7N10186"] ;# Bank  67 VCCO - VADJ_FMC - IO_L2P_T0L_N2_67
#set_property IOSTANDARD  LVCMOSxx [get_ports "7N10186"] ;# Bank  67 VCCO - VADJ_FMC - IO_L2P_T0L_N2_67
#set_property PACKAGE_PIN A16      [get_ports "7N10181"] ;# Bank  67 VCCO - VADJ_FMC - IO_L1N_T0L_N1_DBC_67
#set_property IOSTANDARD  LVCMOSxx [get_ports "7N10181"] ;# Bank  67 VCCO - VADJ_FMC - IO_L1N_T0L_N1_DBC_67
#set_property PACKAGE_PIN A17      [get_ports "7N10182"] ;# Bank  67 VCCO - VADJ_FMC - IO_L1P_T0L_N0_DBC_67
#set_property IOSTANDARD  LVCMOSxx [get_ports "7N10182"] ;# Bank  67 VCCO - VADJ_FMC - IO_L1P_T0L_N0_DBC_67
#Other net   PACKAGE_PIN L18      - 7N9719                    Bank  67 - VREF_67
#set_property PACKAGE_PIN AC13     [get_ports "DDR4_SODIMM_DQ32"] ;# Bank  66 VCCO - VCC1V2   - IO_L24N_T3U_N11_66
#set_property IOSTANDARD  POD12    [get_ports "DDR4_SODIMM_DQ32"] ;# Bank  66 VCCO - VCC1V2   - IO_L24N_T3U_N11_66
#set_property PACKAGE_PIN AB13     [get_ports "DDR4_SODIMM_DQ33"] ;# Bank  66 VCCO - VCC1V2   - IO_L24P_T3U_N10_66
#set_property IOSTANDARD  POD12    [get_ports "DDR4_SODIMM_DQ33"] ;# Bank  66 VCCO - VCC1V2   - IO_L24P_T3U_N10_66
#set_property PACKAGE_PIN AF12     [get_ports "DDR4_SODIMM_DQ34"] ;# Bank  66 VCCO - VCC1V2   - IO_L23N_T3U_N9_66
#set_property IOSTANDARD  POD12    [get_ports "DDR4_SODIMM_DQ34"] ;# Bank  66 VCCO - VCC1V2   - IO_L23N_T3U_N9_66
#set_property PACKAGE_PIN AE12     [get_ports "DDR4_SODIMM_DQ35"] ;# Bank  66 VCCO - VCC1V2   - IO_L23P_T3U_N8_66
#set_property IOSTANDARD  POD12    [get_ports "DDR4_SODIMM_DQ35"] ;# Bank  66 VCCO - VCC1V2   - IO_L23P_T3U_N8_66
#set_property PACKAGE_PIN AD12     [get_ports "DDR4_SODIMM_DQS4_C"] ;# Bank  66 VCCO - VCC1V2   - IO_L22N_T3U_N7_DBC_AD0N_66
#set_property IOSTANDARD  DIFF_POD12 [get_ports "DDR4_SODIMM_DQS4_C"] ;# Bank  66 VCCO - VCC1V2   - IO_L22N_T3U_N7_DBC_AD0N_66
#set_property PACKAGE_PIN AC12     [get_ports "DDR4_SODIMM_DQS4_T"] ;# Bank  66 VCCO - VCC1V2   - IO_L22P_T3U_N6_DBC_AD0P_66
#set_property IOSTANDARD  DIFF_POD12 [get_ports "DDR4_SODIMM_DQS4_T"] ;# Bank  66 VCCO - VCC1V2   - IO_L22P_T3U_N6_DBC_AD0P_66
#set_property PACKAGE_PIN AF13     [get_ports "DDR4_SODIMM_DQ36"] ;# Bank  66 VCCO - VCC1V2   - IO_L21N_T3L_N5_AD8N_66
#set_property IOSTANDARD  POD12    [get_ports "DDR4_SODIMM_DQ36"] ;# Bank  66 VCCO - VCC1V2   - IO_L21N_T3L_N5_AD8N_66
#set_property PACKAGE_PIN AE13     [get_ports "DDR4_SODIMM_DQ37"] ;# Bank  66 VCCO - VCC1V2   - IO_L21P_T3L_N4_AD8P_66
#set_property IOSTANDARD  POD12    [get_ports "DDR4_SODIMM_DQ37"] ;# Bank  66 VCCO - VCC1V2   - IO_L21P_T3L_N4_AD8P_66
#set_property PACKAGE_PIN AE14     [get_ports "DDR4_SODIMM_DQ38"] ;# Bank  66 VCCO - VCC1V2   - IO_L20N_T3L_N3_AD1N_66
#set_property IOSTANDARD  POD12    [get_ports "DDR4_SODIMM_DQ38"] ;# Bank  66 VCCO - VCC1V2   - IO_L20N_T3L_N3_AD1N_66
#set_property PACKAGE_PIN AD14     [get_ports "DDR4_SODIMM_DQ39"] ;# Bank  66 VCCO - VCC1V2   - IO_L20P_T3L_N2_AD1P_66
#set_property IOSTANDARD  POD12    [get_ports "DDR4_SODIMM_DQ39"] ;# Bank  66 VCCO - VCC1V2   - IO_L20P_T3L_N2_AD1P_66
#set_property PACKAGE_PIN AF10     [get_ports "7N10601"] ;# Bank  66 VCCO - VCC1V2   - IO_L19N_T3L_N1_DBC_AD9N_66
#set_property IOSTANDARD  LVCMOSxx [get_ports "7N10601"] ;# Bank  66 VCCO - VCC1V2   - IO_L19N_T3L_N1_DBC_AD9N_66
#set_property PACKAGE_PIN AF11     [get_ports "DDR4_SODIMM_DM4_B"] ;# Bank  66 VCCO - VCC1V2   - IO_L19P_T3L_N0_DBC_AD9P_66
#set_property IOSTANDARD  POD12    [get_ports "DDR4_SODIMM_DM4_B"] ;# Bank  66 VCCO - VCC1V2   - IO_L19P_T3L_N0_DBC_AD9P_66
#set_property PACKAGE_PIN AC14     [get_ports "7N10603"] ;# Bank  66 VCCO - VCC1V2   - IO_T3U_N12_66
#set_property IOSTANDARD  LVCMOSxx [get_ports "7N10603"] ;# Bank  66 VCCO - VCC1V2   - IO_T3U_N12_66
#set_property PACKAGE_PIN AH8      [get_ports "7N10599"] ;# Bank  66 VCCO - VCC1V2   - IO_T2U_N12_66
#set_property IOSTANDARD  LVCMOSxx [get_ports "7N10599"] ;# Bank  66 VCCO - VCC1V2   - IO_T2U_N12_66
#set_property PACKAGE_PIN AG8      [get_ports "DDR4_SODIMM_DQ40"] ;# Bank  66 VCCO - VCC1V2   - IO_L18N_T2U_N11_AD2N_66
#set_property IOSTANDARD  POD12    [get_ports "DDR4_SODIMM_DQ40"] ;# Bank  66 VCCO - VCC1V2   - IO_L18N_T2U_N11_AD2N_66
#set_property PACKAGE_PIN AF8      [get_ports "DDR4_SODIMM_DQ41"] ;# Bank  66 VCCO - VCC1V2   - IO_L18P_T2U_N10_AD2P_66
#set_property IOSTANDARD  POD12    [get_ports "DDR4_SODIMM_DQ41"] ;# Bank  66 VCCO - VCC1V2   - IO_L18P_T2U_N10_AD2P_66
#set_property PACKAGE_PIN AG10     [get_ports "DDR4_SODIMM_DQ42"] ;# Bank  66 VCCO - VCC1V2   - IO_L17N_T2U_N9_AD10N_66
#set_property IOSTANDARD  POD12    [get_ports "DDR4_SODIMM_DQ42"] ;# Bank  66 VCCO - VCC1V2   - IO_L17N_T2U_N9_AD10N_66
#set_property PACKAGE_PIN AG11     [get_ports "DDR4_SODIMM_DQ43"] ;# Bank  66 VCCO - VCC1V2   - IO_L17P_T2U_N8_AD10P_66
#set_property IOSTANDARD  POD12    [get_ports "DDR4_SODIMM_DQ43"] ;# Bank  66 VCCO - VCC1V2   - IO_L17P_T2U_N8_AD10P_66
#set_property PACKAGE_PIN AH9      [get_ports "DDR4_SODIMM_DQS5_C"] ;# Bank  66 VCCO - VCC1V2   - IO_L16N_T2U_N7_QBC_AD3N_66
#set_property IOSTANDARD  DIFF_POD12 [get_ports "DDR4_SODIMM_DQS5_C"] ;# Bank  66 VCCO - VCC1V2   - IO_L16N_T2U_N7_QBC_AD3N_66
#set_property PACKAGE_PIN AG9      [get_ports "DDR4_SODIMM_DQS5_T"] ;# Bank  66 VCCO - VCC1V2   - IO_L16P_T2U_N6_QBC_AD3P_66
#set_property IOSTANDARD  DIFF_POD12 [get_ports "DDR4_SODIMM_DQS5_T"] ;# Bank  66 VCCO - VCC1V2   - IO_L16P_T2U_N6_QBC_AD3P_66
#set_property PACKAGE_PIN AH13     [get_ports "DDR4_SODIMM_DQ44"] ;# Bank  66 VCCO - VCC1V2   - IO_L15N_T2L_N5_AD11N_66
#set_property IOSTANDARD  POD12    [get_ports "DDR4_SODIMM_DQ44"] ;# Bank  66 VCCO - VCC1V2   - IO_L15N_T2L_N5_AD11N_66
#set_property PACKAGE_PIN AG13     [get_ports "DDR4_SODIMM_DQ45"] ;# Bank  66 VCCO - VCC1V2   - IO_L15P_T2L_N4_AD11P_66
#set_property IOSTANDARD  POD12    [get_ports "DDR4_SODIMM_DQ45"] ;# Bank  66 VCCO - VCC1V2   - IO_L15P_T2L_N4_AD11P_66
#set_property PACKAGE_PIN AJ11     [get_ports "DDR4_SODIMM_DQ46"] ;# Bank  66 VCCO - VCC1V2   - IO_L14N_T2L_N3_GC_66
#set_property IOSTANDARD  POD12    [get_ports "DDR4_SODIMM_DQ46"] ;# Bank  66 VCCO - VCC1V2   - IO_L14N_T2L_N3_GC_66
#set_property PACKAGE_PIN AH11     [get_ports "DDR4_SODIMM_DQ47"] ;# Bank  66 VCCO - VCC1V2   - IO_L14P_T2L_N2_GC_66
#set_property IOSTANDARD  POD12    [get_ports "DDR4_SODIMM_DQ47"] ;# Bank  66 VCCO - VCC1V2   - IO_L14P_T2L_N2_GC_66
#set_property PACKAGE_PIN AJ12     [get_ports "7N10597"] ;# Bank  66 VCCO - VCC1V2   - IO_L13N_T2L_N1_GC_QBC_66
#set_property IOSTANDARD  LVCMOSxx [get_ports "7N10597"] ;# Bank  66 VCCO - VCC1V2   - IO_L13N_T2L_N1_GC_QBC_66
#set_property PACKAGE_PIN AH12     [get_ports "DDR4_SODIMM_DM5_B"] ;# Bank  66 VCCO - VCC1V2   - IO_L13P_T2L_N0_GC_QBC_66
#set_property IOSTANDARD  POD12    [get_ports "DDR4_SODIMM_DM5_B"] ;# Bank  66 VCCO - VCC1V2   - IO_L13P_T2L_N0_GC_QBC_66
#set_property PACKAGE_PIN AK9      [get_ports "DDR4_SODIMM_DQ48"] ;# Bank  66 VCCO - VCC1V2   - IO_L12N_T1U_N11_GC_66
#set_property IOSTANDARD  POD12    [get_ports "DDR4_SODIMM_DQ48"] ;# Bank  66 VCCO - VCC1V2   - IO_L12N_T1U_N11_GC_66
#set_property PACKAGE_PIN AJ9      [get_ports "DDR4_SODIMM_DQ49"] ;# Bank  66 VCCO - VCC1V2   - IO_L12P_T1U_N10_GC_66
#set_property IOSTANDARD  POD12    [get_ports "DDR4_SODIMM_DQ49"] ;# Bank  66 VCCO - VCC1V2   - IO_L12P_T1U_N10_GC_66
#set_property PACKAGE_PIN AK10     [get_ports "DDR4_SODIMM_DQ50"] ;# Bank  66 VCCO - VCC1V2   - IO_L11N_T1U_N9_GC_66
#set_property IOSTANDARD  POD12    [get_ports "DDR4_SODIMM_DQ50"] ;# Bank  66 VCCO - VCC1V2   - IO_L11N_T1U_N9_GC_66
#set_property PACKAGE_PIN AJ10     [get_ports "DDR4_SODIMM_DQ51"] ;# Bank  66 VCCO - VCC1V2   - IO_L11P_T1U_N8_GC_66
#set_property IOSTANDARD  POD12    [get_ports "DDR4_SODIMM_DQ51"] ;# Bank  66 VCCO - VCC1V2   - IO_L11P_T1U_N8_GC_66
#set_property PACKAGE_PIN AL8      [get_ports "DDR4_SODIMM_DQS6_C"] ;# Bank  66 VCCO - VCC1V2   - IO_L10N_T1U_N7_QBC_AD4N_66
#set_property IOSTANDARD  DIFF_POD12 [get_ports "DDR4_SODIMM_DQS6_C"] ;# Bank  66 VCCO - VCC1V2   - IO_L10N_T1U_N7_QBC_AD4N_66
#set_property PACKAGE_PIN AK8      [get_ports "DDR4_SODIMM_DQS6_T"] ;# Bank  66 VCCO - VCC1V2   - IO_L10P_T1U_N6_QBC_AD4P_66
#set_property IOSTANDARD  DIFF_POD12 [get_ports "DDR4_SODIMM_DQS6_T"] ;# Bank  66 VCCO - VCC1V2   - IO_L10P_T1U_N6_QBC_AD4P_66
#set_property PACKAGE_PIN AL12     [get_ports "DDR4_SODIMM_DQ52"] ;# Bank  66 VCCO - VCC1V2   - IO_L9N_T1L_N5_AD12N_66
#set_property IOSTANDARD  POD12    [get_ports "DDR4_SODIMM_DQ52"] ;# Bank  66 VCCO - VCC1V2   - IO_L9N_T1L_N5_AD12N_66
#set_property PACKAGE_PIN AK12     [get_ports "DDR4_SODIMM_DQ53"] ;# Bank  66 VCCO - VCC1V2   - IO_L9P_T1L_N4_AD12P_66
#set_property IOSTANDARD  POD12    [get_ports "DDR4_SODIMM_DQ53"] ;# Bank  66 VCCO - VCC1V2   - IO_L9P_T1L_N4_AD12P_66
#set_property PACKAGE_PIN AL10     [get_ports "DDR4_SODIMM_DQ54"] ;# Bank  66 VCCO - VCC1V2   - IO_L8N_T1L_N3_AD5N_66
#set_property IOSTANDARD  POD12    [get_ports "DDR4_SODIMM_DQ54"] ;# Bank  66 VCCO - VCC1V2   - IO_L8N_T1L_N3_AD5N_66
#set_property PACKAGE_PIN AL11     [get_ports "DDR4_SODIMM_DQ55"] ;# Bank  66 VCCO - VCC1V2   - IO_L8P_T1L_N2_AD5P_66
#set_property IOSTANDARD  POD12    [get_ports "DDR4_SODIMM_DQ55"] ;# Bank  66 VCCO - VCC1V2   - IO_L8P_T1L_N2_AD5P_66
#set_property PACKAGE_PIN AL13     [get_ports "7N10593"] ;# Bank  66 VCCO - VCC1V2   - IO_L7N_T1L_N1_QBC_AD13N_66
#set_property IOSTANDARD  LVCMOSxx [get_ports "7N10593"] ;# Bank  66 VCCO - VCC1V2   - IO_L7N_T1L_N1_QBC_AD13N_66
#set_property PACKAGE_PIN AK13     [get_ports "DDR4_SODIMM_DM6_B"] ;# Bank  66 VCCO - VCC1V2   - IO_L7P_T1L_N0_QBC_AD13P_66
#set_property IOSTANDARD  POD12    [get_ports "DDR4_SODIMM_DM6_B"] ;# Bank  66 VCCO - VCC1V2   - IO_L7P_T1L_N0_QBC_AD13P_66
#set_property PACKAGE_PIN AM13     [get_ports "7N10595"] ;# Bank  66 VCCO - VCC1V2   - IO_T1U_N12_66
#set_property IOSTANDARD  LVCMOSxx [get_ports "7N10595"] ;# Bank  66 VCCO - VCC1V2   - IO_T1U_N12_66
#set_property PACKAGE_PIN AP8      [get_ports "VRP_66"] ;# Bank  66 VCCO - VCC1V2   - IO_T0U_N12_VRP_66
#set_property IOSTANDARD  LVCMOSxx [get_ports "VRP_66"] ;# Bank  66 VCCO - VCC1V2   - IO_T0U_N12_VRP_66
#set_property PACKAGE_PIN AM8      [get_ports "DDR4_SODIMM_DQ56"] ;# Bank  66 VCCO - VCC1V2   - IO_L6N_T0U_N11_AD6N_66
#set_property IOSTANDARD  POD12    [get_ports "DDR4_SODIMM_DQ56"] ;# Bank  66 VCCO - VCC1V2   - IO_L6N_T0U_N11_AD6N_66
#set_property PACKAGE_PIN AM9      [get_ports "DDR4_SODIMM_DQ57"] ;# Bank  66 VCCO - VCC1V2   - IO_L6P_T0U_N10_AD6P_66
#set_property IOSTANDARD  POD12    [get_ports "DDR4_SODIMM_DQ57"] ;# Bank  66 VCCO - VCC1V2   - IO_L6P_T0U_N10_AD6P_66
#set_property PACKAGE_PIN AM10     [get_ports "DDR4_SODIMM_DQ58"] ;# Bank  66 VCCO - VCC1V2   - IO_L5N_T0U_N9_AD14N_66
#set_property IOSTANDARD  POD12    [get_ports "DDR4_SODIMM_DQ58"] ;# Bank  66 VCCO - VCC1V2   - IO_L5N_T0U_N9_AD14N_66
#set_property PACKAGE_PIN AM11     [get_ports "DDR4_SODIMM_DQ59"] ;# Bank  66 VCCO - VCC1V2   - IO_L5P_T0U_N8_AD14P_66
#set_property IOSTANDARD  POD12    [get_ports "DDR4_SODIMM_DQ59"] ;# Bank  66 VCCO - VCC1V2   - IO_L5P_T0U_N8_AD14P_66
#set_property PACKAGE_PIN AN8      [get_ports "DDR4_SODIMM_DQS7_C"] ;# Bank  66 VCCO - VCC1V2   - IO_L4N_T0U_N7_DBC_AD7N_66
#set_property IOSTANDARD  DIFF_POD12 [get_ports "DDR4_SODIMM_DQS7_C"] ;# Bank  66 VCCO - VCC1V2   - IO_L4N_T0U_N7_DBC_AD7N_66
#set_property PACKAGE_PIN AN9      [get_ports "DDR4_SODIMM_DQS7_T"] ;# Bank  66 VCCO - VCC1V2   - IO_L4P_T0U_N6_DBC_AD7P_66
#set_property IOSTANDARD  DIFF_POD12 [get_ports "DDR4_SODIMM_DQS7_T"] ;# Bank  66 VCCO - VCC1V2   - IO_L4P_T0U_N6_DBC_AD7P_66
#set_property PACKAGE_PIN AP11     [get_ports "DDR4_SODIMM_DQ60"] ;# Bank  66 VCCO - VCC1V2   - IO_L3N_T0L_N5_AD15N_66
#set_property IOSTANDARD  POD12    [get_ports "DDR4_SODIMM_DQ60"] ;# Bank  66 VCCO - VCC1V2   - IO_L3N_T0L_N5_AD15N_66
#set_property PACKAGE_PIN AN11     [get_ports "DDR4_SODIMM_DQ61"] ;# Bank  66 VCCO - VCC1V2   - IO_L3P_T0L_N4_AD15P_66
#set_property IOSTANDARD  POD12    [get_ports "DDR4_SODIMM_DQ61"] ;# Bank  66 VCCO - VCC1V2   - IO_L3P_T0L_N4_AD15P_66
#set_property PACKAGE_PIN AP9      [get_ports "DDR4_SODIMM_DQ62"] ;# Bank  66 VCCO - VCC1V2   - IO_L2N_T0L_N3_66
#set_property IOSTANDARD  POD12    [get_ports "DDR4_SODIMM_DQ62"] ;# Bank  66 VCCO - VCC1V2   - IO_L2N_T0L_N3_66
#set_property PACKAGE_PIN AP10     [get_ports "DDR4_SODIMM_DQ63"] ;# Bank  66 VCCO - VCC1V2   - IO_L2P_T0L_N2_66
#set_property IOSTANDARD  POD12    [get_ports "DDR4_SODIMM_DQ63"] ;# Bank  66 VCCO - VCC1V2   - IO_L2P_T0L_N2_66
#set_property PACKAGE_PIN AP12     [get_ports "7N10591"] ;# Bank  66 VCCO - VCC1V2   - IO_L1N_T0L_N1_DBC_66
#set_property IOSTANDARD  LVCMOSxx [get_ports "7N10591"] ;# Bank  66 VCCO - VCC1V2   - IO_L1N_T0L_N1_DBC_66
#set_property PACKAGE_PIN AN12     [get_ports "DDR4_SODIMM_DM7_B"] ;# Bank  66 VCCO - VCC1V2   - IO_L1P_T0L_N0_DBC_66
#set_property IOSTANDARD  POD12    [get_ports "DDR4_SODIMM_DM7_B"] ;# Bank  66 VCCO - VCC1V2   - IO_L1P_T0L_N0_DBC_66
#Other net   PACKAGE_PIN AB12     - 7N8282                    Bank  66 - VREF_66
#set_property PACKAGE_PIN AA20     [get_ports "DDR4_SODIMM_DQ8"] ;# Bank  65 VCCO - VCC1V2   - IO_L24N_T3U_N11_PERSTN0_65
#set_property IOSTANDARD  POD12   [get_ports "DDR4_SODIMM_DQ8"] ;# Bank  65 VCCO - VCC1V2   - IO_L24N_T3U_N11_PERSTN0_65
#set_property PACKAGE_PIN AA19     [get_ports "DDR4_SODIMM_DQ9"] ;# Bank  65 VCCO - VCC1V2   - IO_L24P_T3U_N10_PERSTN1_I2C_SDA_65
#set_property IOSTANDARD  POD12    [get_ports "DDR4_SODIMM_DQ9"] ;# Bank  65 VCCO - VCC1V2   - IO_L24P_T3U_N10_PERSTN1_I2C_SDA_65
#set_property PACKAGE_PIN AD19     [get_ports "DDR4_SODIMM_DQ10"] ;# Bank  65 VCCO - VCC1V2   - IO_L23N_T3U_N9_65
#set_property IOSTANDARD  POD12    [get_ports "DDR4_SODIMM_DQ10"] ;# Bank  65 VCCO - VCC1V2   - IO_L23N_T3U_N9_65
#set_property PACKAGE_PIN AC18     [get_ports "DDR4_SODIMM_DQ11"] ;# Bank  65 VCCO - VCC1V2   - IO_L23P_T3U_N8_I2C_SCLK_65
#set_property IOSTANDARD  POD12    [get_ports "DDR4_SODIMM_DQ11"] ;# Bank  65 VCCO - VCC1V2   - IO_L23P_T3U_N8_I2C_SCLK_65
#set_property PACKAGE_PIN AB18     [get_ports "DDR4_SODIMM_DQS1_C"] ;# Bank  65 VCCO - VCC1V2   - IO_L22N_T3U_N7_DBC_AD0N_65
#set_property IOSTANDARD  DIFF_POD12 [get_ports "DDR4_SODIMM_DQS1_C"] ;# Bank  65 VCCO - VCC1V2   - IO_L22N_T3U_N7_DBC_AD0N_65
#set_property PACKAGE_PIN AA18     [get_ports "DDR4_SODIMM_DQS1_T"] ;# Bank  65 VCCO - VCC1V2   - IO_L22P_T3U_N6_DBC_AD0P_65
#set_property IOSTANDARD  DIFF_POD12 [get_ports "DDR4_SODIMM_DQS1_T"] ;# Bank  65 VCCO - VCC1V2   - IO_L22P_T3U_N6_DBC_AD0P_65
#set_property PACKAGE_PIN AE20     [get_ports "DDR4_SODIMM_DQ12"] ;# Bank  65 VCCO - VCC1V2   - IO_L21N_T3L_N5_AD8N_65
#set_property IOSTANDARD  POD12    [get_ports "DDR4_SODIMM_DQ12"] ;# Bank  65 VCCO - VCC1V2   - IO_L21N_T3L_N5_AD8N_65
#set_property PACKAGE_PIN AD20     [get_ports "DDR4_SODIMM_DQ13"] ;# Bank  65 VCCO - VCC1V2   - IO_L21P_T3L_N4_AD8P_65
#set_property IOSTANDARD  POD12    [get_ports "DDR4_SODIMM_DQ13"] ;# Bank  65 VCCO - VCC1V2   - IO_L21P_T3L_N4_AD8P_65
#set_property PACKAGE_PIN AC19     [get_ports "DDR4_SODIMM_DQ14"] ;# Bank  65 VCCO - VCC1V2   - IO_L20N_T3L_N3_AD1N_65
#set_property IOSTANDARD  POD12    [get_ports "DDR4_SODIMM_DQ14"] ;# Bank  65 VCCO - VCC1V2   - IO_L20N_T3L_N3_AD1N_65
#set_property PACKAGE_PIN AB19     [get_ports "DDR4_SODIMM_DQ15"] ;# Bank  65 VCCO - VCC1V2   - IO_L20P_T3L_N2_AD1P_65
#set_property IOSTANDARD  POD12    [get_ports "DDR4_SODIMM_DQ15"] ;# Bank  65 VCCO - VCC1V2   - IO_L20P_T3L_N2_AD1P_65
#set_property PACKAGE_PIN AE19     [get_ports "6N12439"] ;# Bank  65 VCCO - VCC1V2   - IO_L19N_T3L_N1_DBC_AD9N_65
#set_property IOSTANDARD  LVCMOSxx [get_ports "6N12439"] ;# Bank  65 VCCO - VCC1V2   - IO_L19N_T3L_N1_DBC_AD9N_65
#set_property PACKAGE_PIN AE18     [get_ports "DDR4_SODIMM_DM1_B"] ;# Bank  65 VCCO - VCC1V2   - IO_L19P_T3L_N0_DBC_AD9P_65
#set_property IOSTANDARD  POD12    [get_ports "DDR4_SODIMM_DM1_B"] ;# Bank  65 VCCO - VCC1V2   - IO_L19P_T3L_N0_DBC_AD9P_65
#set_property PACKAGE_PIN AE22     [get_ports "6N12442"] ;# Bank  65 VCCO - VCC1V2   - IO_T3U_N12_65
#set_property IOSTANDARD  LVCMOSxx [get_ports "6N12442"] ;# Bank  65 VCCO - VCC1V2   - IO_T3U_N12_65
#set_property PACKAGE_PIN AF20     [get_ports "6N12436"] ;# Bank  65 VCCO - VCC1V2   - IO_T2U_N12_65
#set_property IOSTANDARD  LVCMOSxx [get_ports "6N12436"] ;# Bank  65 VCCO - VCC1V2   - IO_T2U_N12_65
#set_property PACKAGE_PIN AE24     [get_ports "DDR4_SODIMM_DQ0"] ;# Bank  65 VCCO - VCC1V2   - IO_L18N_T2U_N11_AD2N_65
#set_property IOSTANDARD  POD12    [get_ports "DDR4_SODIMM_DQ0"] ;# Bank  65 VCCO - VCC1V2   - IO_L18N_T2U_N11_AD2N_65
#set_property PACKAGE_PIN AE23     [get_ports "DDR4_SODIMM_DQ1"] ;# Bank  65 VCCO - VCC1V2   - IO_L18P_T2U_N10_AD2P_65
#set_property IOSTANDARD  POD12    [get_ports "DDR4_SODIMM_DQ1"] ;# Bank  65 VCCO - VCC1V2   - IO_L18P_T2U_N10_AD2P_65
#set_property PACKAGE_PIN AF22     [get_ports "DDR4_SODIMM_DQ2"] ;# Bank  65 VCCO - VCC1V2   - IO_L17N_T2U_N9_AD10N_65
#set_property IOSTANDARD  POD12    [get_ports "DDR4_SODIMM_DQ2"] ;# Bank  65 VCCO - VCC1V2   - IO_L17N_T2U_N9_AD10N_65
#set_property PACKAGE_PIN AF21     [get_ports "DDR4_SODIMM_DQ3"] ;# Bank  65 VCCO - VCC1V2   - IO_L17P_T2U_N8_AD10P_65
#set_property IOSTANDARD  POD12    [get_ports "DDR4_SODIMM_DQ3"] ;# Bank  65 VCCO - VCC1V2   - IO_L17P_T2U_N8_AD10P_65
#set_property PACKAGE_PIN AG23     [get_ports "DDR4_SODIMM_DQS0_C"] ;# Bank  65 VCCO - VCC1V2   - IO_L16N_T2U_N7_QBC_AD3N_65
#set_property IOSTANDARD  DIFF_POD12 [get_ports "DDR4_SODIMM_DQS0_C"] ;# Bank  65 VCCO - VCC1V2   - IO_L16N_T2U_N7_QBC_AD3N_65
#set_property PACKAGE_PIN AF23     [get_ports "DDR4_SODIMM_DQS0_T"] ;# Bank  65 VCCO - VCC1V2   - IO_L16P_T2U_N6_QBC_AD3P_65
#set_property IOSTANDARD  DIFF_POD12[get_ports "DDR4_SODIMM_DQS0_T"] ;# Bank  65 VCCO - VCC1V2   - IO_L16P_T2U_N6_QBC_AD3P_65
#set_property PACKAGE_PIN AG20     [get_ports "DDR4_SODIMM_DQ4"] ;# Bank  65 VCCO - VCC1V2   - IO_L15N_T2L_N5_AD11N_65
#set_property IOSTANDARD  POD12    [get_ports "DDR4_SODIMM_DQ4"] ;# Bank  65 VCCO - VCC1V2   - IO_L15N_T2L_N5_AD11N_65
#set_property PACKAGE_PIN AG19     [get_ports "DDR4_SODIMM_DQ5"] ;# Bank  65 VCCO - VCC1V2   - IO_L15P_T2L_N4_AD11P_65
#set_property IOSTANDARD  POD12    [get_ports "DDR4_SODIMM_DQ5"] ;# Bank  65 VCCO - VCC1V2   - IO_L15P_T2L_N4_AD11P_65
#set_property PACKAGE_PIN AH21     [get_ports "DDR4_SODIMM_DQ6"] ;# Bank  65 VCCO - VCC1V2   - IO_L14N_T2L_N3_GC_65
#set_property IOSTANDARD  POD12    [get_ports "DDR4_SODIMM_DQ6"] ;# Bank  65 VCCO - VCC1V2   - IO_L14N_T2L_N3_GC_65
#set_property PACKAGE_PIN AG21     [get_ports "DDR4_SODIMM_DQ7"] ;# Bank  65 VCCO - VCC1V2   - IO_L14P_T2L_N2_GC_65
#set_property IOSTANDARD  POD12    [get_ports "DDR4_SODIMM_DQ7"] ;# Bank  65 VCCO - VCC1V2   - IO_L14P_T2L_N2_GC_65
#set_property PACKAGE_PIN AH23     [get_ports "6N12433"] ;# Bank  65 VCCO - VCC1V2   - IO_L13N_T2L_N1_GC_QBC_65
#set_property IOSTANDARD  LVCMOSxx [get_ports "6N12433"] ;# Bank  65 VCCO - VCC1V2   - IO_L13N_T2L_N1_GC_QBC_65
#set_property PACKAGE_PIN AH22     [get_ports "DDR4_SODIMM_DM0_B"] ;# Bank  65 VCCO - VCC1V2   - IO_L13P_T2L_N0_GC_QBC_65
#set_property IOSTANDARD  POD12    [get_ports "DDR4_SODIMM_DM0_B"] ;# Bank  65 VCCO - VCC1V2   - IO_L13P_T2L_N0_GC_QBC_65
#set_property PACKAGE_PIN AJ22     [get_ports "DDR4_SODIMM_DQ16"] ;# Bank  65 VCCO - VCC1V2   - IO_L12N_T1U_N11_GC_65
#set_property IOSTANDARD  POD12    [get_ports "DDR4_SODIMM_DQ16"] ;# Bank  65 VCCO - VCC1V2   - IO_L12N_T1U_N11_GC_65
#set_property PACKAGE_PIN AJ21     [get_ports "DDR4_SODIMM_DQ17"] ;# Bank  65 VCCO - VCC1V2   - IO_L12P_T1U_N10_GC_65
#set_property IOSTANDARD  POD12    [get_ports "DDR4_SODIMM_DQ17"] ;# Bank  65 VCCO - VCC1V2   - IO_L12P_T1U_N10_GC_65
#set_property PACKAGE_PIN AK20     [get_ports "DDR4_SODIMM_DQ18"] ;# Bank  65 VCCO - VCC1V2   - IO_L11N_T1U_N9_GC_65
#set_property IOSTANDARD  POD12    [get_ports "DDR4_SODIMM_DQ18"] ;# Bank  65 VCCO - VCC1V2   - IO_L11N_T1U_N9_GC_65
#set_property PACKAGE_PIN AJ20     [get_ports "DDR4_SODIMM_DQ19"] ;# Bank  65 VCCO - VCC1V2   - IO_L11P_T1U_N8_GC_65
#set_property IOSTANDARD  POD12    [get_ports "DDR4_SODIMM_DQ19"] ;# Bank  65 VCCO - VCC1V2   - IO_L11P_T1U_N8_GC_65
#set_property PACKAGE_PIN AK23     [get_ports "DDR4_SODIMM_DQS2_C"] ;# Bank  65 VCCO - VCC1V2   - IO_L10N_T1U_N7_QBC_AD4N_65
#set_property IOSTANDARD  DIFF_POD12 [get_ports "DDR4_SODIMM_DQS2_C"] ;# Bank  65 VCCO - VCC1V2   - IO_L10N_T1U_N7_QBC_AD4N_65
#set_property PACKAGE_PIN AK22     [get_ports "DDR4_SODIMM_DQS2_T"] ;# Bank  65 VCCO - VCC1V2   - IO_L10P_T1U_N6_QBC_AD4P_65
#set_property IOSTANDARD  DIFF_POD12 [get_ports "DDR4_SODIMM_DQS2_T"] ;# Bank  65 VCCO - VCC1V2   - IO_L10P_T1U_N6_QBC_AD4P_65
#set_property PACKAGE_PIN AK19     [get_ports "DDR4_SODIMM_DQ20"] ;# Bank  65 VCCO - VCC1V2   - IO_L9N_T1L_N5_AD12N_65
#set_property IOSTANDARD  POD12    [get_ports "DDR4_SODIMM_DQ20"] ;# Bank  65 VCCO - VCC1V2   - IO_L9N_T1L_N5_AD12N_65
#set_property PACKAGE_PIN AJ19     [get_ports "DDR4_SODIMM_DQ21"] ;# Bank  65 VCCO - VCC1V2   - IO_L9P_T1L_N4_AD12P_65
#set_property IOSTANDARD  POD12    [get_ports "DDR4_SODIMM_DQ21"] ;# Bank  65 VCCO - VCC1V2   - IO_L9P_T1L_N4_AD12P_65
#set_property PACKAGE_PIN AL23     [get_ports "DDR4_SODIMM_DQ22"] ;# Bank  65 VCCO - VCC1V2   - IO_L8N_T1L_N3_AD5N_65
#set_property IOSTANDARD  POD12    [get_ports "DDR4_SODIMM_DQ22"] ;# Bank  65 VCCO - VCC1V2   - IO_L8N_T1L_N3_AD5N_65
#set_property PACKAGE_PIN AL22     [get_ports "DDR4_SODIMM_DQ23"] ;# Bank  65 VCCO - VCC1V2   - IO_L8P_T1L_N2_AD5P_65
#set_property IOSTANDARD  POD12    [get_ports "DDR4_SODIMM_DQ23"] ;# Bank  65 VCCO - VCC1V2   - IO_L8P_T1L_N2_AD5P_65
#set_property PACKAGE_PIN AL21     [get_ports "6N12427"] ;# Bank  65 VCCO - VCC1V2   - IO_L7N_T1L_N1_QBC_AD13N_65
#set_property IOSTANDARD  LVCMOSxx [get_ports "6N12427"] ;# Bank  65 VCCO - VCC1V2   - IO_L7N_T1L_N1_QBC_AD13N_65
#set_property PACKAGE_PIN AL20     [get_ports "DDR4_SODIMM_DM2_B"] ;# Bank  65 VCCO - VCC1V2   - IO_L7P_T1L_N0_QBC_AD13P_65
#set_property IOSTANDARD  POD12    [get_ports "DDR4_SODIMM_DM2_B"] ;# Bank  65 VCCO - VCC1V2   - IO_L7P_T1L_N0_QBC_AD13P_65
#set_property PACKAGE_PIN AH19     [get_ports "6N12430"] ;# Bank  65 VCCO - VCC1V2   - IO_T1U_N12_65
#set_property IOSTANDARD  LVCMOSxx [get_ports "6N12430"] ;# Bank  65 VCCO - VCC1V2   - IO_T1U_N12_65
#set_property PACKAGE_PIN AM20     [get_ports "VRP_65"] ;# Bank  65 VCCO - VCC1V2   - IO_T0U_N12_VRP_65
#set_property IOSTANDARD  LVCMOSxx [get_ports "VRP_65"] ;# Bank  65 VCCO - VCC1V2   - IO_T0U_N12_VRP_65
#set_property PACKAGE_PIN AN23     [get_ports "DDR4_SODIMM_DQ24"] ;# Bank  65 VCCO - VCC1V2   - IO_L6N_T0U_N11_AD6N_65
#set_property IOSTANDARD  POD12    [get_ports "DDR4_SODIMM_DQ24"] ;# Bank  65 VCCO - VCC1V2   - IO_L6N_T0U_N11_AD6N_65
#set_property PACKAGE_PIN AM23     [get_ports "DDR4_SODIMM_DQ25"] ;# Bank  65 VCCO - VCC1V2   - IO_L6P_T0U_N10_AD6P_65
#set_property IOSTANDARD  POD12    [get_ports "DDR4_SODIMM_DQ25"] ;# Bank  65 VCCO - VCC1V2   - IO_L6P_T0U_N10_AD6P_65
#set_property PACKAGE_PIN AP23     [get_ports "DDR4_SODIMM_DQ26"] ;# Bank  65 VCCO - VCC1V2   - IO_L5N_T0U_N9_AD14N_65
#set_property IOSTANDARD  POD12    [get_ports "DDR4_SODIMM_DQ26"] ;# Bank  65 VCCO - VCC1V2   - IO_L5N_T0U_N9_AD14N_65
#set_property PACKAGE_PIN AN22     [get_ports "DDR4_SODIMM_DQ27"] ;# Bank  65 VCCO - VCC1V2   - IO_L5P_T0U_N8_AD14P_65
#set_property IOSTANDARD  POD12    [get_ports "DDR4_SODIMM_DQ27"] ;# Bank  65 VCCO - VCC1V2   - IO_L5P_T0U_N8_AD14P_65
#set_property PACKAGE_PIN AN21     [get_ports "DDR4_SODIMM_DQS3_C"] ;# Bank  65 VCCO - VCC1V2   - IO_L4N_T0U_N7_DBC_AD7N_65
#set_property IOSTANDARD  DIFF_POD12 [get_ports "DDR4_SODIMM_DQS3_C"] ;# Bank  65 VCCO - VCC1V2   - IO_L4N_T0U_N7_DBC_AD7N_65
#set_property PACKAGE_PIN AM21     [get_ports "DDR4_SODIMM_DQS3_T"] ;# Bank  65 VCCO - VCC1V2   - IO_L4P_T0U_N6_DBC_AD7P_SMBALERT_65
#set_property IOSTANDARD  DIFF_POD12 [get_ports "DDR4_SODIMM_DQS3_T"] ;# Bank  65 VCCO - VCC1V2   - IO_L4P_T0U_N6_DBC_AD7P_SMBALERT_65
#set_property PACKAGE_PIN AP22     [get_ports "DDR4_SODIMM_DQ28"] ;# Bank  65 VCCO - VCC1V2   - IO_L3N_T0L_N5_AD15N_65
#set_property IOSTANDARD  POD12    [get_ports "DDR4_SODIMM_DQ28"] ;# Bank  65 VCCO - VCC1V2   - IO_L3N_T0L_N5_AD15N_65
#set_property PACKAGE_PIN AP21     [get_ports "DDR4_SODIMM_DQ29"] ;# Bank  65 VCCO - VCC1V2   - IO_L3P_T0L_N4_AD15P_65
#set_property IOSTANDARD  POD12    [get_ports "DDR4_SODIMM_DQ29"] ;# Bank  65 VCCO - VCC1V2   - IO_L3P_T0L_N4_AD15P_65
#set_property PACKAGE_PIN AN19     [get_ports "DDR4_SODIMM_DQ30"] ;# Bank  65 VCCO - VCC1V2   - IO_L2N_T0L_N3_65
#set_property IOSTANDARD  POD12    [get_ports "DDR4_SODIMM_DQ30"] ;# Bank  65 VCCO - VCC1V2   - IO_L2N_T0L_N3_65
#set_property PACKAGE_PIN AM19     [get_ports "DDR4_SODIMM_DQ31"] ;# Bank  65 VCCO - VCC1V2   - IO_L2P_T0L_N2_65
#set_property IOSTANDARD  POD12    [get_ports "DDR4_SODIMM_DQ31"] ;# Bank  65 VCCO - VCC1V2   - IO_L2P_T0L_N2_65
#set_property PACKAGE_PIN AP20     [get_ports "6N12401"] ;# Bank  65 VCCO - VCC1V2   - IO_L1N_T0L_N1_DBC_65
#set_property IOSTANDARD  LVCMOSxx [get_ports "6N12401"] ;# Bank  65 VCCO - VCC1V2   - IO_L1N_T0L_N1_DBC_65
#set_property PACKAGE_PIN AP19     [get_ports "DDR4_SODIMM_DM3_B"] ;# Bank  65 VCCO - VCC1V2   - IO_L1P_T0L_N0_DBC_65
#set_property IOSTANDARD  POD12    [get_ports "DDR4_SODIMM_DM3_B"] ;# Bank  65 VCCO - VCC1V2   - IO_L1P_T0L_N0_DBC_65
#Other net   PACKAGE_PIN AB20     - 6N11582                   Bank  65 - VREF_65
#set_property PACKAGE_PIN AD16     [get_ports "DDR4_SODIMM_PARITY"] ;# Bank  64 VCCO - VCC1V2   - IO_L24N_T3U_N11_64
#set_property IOSTANDARD  POD12    [get_ports "DDR4_SODIMM_PARITY"] ;# Bank  64 VCCO - VCC1V2   - IO_L24N_T3U_N11_64
#set_property PACKAGE_PIN AD17     [get_ports "DDR4_SODIMM_CKE0"] ;# Bank  64 VCCO - VCC1V2   - IO_L24P_T3U_N10_64
#set_property IOSTANDARD  SSTL12   [get_ports "DDR4_SODIMM_CKE0"] ;# Bank  64 VCCO - VCC1V2   - IO_L24P_T3U_N10_64
#set_property PACKAGE_PIN AB14     [get_ports "DDR4_SODIMM_RESET_B"] ;# Bank  64 VCCO - VCC1V2   - IO_L23N_T3U_N9_64
#set_property IOSTANDARD  LVCMOS12 [get_ports "DDR4_SODIMM_RESET_B"] ;# Bank  64 VCCO - VCC1V2   - IO_L23N_T3U_N9_64
#set_property PACKAGE_PIN AA14     [get_ports "DDR4_SODIMM_CAS_B"] ;# Bank  64 VCCO - VCC1V2   - IO_L23P_T3U_N8_64
#set_property IOSTANDARD  SSTL12   [get_ports "DDR4_SODIMM_CAS_B"] ;# Bank  64 VCCO - VCC1V2   - IO_L23P_T3U_N8_64
#set_property PACKAGE_PIN AA15     [get_ports "DDR4_SODIMM_CS0_B"] ;# Bank  64 VCCO - VCC1V2   - IO_L22N_T3U_N7_DBC_AD0N_64
#set_property IOSTANDARD  SSTL12   [get_ports "DDR4_SODIMM_CS0_B"] ;# Bank  64 VCCO - VCC1V2   - IO_L22N_T3U_N7_DBC_AD0N_64
#set_property PACKAGE_PIN AA16     [get_ports "DDR4_SODIMM_WE_B"] ;# Bank  64 VCCO - VCC1V2   - IO_L22P_T3U_N6_DBC_AD0P_64
#set_property IOSTANDARD  SSTL12   [get_ports "DDR4_SODIMM_WE_B"] ;# Bank  64 VCCO - VCC1V2   - IO_L22P_T3U_N6_DBC_AD0P_64
#set_property PACKAGE_PIN AB15     [get_ports "DDR4_SODIMM_ALERT_B"] ;# Bank  64 VCCO - VCC1V2   - IO_L21N_T3L_N5_AD8N_64
#set_property IOSTANDARD  POD12    [get_ports "DDR4_SODIMM_ALERT_B"] ;# Bank  64 VCCO - VCC1V2   - IO_L21N_T3L_N5_AD8N_64
#set_property PACKAGE_PIN AB16     [get_ports "DDR4_SODIMM_BG1"] ;# Bank  64 VCCO - VCC1V2   - IO_L21P_T3L_N4_AD8P_64
#set_property IOSTANDARD  SSTL12   [get_ports "DDR4_SODIMM_BG1"] ;# Bank  64 VCCO - VCC1V2   - IO_L21P_T3L_N4_AD8P_64
#set_property PACKAGE_PIN AC16     [get_ports "DDR4_SODIMM_BG0"] ;# Bank  64 VCCO - VCC1V2   - IO_L20N_T3L_N3_AD1N_64
#set_property IOSTANDARD  SSTL12   [get_ports "DDR4_SODIMM_BG0"] ;# Bank  64 VCCO - VCC1V2   - IO_L20N_T3L_N3_AD1N_64
#set_property PACKAGE_PIN AC17     [get_ports "DDR4_SODIMM_ACT_B"] ;# Bank  64 VCCO - VCC1V2   - IO_L20P_T3L_N2_AD1P_64
#set_property IOSTANDARD  SSTL12   [get_ports "DDR4_SODIMM_ACT_B"] ;# Bank  64 VCCO - VCC1V2   - IO_L20P_T3L_N2_AD1P_64
#set_property PACKAGE_PIN AE15     [get_ports "DDR4_SODIMM_ODT0"] ;# Bank  64 VCCO - VCC1V2   - IO_L19N_T3L_N1_DBC_AD9N_64
#set_property IOSTANDARD  SSTL12   [get_ports "DDR4_SODIMM_ODT0"] ;# Bank  64 VCCO - VCC1V2   - IO_L19N_T3L_N1_DBC_AD9N_64
#set_property PACKAGE_PIN AD15     [get_ports "DDR4_SODIMM_RAS_B"] ;# Bank  64 VCCO - VCC1V2   - IO_L19P_T3L_N0_DBC_AD9P_64
#set_property IOSTANDARD  SSTL12   [get_ports "DDR4_SODIMM_RAS_B"] ;# Bank  64 VCCO - VCC1V2   - IO_L19P_T3L_N0_DBC_AD9P_64
#set_property PACKAGE_PIN AA17     [get_ports "6N12707"] ;# Bank  64 VCCO - VCC1V2   - IO_T3U_N12_64
#set_property IOSTANDARD  LVCMOSxx [get_ports "6N12707"] ;# Bank  64 VCCO - VCC1V2   - IO_T3U_N12_64
#set_property PACKAGE_PIN AH16     [get_ports "DDR4_SODIMM_A0"] ;# Bank  64 VCCO - VCC1V2   - IO_T2U_N12_64
#set_property IOSTANDARD  SSTL12   [get_ports "DDR4_SODIMM_A0"] ;# Bank  64 VCCO - VCC1V2   - IO_T2U_N12_64
#set_property PACKAGE_PIN AG14     [get_ports "DDR4_SODIMM_A1"] ;# Bank  64 VCCO - VCC1V2   - IO_L18N_T2U_N11_AD2N_64
#set_property IOSTANDARD  SSTL12   [get_ports "DDR4_SODIMM_A1"] ;# Bank  64 VCCO - VCC1V2   - IO_L18N_T2U_N11_AD2N_64
#set_property PACKAGE_PIN AG15     [get_ports "DDR4_SODIMM_A2"] ;# Bank  64 VCCO - VCC1V2   - IO_L18P_T2U_N10_AD2P_64
#set_property IOSTANDARD  SSTL12   [get_ports "DDR4_SODIMM_A2"] ;# Bank  64 VCCO - VCC1V2   - IO_L18P_T2U_N10_AD2P_64
#set_property PACKAGE_PIN AF15     [get_ports "DDR4_SODIMM_A3"] ;# Bank  64 VCCO - VCC1V2   - IO_L17N_T2U_N9_AD10N_64
#set_property IOSTANDARD  SSTL12   [get_ports "DDR4_SODIMM_A3"] ;# Bank  64 VCCO - VCC1V2   - IO_L17N_T2U_N9_AD10N_64
#set_property PACKAGE_PIN AF16     [get_ports "DDR4_SODIMM_A4"] ;# Bank  64 VCCO - VCC1V2   - IO_L17P_T2U_N8_AD10P_64
#set_property IOSTANDARD  SSTL12   [get_ports "DDR4_SODIMM_A4"] ;# Bank  64 VCCO - VCC1V2   - IO_L17P_T2U_N8_AD10P_64
#set_property PACKAGE_PIN AJ14     [get_ports "DDR4_SODIMM_A5"] ;# Bank  64 VCCO - VCC1V2   - IO_L16N_T2U_N7_QBC_AD3N_64
#set_property IOSTANDARD  SSTL12   [get_ports "DDR4_SODIMM_A5"] ;# Bank  64 VCCO - VCC1V2   - IO_L16N_T2U_N7_QBC_AD3N_64
#set_property PACKAGE_PIN AH14     [get_ports "DDR4_SODIMM_A6"] ;# Bank  64 VCCO - VCC1V2   - IO_L16P_T2U_N6_QBC_AD3P_64
#set_property IOSTANDARD  SSTL12   [get_ports "DDR4_SODIMM_A6"] ;# Bank  64 VCCO - VCC1V2   - IO_L16P_T2U_N6_QBC_AD3P_64
#set_property PACKAGE_PIN AF17     [get_ports "DDR4_SODIMM_A7"] ;# Bank  64 VCCO - VCC1V2   - IO_L15N_T2L_N5_AD11N_64
#set_property IOSTANDARD  SSTL12   [get_ports "DDR4_SODIMM_A7"] ;# Bank  64 VCCO - VCC1V2   - IO_L15N_T2L_N5_AD11N_64
#set_property PACKAGE_PIN AE17     [get_ports "6N12705"] ;# Bank  64 VCCO - VCC1V2   - IO_L15P_T2L_N4_AD11P_64
#set_property IOSTANDARD  LVCMOSxx [get_ports "6N12705"] ;# Bank  64 VCCO - VCC1V2   - IO_L15P_T2L_N4_AD11P_64
#set_property PACKAGE_PIN AG18     [get_ports "DDR4_SODIMM_CK0_C"] ;# Bank  64 VCCO - VCC1V2   - IO_L14N_T2L_N3_GC_64
#set_property IOSTANDARD  DIFF_POD12 [get_ports "DDR4_SODIMM_CK0_C"] ;# Bank  64 VCCO - VCC1V2   - IO_L14N_T2L_N3_GC_64
#set_property PACKAGE_PIN AF18     [get_ports "DDR4_SODIMM_CK0_T"] ;# Bank  64 VCCO - VCC1V2   - IO_L14P_T2L_N2_GC_64
#set_property IOSTANDARD  DIFF_POD12 [get_ports "DDR4_SODIMM_CK0_T"] ;# Bank  64 VCCO - VCC1V2   - IO_L14P_T2L_N2_GC_64
#set_property PACKAGE_PIN AH17     [get_ports "CLK_300_N"] ;# Bank  64 VCCO - VCC1V2   - IO_L13N_T2L_N1_GC_QBC_64
#set_property IOSTANDARD  DIFF_SSTL12 [get_ports "CLK_300_N"] ;# Bank  64 VCCO - VCC1V2   - IO_L13N_T2L_N1_GC_QBC_64
#set_property PACKAGE_PIN AH18     [get_ports "CLK_300_P"] ;# Bank  64 VCCO - VCC1V2   - IO_L13P_T2L_N0_GC_QBC_64
#set_property IOSTANDARD  DIFF_SSTL12 [get_ports "CLK_300_P"] ;# Bank  64 VCCO - VCC1V2   - IO_L13P_T2L_N0_GC_QBC_64
#set_property PACKAGE_PIN AJ15     [get_ports "DDR4_SODIMM_CK1_C"] ;# Bank  64 VCCO - VCC1V2   - IO_L12N_T1U_N11_GC_64
#set_property IOSTANDARD  DIFF_POD12 [get_ports "DDR4_SODIMM_CK1_C"] ;# Bank  64 VCCO - VCC1V2   - IO_L12N_T1U_N11_GC_64
#set_property PACKAGE_PIN AJ16     [get_ports "DDR4_SODIMM_CK1_T"] ;# Bank  64 VCCO - VCC1V2   - IO_L12P_T1U_N10_GC_64
#set_property IOSTANDARD  DIFF_POD12 [get_ports "DDR4_SODIMM_CK1_T"] ;# Bank  64 VCCO - VCC1V2   - IO_L12P_T1U_N10_GC_64
#set_property PACKAGE_PIN AK17     [get_ports "DDR4_SODIMM_A8"] ;# Bank  64 VCCO - VCC1V2   - IO_L11N_T1U_N9_GC_64
#set_property IOSTANDARD  SSTL12   [get_ports "DDR4_SODIMM_A8"] ;# Bank  64 VCCO - VCC1V2   - IO_L11N_T1U_N9_GC_64
#set_property PACKAGE_PIN AJ17     [get_ports "DDR4_SODIMM_A9"] ;# Bank  64 VCCO - VCC1V2   - IO_L11P_T1U_N8_GC_64
#set_property IOSTANDARD  SSTL12   [get_ports "DDR4_SODIMM_A9"] ;# Bank  64 VCCO - VCC1V2   - IO_L11P_T1U_N8_GC_64
#set_property PACKAGE_PIN AK14     [get_ports "DDR4_SODIMM_A10"] ;# Bank  64 VCCO - VCC1V2   - IO_L10N_T1U_N7_QBC_AD4N_64
#set_property IOSTANDARD  SSTL12   [get_ports "DDR4_SODIMM_A10"] ;# Bank  64 VCCO - VCC1V2   - IO_L10N_T1U_N7_QBC_AD4N_64
#set_property PACKAGE_PIN AK15     [get_ports "DDR4_SODIMM_A11"] ;# Bank  64 VCCO - VCC1V2   - IO_L10P_T1U_N6_QBC_AD4P_64
#set_property IOSTANDARD  SSTL12   [get_ports "DDR4_SODIMM_A11"] ;# Bank  64 VCCO - VCC1V2   - IO_L10P_T1U_N6_QBC_AD4P_64
#set_property PACKAGE_PIN AL18     [get_ports "DDR4_SODIMM_A12"] ;# Bank  64 VCCO - VCC1V2   - IO_L9N_T1L_N5_AD12N_64
#set_property IOSTANDARD  SSTL12   [get_ports "DDR4_SODIMM_A12"] ;# Bank  64 VCCO - VCC1V2   - IO_L9N_T1L_N5_AD12N_64
#set_property PACKAGE_PIN AK18     [get_ports "DDR4_SODIMM_A13"] ;# Bank  64 VCCO - VCC1V2   - IO_L9P_T1L_N4_AD12P_64
#set_property IOSTANDARD  SSTL12   [get_ports "DDR4_SODIMM_A13"] ;# Bank  64 VCCO - VCC1V2   - IO_L9P_T1L_N4_AD12P_64
#set_property PACKAGE_PIN AL15     [get_ports "DDR4_SODIMM_BA0"] ;# Bank  64 VCCO - VCC1V2   - IO_L8N_T1L_N3_AD5N_64
#set_property IOSTANDARD  SSTL12   [get_ports "DDR4_SODIMM_BA0"] ;# Bank  64 VCCO - VCC1V2   - IO_L8N_T1L_N3_AD5N_64
#set_property PACKAGE_PIN AL16     [get_ports "DDR4_SODIMM_BA1"] ;# Bank  64 VCCO - VCC1V2   - IO_L8P_T1L_N2_AD5P_64
#set_property IOSTANDARD  SSTL12   [get_ports "DDR4_SODIMM_BA1"] ;# Bank  64 VCCO - VCC1V2   - IO_L8P_T1L_N2_AD5P_64
#set_property PACKAGE_PIN AM15     [get_ports "DDR4_SODIMM_CKE1"] ;# Bank  64 VCCO - VCC1V2   - IO_L7N_T1L_N1_QBC_AD13N_64
#set_property IOSTANDARD  SSTL12   [get_ports "DDR4_SODIMM_CKE1"] ;# Bank  64 VCCO - VCC1V2   - IO_L7N_T1L_N1_QBC_AD13N_64
#set_property PACKAGE_PIN AM16     [get_ports "DDR4_SODIMM_ODT1"] ;# Bank  64 VCCO - VCC1V2   - IO_L7P_T1L_N0_QBC_AD13P_64
#set_property IOSTANDARD  SSTL12   [get_ports "DDR4_SODIMM_ODT1"] ;# Bank  64 VCCO - VCC1V2   - IO_L7P_T1L_N0_QBC_AD13P_64
#set_property PACKAGE_PIN AL17     [get_ports "DDR4_SODIMM_CS1_B"] ;# Bank  64 VCCO - VCC1V2   - IO_T1U_N12_64
#set_property IOSTANDARD  SSTL12   [get_ports "DDR4_SODIMM_CS1_B"] ;# Bank  64 VCCO - VCC1V2   - IO_T1U_N12_64
#set_property PACKAGE_PIN AP14     [get_ports "VRP_64"] ;# Bank  64 VCCO - VCC1V2   - IO_T0U_N12_VRP_64
#set_property IOSTANDARD  LVCMOSxx [get_ports "VRP_64"] ;# Bank  64 VCCO - VCC1V2   - IO_T0U_N12_VRP_64
#set_property PACKAGE_PIN AN16     [get_ports "DDR4_SODIMM_CS3_B"] ;# Bank  64 VCCO - VCC1V2   - IO_L6N_T0U_N11_AD6N_64
#set_property IOSTANDARD  SSTL12   [get_ports "DDR4_SODIMM_CS3_B"] ;# Bank  64 VCCO - VCC1V2   - IO_L6N_T0U_N11_AD6N_64
#set_property PACKAGE_PIN AN17     [get_ports "DDR4_SODIMM_CS2_B"] ;# Bank  64 VCCO - VCC1V2   - IO_L6P_T0U_N10_AD6P_64
#set_property IOSTANDARD  SSTL12   [get_ports "DDR4_SODIMM_CS2_B"] ;# Bank  64 VCCO - VCC1V2   - IO_L6P_T0U_N10_AD6P_64
#set_property PACKAGE_PIN AP15     [get_ports "6N12788"] ;# Bank  64 VCCO - VCC1V2   - IO_L5N_T0U_N9_AD14N_64
#set_property IOSTANDARD  LVCMOSxx [get_ports "6N12788"] ;# Bank  64 VCCO - VCC1V2   - IO_L5N_T0U_N9_AD14N_64
#set_property PACKAGE_PIN AP16     [get_ports "6N12789"] ;# Bank  64 VCCO - VCC1V2   - IO_L5P_T0U_N8_AD14P_64
#set_property IOSTANDARD  LVCMOSxx [get_ports "6N12789"] ;# Bank  64 VCCO - VCC1V2   - IO_L5P_T0U_N8_AD14P_64
#set_property PACKAGE_PIN AN14     [get_ports "6N12782"] ;# Bank  64 VCCO - VCC1V2   - IO_L4N_T0U_N7_DBC_AD7N_64
#set_property IOSTANDARD  LVCMOSxx [get_ports "6N12782"] ;# Bank  64 VCCO - VCC1V2   - IO_L4N_T0U_N7_DBC_AD7N_64
#set_property PACKAGE_PIN AM14     [get_ports "6N12783"] ;# Bank  64 VCCO - VCC1V2   - IO_L4P_T0U_N6_DBC_AD7P_64
#set_property IOSTANDARD  LVCMOSxx [get_ports "6N12783"] ;# Bank  64 VCCO - VCC1V2   - IO_L4P_T0U_N6_DBC_AD7P_64
#set_property PACKAGE_PIN AN18     [get_ports "6N12780"] ;# Bank  64 VCCO - VCC1V2   - IO_L3N_T0L_N5_AD15N_64
#set_property IOSTANDARD  LVCMOSxx [get_ports "6N12780"] ;# Bank  64 VCCO - VCC1V2   - IO_L3N_T0L_N5_AD15N_64
#set_property PACKAGE_PIN AM18     [get_ports "6N12781"] ;# Bank  64 VCCO - VCC1V2   - IO_L3P_T0L_N4_AD15P_64
#set_property IOSTANDARD  LVCMOSxx [get_ports "6N12781"] ;# Bank  64 VCCO - VCC1V2   - IO_L3P_T0L_N4_AD15P_64
#set_property PACKAGE_PIN AP13     [get_ports "6N12774"] ;# Bank  64 VCCO - VCC1V2   - IO_L2N_T0L_N3_64
#set_property IOSTANDARD  LVCMOSxx [get_ports "6N12774"] ;# Bank  64 VCCO - VCC1V2   - IO_L2N_T0L_N3_64
#set_property PACKAGE_PIN AN13     [get_ports "6N12775"] ;# Bank  64 VCCO - VCC1V2   - IO_L2P_T0L_N2_64
#set_property IOSTANDARD  LVCMOSxx [get_ports "6N12775"] ;# Bank  64 VCCO - VCC1V2   - IO_L2P_T0L_N2_64
#set_property PACKAGE_PIN AP17     [get_ports "6N12772"] ;# Bank  64 VCCO - VCC1V2   - IO_L1N_T0L_N1_DBC_64
#set_property IOSTANDARD  LVCMOSxx [get_ports "6N12772"] ;# Bank  64 VCCO - VCC1V2   - IO_L1N_T0L_N1_DBC_64
#set_property PACKAGE_PIN AP18     [get_ports "6N12773"] ;# Bank  64 VCCO - VCC1V2   - IO_L1P_T0L_N0_DBC_64
#set_property IOSTANDARD  LVCMOSxxn [get_ports "6N12773"] ;# Bank  64 VCCO - VCC1V2   - IO_L1P_T0L_N0_DBC_64
#Other net   PACKAGE_PIN AG16     - 6N11370                   Bank  64 - VREF_64
#set_property PACKAGE_PIN E5       [get_ports "HDMI_RX_PWR_DET"] ;# Bank  88 VCCO - VCC3V3   - IO_L12N_AD8N_88
#set_property IOSTANDARD  LVCMOS33 [get_ports "HDMI_RX_PWR_DET"] ;# Bank  88 VCCO - VCC3V3   - IO_L12N_AD8N_88
#set_property PACKAGE_PIN F6       [get_ports "HDMI_RX_HPD"] ;# Bank  88 VCCO - VCC3V3   - IO_L12P_AD8P_88
#set_property IOSTANDARD  LVCMOS33 [get_ports "HDMI_RX_HPD"] ;# Bank  88 VCCO - VCC3V3   - IO_L12P_AD8P_88
#set_property PACKAGE_PIN D5       [get_ports "GPIO_LED_0_LS"] ;# Bank  88 VCCO - VCC3V3   - IO_L11N_AD9N_88
#set_property IOSTANDARD  LVCMOS33 [get_ports "GPIO_LED_0_LS"] ;# Bank  88 VCCO - VCC3V3   - IO_L11N_AD9N_88
#set_property PACKAGE_PIN D6       [get_ports "GPIO_LED_1_LS"] ;# Bank  88 VCCO - VCC3V3   - IO_L11P_AD9P_88
#set_property IOSTANDARD  LVCMOS33 [get_ports "GPIO_LED_1_LS"] ;# Bank  88 VCCO - VCC3V3   - IO_L11P_AD9P_88
#set_property PACKAGE_PIN A5       [get_ports "GPIO_LED_2_LS"] ;# Bank  88 VCCO - VCC3V3   - IO_L10N_AD10N_88
#set_property IOSTANDARD  LVCMOS33 [get_ports "GPIO_LED_2_LS"] ;# Bank  88 VCCO - VCC3V3   - IO_L10N_AD10N_88
#set_property PACKAGE_PIN B5       [get_ports "GPIO_LED_3_LS"] ;# Bank  88 VCCO - VCC3V3   - IO_L10P_AD10P_88
#set_property IOSTANDARD  LVCMOS33 [get_ports "GPIO_LED_3_LS"] ;# Bank  88 VCCO - VCC3V3   - IO_L10P_AD10P_88
#set_property PACKAGE_PIN F4       [get_ports "GPIO_DIP_SW3"] ;# Bank  88 VCCO - VCC3V3   - IO_L9N_AD11N_88
#set_property IOSTANDARD  LVCMOS33 [get_ports "GPIO_DIP_SW3"] ;# Bank  88 VCCO - VCC3V3   - IO_L9N_AD11N_88
#set_property PACKAGE_PIN F5       [get_ports "GPIO_DIP_SW2"] ;# Bank  88 VCCO - VCC3V3   - IO_L9P_AD11P_88
#set_property IOSTANDARD  LVCMOS33 [get_ports "GPIO_DIP_SW2"] ;# Bank  88 VCCO - VCC3V3   - IO_L9P_AD11P_88
#set_property PACKAGE_PIN D4       [get_ports "GPIO_DIP_SW1"] ;# Bank  88 VCCO - VCC3V3   - IO_L8N_HDGC_88
#set_property IOSTANDARD  LVCMOS33 [get_ports "GPIO_DIP_SW1"] ;# Bank  88 VCCO - VCC3V3   - IO_L8N_HDGC_88
#set_property PACKAGE_PIN E4       [get_ports "GPIO_DIP_SW0"] ;# Bank  88 VCCO - VCC3V3   - IO_L8P_HDGC_88
#set_property IOSTANDARD  LVCMOS33 [get_ports "GPIO_DIP_SW0"] ;# Bank  88 VCCO - VCC3V3   - IO_L8P_HDGC_88
#set_property PACKAGE_PIN B4       [get_ports "GPIO_PB_SW0"] ;# Bank  88 VCCO - VCC3V3   - IO_L7N_HDGC_88
#set_property IOSTANDARD  LVCMOS33 [get_ports "GPIO_PB_SW0"] ;# Bank  88 VCCO - VCC3V3   - IO_L7N_HDGC_88
#set_property PACKAGE_PIN C4       [get_ports "GPIO_PB_SW1"] ;# Bank  88 VCCO - VCC3V3   - IO_L7P_HDGC_88
#set_property IOSTANDARD  LVCMOS33 [get_ports "GPIO_PB_SW1"] ;# Bank  88 VCCO - VCC3V3   - IO_L7P_HDGC_88
#set_property PACKAGE_PIN B3       [get_ports "GPIO_PB_SW2"] ;# Bank  88 VCCO - VCC3V3   - IO_L6N_HDGC_88
#set_property IOSTANDARD  LVCMOS33 [get_ports "GPIO_PB_SW2"] ;# Bank  88 VCCO - VCC3V3   - IO_L6N_HDGC_88
#set_property PACKAGE_PIN C3       [get_ports "GPIO_PB_SW3"] ;# Bank  88 VCCO - VCC3V3   - IO_L6P_HDGC_88
#set_property IOSTANDARD  LVCMOS33 [get_ports "GPIO_PB_SW3"] ;# Bank  88 VCCO - VCC3V3   - IO_L6P_HDGC_88
#set_property PACKAGE_PIN C2       [get_ports "34N8749"] ;# Bank  88 VCCO - VCC3V3   - IO_L5N_HDGC_88
#set_property IOSTANDARD  LVCMOS33 [get_ports "HDMI_RX_LS_OE"] ;# Bank  88 VCCO - VCC3V3   - IO_L5N_HDGC_88
#set_property PACKAGE_PIN D2       [get_ports "HDMI_RX_SNK_SCL"] ;# Bank  88 VCCO - VCC3V3   - IO_L5P_HDGC_88
#set_property IOSTANDARD  LVCMOS33 [get_ports "HDMI_RX_SNK_SCL"] ;# Bank  88 VCCO - VCC3V3   - IO_L5P_HDGC_88
#set_property PACKAGE_PIN E2       [get_ports "HDMI_RX_SNK_SDA"] ;# Bank  88 VCCO - VCC3V3   - IO_L4N_AD12N_88
#set_property IOSTANDARD  LVCMOS33 [get_ports "HDMI_RX_SNK_SDA"] ;# Bank  88 VCCO - VCC3V3   - IO_L4N_AD12N_88
#set_property PACKAGE_PIN E3       [get_ports "HDMI_TX_HPD"] ;# Bank  88 VCCO - VCC3V3   - IO_L4P_AD12P_88
#set_property IOSTANDARD  LVCMOS33 [get_ports "HDMI_TX_HPD"] ;# Bank  88 VCCO - VCC3V3   - IO_L4P_AD12P_88
#set_property PACKAGE_PIN A2       [get_ports "HDMI_TX_EN"] ;# Bank  88 VCCO - VCC3V3   - IO_L3N_AD13N_88
#set_property IOSTANDARD  LVCMOS33 [get_ports "HDMI_TX_EN"] ;# Bank  88 VCCO - VCC3V3   - IO_L3N_AD13N_88
#set_property PACKAGE_PIN A3       [get_ports "HDMI_TX_CEC"] ;# Bank  88 VCCO - VCC3V3   - IO_L3P_AD13P_88
#set_property IOSTANDARD  LVCMOS33 [get_ports "HDMI_TX_CEC"] ;# Bank  88 VCCO - VCC3V3   - IO_L3P_AD13P_88
#set_property PACKAGE_PIN B1       [get_ports "HDMI_TX_SRC_SCL"] ;# Bank  88 VCCO - VCC3V3   - IO_L2N_AD14N_88
#set_property IOSTANDARD  LVCMOS33 [get_ports "HDMI_TX_SRC_SCL"] ;# Bank  88 VCCO - VCC3V3   - IO_L2N_AD14N_88
#set_property PACKAGE_PIN C1       [get_ports "HDMI_TX_SRC_SDA"] ;# Bank  88 VCCO - VCC3V3   - IO_L2P_AD14P_88
#set_property IOSTANDARD  LVCMOS33 [get_ports "HDMI_TX_SRC_SDA"] ;# Bank  88 VCCO - VCC3V3   - IO_L2P_AD14P_88
#set_property PACKAGE_PIN D1       [get_ports "HDMI_CTL_SCL"] ;# Bank  88 VCCO - VCC3V3   - IO_L1N_AD15N_88
#set_property IOSTANDARD  LVCMOS33 [get_ports "HDMI_CTL_SCL"] ;# Bank  88 VCCO - VCC3V3   - IO_L1N_AD15N_88
#set_property PACKAGE_PIN E1       [get_ports "HDMI_CTL_SDA"] ;# Bank  88 VCCO - VCC3V3   - IO_L1P_AD15P_88
#set_property IOSTANDARD  LVCMOS33 [get_ports "HDMI_CTL_SDA"] ;# Bank  88 VCCO - VCC3V3   - IO_L1P_AD15P_88
#set_property PACKAGE_PIN G8       [get_ports "PMOD0_0"] ;# Bank  87 VCCO - VCC3V3   - IO_L12N_AD0N_87
#set_property IOSTANDARD  LVCMOS33 [get_ports "PMOD0_0"] ;# Bank  87 VCCO - VCC3V3   - IO_L12N_AD0N_87
#set_property PACKAGE_PIN H8       [get_ports "PMOD0_1"] ;# Bank  87 VCCO - VCC3V3   - IO_L12P_AD0P_87
#set_property IOSTANDARD  LVCMOS33 [get_ports "PMOD0_1"] ;# Bank  87 VCCO - VCC3V3   - IO_L12P_AD0P_87
#set_property PACKAGE_PIN G7       [get_ports "PMOD0_2"] ;# Bank  87 VCCO - VCC3V3   - IO_L11N_AD1N_87
#set_property IOSTANDARD  LVCMOS33 [get_ports "PMOD0_2"] ;# Bank  87 VCCO - VCC3V3   - IO_L11N_AD1N_87
#set_property PACKAGE_PIN H7       [get_ports "PMOD0_3"] ;# Bank  87 VCCO - VCC3V3   - IO_L11P_AD1P_87
#set_property IOSTANDARD  LVCMOS33 [get_ports "PMOD0_3"] ;# Bank  87 VCCO - VCC3V3   - IO_L11P_AD1P_87
#set_property PACKAGE_PIN G6       [get_ports "PMOD0_4"] ;# Bank  87 VCCO - VCC3V3   - IO_L10N_AD2N_87
#set_property IOSTANDARD  LVCMOS33 [get_ports "PMOD0_4"] ;# Bank  87 VCCO - VCC3V3   - IO_L10N_AD2N_87
#set_property PACKAGE_PIN H6       [get_ports "PMOD0_5"] ;# Bank  87 VCCO - VCC3V3   - IO_L10P_AD2P_87
#set_property IOSTANDARD  LVCMOS33 [get_ports "PMOD0_5"] ;# Bank  87 VCCO - VCC3V3   - IO_L10P_AD2P_87
#set_property PACKAGE_PIN J6       [get_ports "PMOD0_6"] ;# Bank  87 VCCO - VCC3V3   - IO_L9N_AD3N_87
#set_property IOSTANDARD  LVCMOS33 [get_ports "PMOD0_6"] ;# Bank  87 VCCO - VCC3V3   - IO_L9N_AD3N_87
#set_property PACKAGE_PIN J7       [get_ports "PMOD0_7"] ;# Bank  87 VCCO - VCC3V3   - IO_L9P_AD3P_87
#set_property IOSTANDARD  LVCMOS33 [get_ports "PMOD0_7"] ;# Bank  87 VCCO - VCC3V3   - IO_L9P_AD3P_87
#set_property PACKAGE_PIN J9       [get_ports "PMOD1_0"] ;# Bank  87 VCCO - VCC3V3   - IO_L8N_HDGC_AD4N_87
#set_property IOSTANDARD  LVCMOS33 [get_ports "PMOD1_0"] ;# Bank  87 VCCO - VCC3V3   - IO_L8N_HDGC_AD4N_87
#set_property PACKAGE_PIN K9       [get_ports "PMOD1_1"] ;# Bank  87 VCCO - VCC3V3   - IO_L8P_HDGC_AD4P_87
#set_property IOSTANDARD  LVCMOS33 [get_ports "PMOD1_1"] ;# Bank  87 VCCO - VCC3V3   - IO_L8P_HDGC_AD4P_87
#set_property PACKAGE_PIN K8       [get_ports "PMOD1_2"] ;# Bank  87 VCCO - VCC3V3   - IO_L7N_HDGC_AD5N_87
#set_property IOSTANDARD  LVCMOS33 [get_ports "PMOD1_2"] ;# Bank  87 VCCO - VCC3V3   - IO_L7N_HDGC_AD5N_87
#set_property PACKAGE_PIN L8       [get_ports "PMOD1_3"] ;# Bank  87 VCCO - VCC3V3   - IO_L7P_HDGC_AD5P_87
#set_property IOSTANDARD  LVCMOS33 [get_ports "PMOD1_3"] ;# Bank  87 VCCO - VCC3V3   - IO_L7P_HDGC_AD5P_87
#set_property PACKAGE_PIN L10      [get_ports "PMOD1_4"] ;# Bank  87 VCCO - VCC3V3   - IO_L6N_HDGC_AD6N_87
#set_property IOSTANDARD  LVCMOS33 [get_ports "PMOD1_4"] ;# Bank  87 VCCO - VCC3V3   - IO_L6N_HDGC_AD6N_87
#set_property PACKAGE_PIN M10      [get_ports "PMOD1_5"] ;# Bank  87 VCCO - VCC3V3   - IO_L6P_HDGC_AD6P_87
#set_property IOSTANDARD  LVCMOS33 [get_ports "PMOD1_5"] ;# Bank  87 VCCO - VCC3V3   - IO_L6P_HDGC_AD6P_87
#set_property PACKAGE_PIN M8       [get_ports "PMOD1_6"] ;# Bank  87 VCCO - VCC3V3   - IO_L5N_HDGC_AD7N_87
#set_property IOSTANDARD  LVCMOS33 [get_ports "PMOD1_6"] ;# Bank  87 VCCO - VCC3V3   - IO_L5N_HDGC_AD7N_87
#set_property PACKAGE_PIN M9       [get_ports "PMOD1_7"] ;# Bank  87 VCCO - VCC3V3   - IO_L5P_HDGC_AD7P_87
#set_property IOSTANDARD  LVCMOS33 [get_ports "PMOD1_7"] ;# Bank  87 VCCO - VCC3V3   - IO_L5P_HDGC_AD7P_87
#set_property PACKAGE_PIN M11      [get_ports "CPU_RESET"] ;# Bank  87 VCCO - VCC3V3   - IO_L4N_AD8N_87
#set_property IOSTANDARD  LVCMOS33 [get_ports "CPU_RESET"] ;# Bank  87 VCCO - VCC3V3   - IO_L4N_AD8N_87
#set_property PACKAGE_PIN N11      [get_ports "HDMI_8T49N241_LOL"] ;# Bank  87 VCCO - VCC3V3   - IO_L4P_AD8P_87
#set_property IOSTANDARD  LVCMOS33 [get_ports "HDMI_8T49N241_LOL"] ;# Bank  87 VCCO - VCC3V3   - IO_L4P_AD8P_87
#set_property PACKAGE_PIN M12      [get_ports "HDMI_8T49N241_RST"] ;# Bank  87 VCCO - VCC3V3   - IO_L3N_AD9N_87
#set_property IOSTANDARD  LVCMOS33 [get_ports "HDMI_8T49N241_RST"] ;# Bank  87 VCCO - VCC3V3   - IO_L3N_AD9N_87
#set_property PACKAGE_PIN N13      [get_ports "HDMI_TX_LS_OE"] ;# Bank  87 VCCO - VCC3V3   - IO_L3P_AD9P_87
#set_property IOSTANDARD  LVCMOS33 [get_ports "HDMI_TX_LS_OE"] ;# Bank  87 VCCO - VCC3V3   - IO_L3P_AD9P_87
#set_property PACKAGE_PIN N8       [get_ports "HDMI_TX_CT_HPD"] ;# Bank  87 VCCO - VCC3V3   - IO_L2N_AD10N_87
#set_property IOSTANDARD  LVCMOS33 [get_ports "HDMI_TX_CT_HPD"] ;# Bank  87 VCCO - VCC3V3   - IO_L2N_AD10N_87
#set_property PACKAGE_PIN N9       [get_ports "34N8735"] ;# Bank  87 VCCO - VCC3V3   - IO_L2P_AD10P_87
#set_property IOSTANDARD  LVCMOS33 [get_ports "34N8735"] ;# Bank  87 VCCO - VCC3V3   - IO_L2P_AD10P_87
#set_property PACKAGE_PIN N12      [get_ports "PL_I2C1_SCL_LS"] ;# Bank  87 VCCO - VCC3V3   - IO_L1N_AD11N_87
#set_property IOSTANDARD  LVCMOS33 [get_ports "PL_I2C1_SCL_LS"] ;# Bank  87 VCCO - VCC3V3   - IO_L1N_AD11N_87
#set_property PACKAGE_PIN P12      [get_ports "PL_I2C1_SDA_LS"] ;# Bank  87 VCCO - VCC3V3   - IO_L1P_AD11P_87
#set_property IOSTANDARD  LVCMOS33 [get_ports "PL_I2C1_SDA_LS"] ;# Bank  87 VCCO - VCC3V3   - IO_L1P_AD11P_87
#set_property PACKAGE_PIN AP3      [get_ports "GND"] ;# Bank 223 - MGTHRXN0_223
#set_property PACKAGE_PIN AN1      [get_ports "GND"] ;# Bank 223 - MGTHRXN1_223
#set_property PACKAGE_PIN AL1      [get_ports "GND"] ;# Bank 223 - MGTHRXN2_223
#set_property PACKAGE_PIN AK3      [get_ports "GND"] ;# Bank 223 - MGTHRXN3_223
#set_property PACKAGE_PIN AP4      [get_ports "GND"] ;# Bank 223 - MGTHRXP0_223
#set_property PACKAGE_PIN AN2      [get_ports "GND"] ;# Bank 223 - MGTHRXP1_223
#set_property PACKAGE_PIN AL2      [get_ports "GND"] ;# Bank 223 - MGTHRXP2_223
#set_property PACKAGE_PIN AK4      [get_ports "GND"] ;# Bank 223 - MGTHRXP3_223
#set_property PACKAGE_PIN AN5      [get_ports "9N7450"] ;# Bank 223 - MGTHTXN0_223
#set_property PACKAGE_PIN AM3      [get_ports "9N7448"] ;# Bank 223 - MGTHTXN1_223
#set_property PACKAGE_PIN AL5      [get_ports "9N7446"] ;# Bank 223 - MGTHTXN2_223
#set_property PACKAGE_PIN AJ5      [get_ports "9N7444"] ;# Bank 223 - MGTHTXN3_223
#set_property PACKAGE_PIN AN6      [get_ports "9N7449"] ;# Bank 223 - MGTHTXP0_223
#set_property PACKAGE_PIN AM4      [get_ports "9N7447"] ;# Bank 223 - MGTHTXP1_223
#set_property PACKAGE_PIN AL6      [get_ports "9N7445"] ;# Bank 223 - MGTHTXP2_223
#set_property PACKAGE_PIN AJ6      [get_ports "9N7443"] ;# Bank 223 - MGTHTXP3_223
#set_property PACKAGE_PIN AD7      [get_ports "9N7442"] ;# Bank 223 - MGTREFCLK0N_223
#set_property PACKAGE_PIN AD8      [get_ports "9N7441"] ;# Bank 223 - MGTREFCLK0P_223
#set_property PACKAGE_PIN AC9      [get_ports "9N7455"] ;# Bank 223 - MGTREFCLK1N_223
#set_property PACKAGE_PIN AC10     [get_ports "9N7454"] ;# Bank 223 - MGTREFCLK1P_223
#set_property PACKAGE_PIN AJ1      [get_ports "GND"] ;# Bank 224 - MGTHRXN0_224
#set_property PACKAGE_PIN AG1      [get_ports "GND"] ;# Bank 224 - MGTHRXN1_224
#set_property PACKAGE_PIN AF3      [get_ports "GND"] ;# Bank 224 - MGTHRXN2_224
#set_property PACKAGE_PIN AE1      [get_ports "GND"] ;# Bank 224 - MGTHRXN3_224
#set_property PACKAGE_PIN AJ2      [get_ports "GND"] ;# Bank 224 - MGTHRXP0_224
#set_property PACKAGE_PIN AG2      [get_ports "GND"] ;# Bank 224 - MGTHRXP1_224
#set_property PACKAGE_PIN AF4      [get_ports "GND"] ;# Bank 224 - MGTHRXP2_224
#set_property PACKAGE_PIN AE2      [get_ports "GND"] ;# Bank 224 - MGTHRXP3_224
#set_property PACKAGE_PIN AH3      [get_ports "9N7412"] ;# Bank 224 - MGTHTXN0_224
#set_property PACKAGE_PIN AG5      [get_ports "9N7408"] ;# Bank 224 - MGTHTXN1_224
#set_property PACKAGE_PIN AE5      [get_ports "9N7404"] ;# Bank 224 - MGTHTXN2_224
#set_property PACKAGE_PIN AD3      [get_ports "9N7400"] ;# Bank 224 - MGTHTXN3_224
#set_property PACKAGE_PIN AH4      [get_ports "9N7411"] ;# Bank 224 - MGTHTXP0_224
#set_property PACKAGE_PIN AG6      [get_ports "9N7407"] ;# Bank 224 - MGTHTXP1_224
#set_property PACKAGE_PIN AE6      [get_ports "9N7403"] ;# Bank 224 - MGTHTXP2_224
#set_property PACKAGE_PIN AD4      [get_ports "9N7399"] ;# Bank 224 - MGTHTXP3_224
#set_property PACKAGE_PIN AB7      [get_ports "9N7396"] ;# Bank 224 - MGTREFCLK0N_224
#set_property PACKAGE_PIN AB8      [get_ports "9N7395"] ;# Bank 224 - MGTREFCLK0P_224
#set_property PACKAGE_PIN AA9      [get_ports "9N7386"] ;# Bank 224 - MGTREFCLK1N_224
#set_property PACKAGE_PIN AA10     [get_ports "9N7384"] ;# Bank 224 - MGTREFCLK1P_224
#Other net   PACKAGE_PIN AD9      - MGT1V2                    Bank 224 - MGTAVTTRCAL_R
#set_property PACKAGE_PIN AD10     [get_ports "MGTRREF_224"] ;# Bank 224 - MGTRREF_R
#set_property PACKAGE_PIN AC1      [get_ports "GND"] ;# Bank 225 - MGTHRXN0_225
#set_property PACKAGE_PIN AB3      [get_ports "GND"] ;# Bank 225 - MGTHRXN1_225
#set_property PACKAGE_PIN AA1      [get_ports "GND"] ;# Bank 225 - MGTHRXN2_225
#set_property PACKAGE_PIN W1       [get_ports "GND"] ;# Bank 225 - MGTHRXN3_225
#set_property PACKAGE_PIN AC2      [get_ports "GND"] ;# Bank 225 - MGTHRXP0_225
#set_property PACKAGE_PIN AB4      [get_ports "GND"] ;# Bank 225 - MGTHRXP1_225
#set_property PACKAGE_PIN AA2      [get_ports "GND"] ;# Bank 225 - MGTHRXP2_225
#set_property PACKAGE_PIN W2       [get_ports "GND"] ;# Bank 225 - MGTHRXP3_225
#set_property PACKAGE_PIN AC5      [get_ports "38N7665"] ;# Bank 225 - MGTHTXN0_225
#set_property PACKAGE_PIN AA5      [get_ports "38N7659"] ;# Bank 225 - MGTHTXN1_225
#set_property PACKAGE_PIN Y3       [get_ports "38N7653"] ;# Bank 225 - MGTHTXN2_225
#set_property PACKAGE_PIN W5       [get_ports "38N7647"] ;# Bank 225 - MGTHTXN3_225
#set_property PACKAGE_PIN AC6      [get_ports "38N7663"] ;# Bank 225 - MGTHTXP0_225
#set_property PACKAGE_PIN AA6      [get_ports "38N7657"] ;# Bank 225 - MGTHTXP1_225
#set_property PACKAGE_PIN Y4       [get_ports "38N7651"] ;# Bank 225 - MGTHTXP2_225
#set_property PACKAGE_PIN W6       [get_ports "38N7645"] ;# Bank 225 - MGTHTXP3_225
#set_property PACKAGE_PIN Y7       [get_ports "38N7641"] ;# Bank 225 - MGTREFCLK0N_225
#set_property PACKAGE_PIN Y8       [get_ports "38N7639"] ;# Bank 225 - MGTREFCLK0P_225
#set_property PACKAGE_PIN W9       [get_ports "38N7635"] ;# Bank 225 - MGTREFCLK1N_225
#set_property PACKAGE_PIN W10      [get_ports "38N7633"] ;# Bank 225 - MGTREFCLK1P_225
#set_property PACKAGE_PIN V3       [get_ports "GND"] ;# Bank 226 - MGTHRXN0_226
#set_property PACKAGE_PIN U1       [get_ports "GND"] ;# Bank 226 - MGTHRXN1_226
#set_property PACKAGE_PIN R1       [get_ports "GND"] ;# Bank 226 - MGTHRXN2_226
#set_property PACKAGE_PIN P3       [get_ports "FMC_LPC_DP0_M2C_N"] ;# Bank 226 - MGTHRXN3_226
#set_property PACKAGE_PIN V4       [get_ports "GND"] ;# Bank 226 - MGTHRXP0_226
#set_property PACKAGE_PIN U2       [get_ports "GND"] ;# Bank 226 - MGTHRXP1_226
#set_property PACKAGE_PIN R2       [get_ports "GND"] ;# Bank 226 - MGTHRXP2_226
#set_property PACKAGE_PIN P4       [get_ports "FMC_LPC_DP0_M2C_P"] ;# Bank 226 - MGTHRXP3_226
#set_property PACKAGE_PIN U5       [get_ports "38N7744"] ;# Bank 226 - MGTHTXN0_226
#set_property PACKAGE_PIN T3       [get_ports "38N7740"] ;# Bank 226 - MGTHTXN1_226
#set_property PACKAGE_PIN R5       [get_ports "38N8078"] ;# Bank 226 - MGTHTXN2_226
#set_property PACKAGE_PIN N5       [get_ports "FMC_LPC_DP0_C2M_N"] ;# Bank 226 - MGTHTXN3_226
#set_property PACKAGE_PIN U6       [get_ports "38N7743"] ;# Bank 226 - MGTHTXP0_226
#set_property PACKAGE_PIN T4       [get_ports "38N7739"] ;# Bank 226 - MGTHTXP1_226
#set_property PACKAGE_PIN R6       [get_ports "38N8077"] ;# Bank 226 - MGTHTXP2_226
#set_property PACKAGE_PIN N6       [get_ports "FMC_LPC_DP0_C2M_P"] ;# Bank 226 - MGTHTXP3_226
#set_property PACKAGE_PIN V7       [get_ports "FMC_LPC_GBTCLK0_M2C_C_N"] ;# Bank 226 - MGTREFCLK0N_226
#set_property PACKAGE_PIN V8       [get_ports "FMC_LPC_GBTCLK0_M2C_C_P"] ;# Bank 226 - MGTREFCLK0P_226
#set_property PACKAGE_PIN U9       [get_ports "HDMI_DRU_CLOCK_C_N"] ;# Bank 226 - MGTREFCLK1N_226
#set_property PACKAGE_PIN U10      [get_ports "HDMI_DRU_CLOCK_C_P"] ;# Bank 226 - MGTREFCLK1P_226
#set_property PACKAGE_PIN N1       [get_ports "HDMI_RX0_C_N"] ;# Bank 227 - MGTHRXN0_227
#set_property PACKAGE_PIN L1       [get_ports "HDMI_RX1_C_N"] ;# Bank 227 - MGTHRXN1_227
#set_property PACKAGE_PIN J1       [get_ports "HDMI_RX2_C_N"] ;# Bank 227 - MGTHRXN2_227
#set_property PACKAGE_PIN G1       [get_ports "GND"] ;# Bank 227 - MGTHRXN3_227
#set_property PACKAGE_PIN N2       [get_ports "HDMI_RX0_C_P"] ;# Bank 227 - MGTHRXP0_227
#set_property PACKAGE_PIN L2       [get_ports "HDMI_RX1_C_P"] ;# Bank 227 - MGTHRXP1_227
#set_property PACKAGE_PIN J2       [get_ports "HDMI_RX2_C_P"] ;# Bank 227 - MGTHRXP2_227
#set_property PACKAGE_PIN G2       [get_ports "GND"] ;# Bank 227 - MGTHRXP3_227
#set_property PACKAGE_PIN M3       [get_ports "HDMI_TX0_N"] ;# Bank 227 - MGTHTXN0_227
#set_property PACKAGE_PIN L5       [get_ports "HDMI_TX1_N"] ;# Bank 227 - MGTHTXN1_227
#set_property PACKAGE_PIN K3       [get_ports "HDMI_TX2_N"] ;# Bank 227 - MGTHTXN2_227
#set_property PACKAGE_PIN H3       [get_ports "38N8088"] ;# Bank 227 - MGTHTXN3_227
#set_property PACKAGE_PIN M4       [get_ports "HDMI_TX0_P"] ;# Bank 227 - MGTHTXP0_227
#set_property PACKAGE_PIN L6       [get_ports "HDMI_TX1_P"] ;# Bank 227 - MGTHTXP1_227
#set_property PACKAGE_PIN K4       [get_ports "HDMI_TX2_P"] ;# Bank 227 - MGTHTXP2_227
#set_property PACKAGE_PIN H4       [get_ports "38N8087"] ;# Bank 227 - MGTHTXP3_227
#set_property PACKAGE_PIN T7       [get_ports "HDMI_8T49N241_OUT_C_N"] ;# Bank 227 - MGTREFCLK0N_227
#set_property PACKAGE_PIN T8       [get_ports "HDMI_8T49N241_OUT_C_P"] ;# Bank 227 - MGTREFCLK0P_227
#set_property PACKAGE_PIN R9       [get_ports "HDMI_RX_CLK_C_N"] ;# Bank 227 - MGTREFCLK1N_227
#set_property PACKAGE_PIN R10      [get_ports "HDMI_RX_CLK_C_P"] ;# Bank 227 - MGTREFCLK1P_227
#Other net   PACKAGE_PIN A24      - MIO0_QSPI_LWR_CLK         Bank 500 - PS_MIO0
#Other net   PACKAGE_PIN C24      - MIO1_QSPI_LWR_DQ1         Bank 500 - PS_MIO1
#Other net   PACKAGE_PIN F26      - 53N7803                   Bank 500 - PS_MIO10
#Other net   PACKAGE_PIN B26      - 53N7806                   Bank 500 - PS_MIO11
#Other net   PACKAGE_PIN C27      - 53N7809                   Bank 500 - PS_MIO12
#Other net   PACKAGE_PIN D27      - 53N7788                   Bank 500 - PS_MIO13
#Other net   PACKAGE_PIN A27      - 53N7844                   Bank 500 - PS_MIO14
#Other net   PACKAGE_PIN E27      - 53N7842                   Bank 500 - PS_MIO15
#Other net   PACKAGE_PIN A28      - MIO16_I2C1_SCL            Bank 500 - PS_MIO16
#Other net   PACKAGE_PIN C29      - MIO17_I2C1_SDA            Bank 500 - PS_MIO17
#Other net   PACKAGE_PIN F27      - UART0_TXD_MIO18_RXD       Bank 500 - PS_MIO18
#Other net   PACKAGE_PIN B28      - UART0_RXD_MIO19_TXD       Bank 500 - PS_MIO19
#Other net   PACKAGE_PIN B24      - MIO2_QSPI_LWR_DQ2         Bank 500 - PS_MIO2
#Other net   PACKAGE_PIN E29      - UART1_RXD_MIO20_TXD       Bank 500 - PS_MIO20
#Other net   PACKAGE_PIN C28      - UART1_TXD_MIO21_RXD       Bank 500 - PS_MIO21
#Other net   PACKAGE_PIN F28      - 53N7824                   Bank 500 - PS_MIO22
#Other net   PACKAGE_PIN B29      - 53N7822                   Bank 500 - PS_MIO23
#Other net   PACKAGE_PIN E28      - MIO24_CAN_TX              Bank 500 - PS_MIO24
#Other net   PACKAGE_PIN D29      - MIO25_CAN_RX              Bank 500 - PS_MIO25
#Other net   PACKAGE_PIN E25      - MIO3_QSPI_LWR_DQ3         Bank 500 - PS_MIO3
#Other net   PACKAGE_PIN A25      - MIO4_QSPI_LWR_DQ0         Bank 500 - PS_MIO4
#Other net   PACKAGE_PIN D25      - MIO5_QSPI_LWR_CS_B        Bank 500 - PS_MIO5
#Other net   PACKAGE_PIN A26      - 53N6816                   Bank 500 - PS_MIO6
#Other net   PACKAGE_PIN B25      - 53N7794                   Bank 500 - PS_MIO7
#Other net   PACKAGE_PIN D26      - 53N7797                   Bank 500 - PS_MIO8
#Other net   PACKAGE_PIN C26      - 53N7800                   Bank 500 - PS_MIO9
#Other net   PACKAGE_PIN AA25     - PS_SYSMON_AVCC            Bank 500 - VCC_PSADC
#Other net   PACKAGE_PIN AA24     - PS_SYSMON_AGND            Bank 500 - GND_PSADC
#Other net   PACKAGE_PIN A29      - 53N7791                   Bank 501 - PS_MIO26
#Other net   PACKAGE_PIN A30      - MIO27_DP_AUX_OUT          Bank 501 - PS_MIO27
#Other net   PACKAGE_PIN A31      - MIO28_DP_HPD              Bank 501 - PS_MIO28
#Other net   PACKAGE_PIN A32      - MIO29_DP_OE               Bank 501 - PS_MIO29
#Other net   PACKAGE_PIN A33      - MIO30_DP_AUX_IN           Bank 501 - PS_MIO30
#Other net   PACKAGE_PIN B30      - 53N7736                   Bank 501 - PS_MIO31
#Other net   PACKAGE_PIN B31      - 53N7739                   Bank 501 - PS_MIO32
#Other net   PACKAGE_PIN B33      - 53N7742                   Bank 501 - PS_MIO33
#Other net   PACKAGE_PIN B34      - 53N7745                   Bank 501 - PS_MIO34
#Other net   PACKAGE_PIN C31      - 53N7748                   Bank 501 - PS_MIO35
#Other net   PACKAGE_PIN C32      - 53N7751                   Bank 501 - PS_MIO36
#Other net   PACKAGE_PIN C33      - 53N7754                   Bank 501 - PS_MIO37
#Other net   PACKAGE_PIN C34      - 53N7768                   Bank 501 - PS_MIO38
#Other net   PACKAGE_PIN D30      - 53N7771                   Bank 501 - PS_MIO39
#Other net   PACKAGE_PIN D31      - 53N7773                   Bank 501 - PS_MIO40
#Other net   PACKAGE_PIN D32      - 53N7775                   Bank 501 - PS_MIO41
#Other net   PACKAGE_PIN D34      - 53N7777                   Bank 501 - PS_MIO42
#Other net   PACKAGE_PIN E30      - 53N6798                   Bank 501 - PS_MIO43
#Other net   PACKAGE_PIN E32      - 53N7783                   Bank 501 - PS_MIO44
#Other net   PACKAGE_PIN E33      - MIO45_SDIO_DETECT         Bank 501 - PS_MIO45
#Other net   PACKAGE_PIN E34      - MIO46_SDIO_DAT0_R         Bank 501 - PS_MIO46
#Other net   PACKAGE_PIN F30      - MIO47_SDIO_DAT1_R         Bank 501 - PS_MIO47
#Other net   PACKAGE_PIN F31      - MIO48_SDIO_DAT2_R         Bank 501 - PS_MIO48
#Other net   PACKAGE_PIN F32      - MIO49_SDIO_DAT3_R         Bank 501 - PS_MIO49
#Other net   PACKAGE_PIN F33      - MIO50_SDIO_CMD_R          Bank 501 - PS_MIO50
#Other net   PACKAGE_PIN F34      - MIO51_SDIO_CLK_R          Bank 501 - PS_MIO51
#Other net   PACKAGE_PIN G29      - MIO52_USB_CLK             Bank 502 - PS_MIO52
#Other net   PACKAGE_PIN G30      - MIO53_USB_DIR             Bank 502 - PS_MIO53
#Other net   PACKAGE_PIN G31      - MIO54_USB_DATA2_R         Bank 502 - PS_MIO54
#Other net   PACKAGE_PIN G33      - MIO55_USB_NXT             Bank 502 - PS_MIO55
#Other net   PACKAGE_PIN G34      - MIO56_USB_DATA0_R         Bank 502 - PS_MIO56
#Other net   PACKAGE_PIN H29      - MIO57_USB_DATA1_R         Bank 502 - PS_MIO57
#Other net   PACKAGE_PIN H31      - MIO58_USB_STP_R           Bank 502 - PS_MIO58
#Other net   PACKAGE_PIN H32      - MIO59_USB_DATA3_R         Bank 502 - PS_MIO59
#Other net   PACKAGE_PIN H33      - MIO60_USB_DATA4_R         Bank 502 - PS_MIO60
#Other net   PACKAGE_PIN H34      - MIO61_USB_DATA5_R         Bank 502 - PS_MIO61
#Other net   PACKAGE_PIN J29      - MIO62_USB_DATA6_R         Bank 502 - PS_MIO62
#Other net   PACKAGE_PIN J30      - MIO63_USB_DATA7_R         Bank 502 - PS_MIO63
#Other net   PACKAGE_PIN J31      - MIO64_ENET_TX_CLK         Bank 502 - PS_MIO64
#Other net   PACKAGE_PIN J32      - MIO65_ENET_TX_D0          Bank 502 - PS_MIO65
#Other net   PACKAGE_PIN J34      - MIO66_ENET_TX_D1          Bank 502 - PS_MIO66
#Other net   PACKAGE_PIN K28      - MIO67_ENET_TX_D2          Bank 502 - PS_MIO67
#Other net   PACKAGE_PIN K29      - MIO68_ENET_TX_D3          Bank 502 - PS_MIO68
#Other net   PACKAGE_PIN K30      - MIO69_ENET_TX_CTRL        Bank 502 - PS_MIO69
#Other net   PACKAGE_PIN K31      - MIO70_ENET_RX_CLK         Bank 502 - PS_MIO70
#Other net   PACKAGE_PIN K32      - MIO71_ENET_RX_D0          Bank 502 - PS_MIO71
#Other net   PACKAGE_PIN K33      - MIO72_ENET_RX_D1          Bank 502 - PS_MIO72
#Other net   PACKAGE_PIN K34      - MIO73_ENET_RX_D2          Bank 502 - PS_MIO73
#Other net   PACKAGE_PIN L29      - MIO74_ENET_RX_D3          Bank 502 - PS_MIO74
#Other net   PACKAGE_PIN L30      - MIO75_ENET_RX_CTRL        Bank 502 - PS_MIO75
#Other net   PACKAGE_PIN L33      - MIO76_ENET_MDC            Bank 502 - PS_MIO76
#Other net   PACKAGE_PIN L34      - MIO77_ENET_MDIO           Bank 502 - PS_MIO77
#Other net   PACKAGE_PIN N24      - PS_DONE                   Bank 503 - PS_DONE
#Other net   PACKAGE_PIN T25      - PS_ERR_OUT                Bank 503 - PS_ERROR_OUT
#Other net   PACKAGE_PIN R25      - PS_ERR_STATUS             Bank 503 - PS_ERROR_STATUS
#Other net   PACKAGE_PIN P24      - PS_INIT_B                 Bank 503 - PS_INIT_B
#Other net   PACKAGE_PIN K27      - FPGA_TCK                  Bank 503 - PS_JTAG_TCK
#Other net   PACKAGE_PIN J27      - FPGA_TDI                  Bank 503 - PS_JTAG_TDI
#Other net   PACKAGE_PIN G28      - FPGA_TDO_FMC_TDI          Bank 503 - PS_JTAG_TDO
#Other net   PACKAGE_PIN H28      - FPGA_TMS                  Bank 503 - PS_JTAG_TMS
#Other net   PACKAGE_PIN H27      - PS_MODE0                  Bank 503 - PS_MODE0
#Other net   PACKAGE_PIN J26      - PS_MODE1                  Bank 503 - PS_MODE1
#Other net   PACKAGE_PIN K26      - PS_MODE2                  Bank 503 - PS_MODE2
#Other net   PACKAGE_PIN K25      - PS_MODE3                  Bank 503 - PS_MODE3
#Other net   PACKAGE_PIN M25      - PS_PADI                   Bank 503 - PS_PADI
#Other net   PACKAGE_PIN L25      - PS_PADO                   Bank 503 - PS_PADO
#Other net   PACKAGE_PIN M24      - PS_POR_B                  Bank 503 - PS_POR_B
#Other net   PACKAGE_PIN T24      - PS_PROG_B                 Bank 503 - PS_PROG_B
#Other net   PACKAGE_PIN R24      - PS_REF_CLK                Bank 503 - PS_REF_CLK
#Other net   PACKAGE_PIN P25      - PS_SRST_B                 Bank 503 - PS_SRST_B
#Other net   PACKAGE_PIN AN34     - DDR4_A0                   Bank 504 - PS_DDR_A0
#Other net   PACKAGE_PIN AM34     - DDR4_A1                   Bank 504 - PS_DDR_A1
#Other net   PACKAGE_PIN AG31     - DDR4_A10                  Bank 504 - PS_DDR_A10
#Other net   PACKAGE_PIN AF31     - DDR4_A11                  Bank 504 - PS_DDR_A11
#Other net   PACKAGE_PIN AG30     - DDR4_A12                  Bank 504 - PS_DDR_A12
#Other net   PACKAGE_PIN AF30     - DDR4_A13                  Bank 504 - PS_DDR_A13
#Other net   PACKAGE_PIN AG29     - DDR4_A14_WE_B             Bank 504 - PS_DDR_A14
#Other net   PACKAGE_PIN AG28     - DDR4_A15_CAS_B            Bank 504 - PS_DDR_A15
#Other net   PACKAGE_PIN AF28     - DDR4_A16_RAS_B            Bank 504 - PS_DDR_A16
#Other net   PACKAGE_PIN AF26     - 68N6692                   Bank 504 - PS_DDR_A17
#Other net   PACKAGE_PIN AM33     - DDR4_A2                   Bank 504 - PS_DDR_A2
#Other net   PACKAGE_PIN AL34     - DDR4_A3                   Bank 504 - PS_DDR_A3
#Other net   PACKAGE_PIN AL33     - DDR4_A4                   Bank 504 - PS_DDR_A4
#Other net   PACKAGE_PIN AK33     - DDR4_A5                   Bank 504 - PS_DDR_A5
#Other net   PACKAGE_PIN AK30     - DDR4_A6                   Bank 504 - PS_DDR_A6
#Other net   PACKAGE_PIN AJ30     - DDR4_A7                   Bank 504 - PS_DDR_A7
#Other net   PACKAGE_PIN AJ31     - DDR4_A8                   Bank 504 - PS_DDR_A8
#Other net   PACKAGE_PIN AH31     - DDR4_A9                   Bank 504 - PS_DDR_A9
#Other net   PACKAGE_PIN AE25     - DDR4_ACT_B                Bank 504 - PS_DDR_ACT_N
#Other net   PACKAGE_PIN AB26     - DDR4_ALERT_B              Bank 504 - PS_DDR_ALERT_N
#Other net   PACKAGE_PIN AE27     - DDR4_BA0                  Bank 504 - PS_DDR_BA0
#Other net   PACKAGE_PIN AE28     - DDR4_BA1                  Bank 504 - PS_DDR_BA1
#Other net   PACKAGE_PIN AD27     - DDR4_BG0                  Bank 504 - PS_DDR_BG0
#Other net   PACKAGE_PIN AF27     - 68N7393                   Bank 504 - PS_DDR_BG1
#Other net   PACKAGE_PIN AL31     - DDR4_CK_T                 Bank 504 - PS_DDR_CK0
#Other net   PACKAGE_PIN AL30     - 68N7399                   Bank 504 - PS_DDR_CK1
#Other net   PACKAGE_PIN AN33     - DDR4_CKE                  Bank 504 - PS_DDR_CKE0
#Other net   PACKAGE_PIN AH32     - 68N7405                   Bank 504 - PS_DDR_CKE1
#Other net   PACKAGE_PIN AN32     - DDR4_CK_C                 Bank 504 - PS_DDR_CK_N0
#Other net   PACKAGE_PIN AL32     - 68N7402                   Bank 504 - PS_DDR_CK_N1
#Other net   PACKAGE_PIN AP33     - DDR4_CS_B                 Bank 504 - PS_DDR_CS_N0
#Other net   PACKAGE_PIN AK32     - 68N7396                   Bank 504 - PS_DDR_CS_N1
#Other net   PACKAGE_PIN AN24     - DDR4_DM0                  Bank 504 - PS_DDR_DM0
#Other net   PACKAGE_PIN AM29     - DDR4_DM1                  Bank 504 - PS_DDR_DM1
#Other net   PACKAGE_PIN AH24     - DDR4_DM2                  Bank 504 - PS_DDR_DM2
#Other net   PACKAGE_PIN AJ29     - DDR4_DM3                  Bank 504 - PS_DDR_DM3
#Other net   PACKAGE_PIN AD29     - DDR4_DM4                  Bank 504 - PS_DDR_DM4
#Other net   PACKAGE_PIN Y29      - DDR4_DM5                  Bank 504 - PS_DDR_DM5
#Other net   PACKAGE_PIN AC32     - DDR4_DM6                  Bank 504 - PS_DDR_DM6
#Other net   PACKAGE_PIN Y32      - DDR4_DM7                  Bank 504 - PS_DDR_DM7
#Other net   PACKAGE_PIN AF34     - 68N7353                   Bank 504 - PS_DDR_DM8
#Other net   PACKAGE_PIN AP27     - DDR4_DQ0                  Bank 504 - PS_DDR_DQ0
#Other net   PACKAGE_PIN AP25     - DDR4_DQ1                  Bank 504 - PS_DDR_DQ1
#Other net   PACKAGE_PIN AP29     - DDR4_DQ10                 Bank 504 - PS_DDR_DQ10
#Other net   PACKAGE_PIN AP28     - DDR4_DQ11                 Bank 504 - PS_DDR_DQ11
#Other net   PACKAGE_PIN AM31     - DDR4_DQ12                 Bank 504 - PS_DDR_DQ12
#Other net   PACKAGE_PIN AP31     - DDR4_DQ13                 Bank 504 - PS_DDR_DQ13
#Other net   PACKAGE_PIN AN31     - DDR4_DQ14                 Bank 504 - PS_DDR_DQ14
#Other net   PACKAGE_PIN AM30     - DDR4_DQ15                 Bank 504 - PS_DDR_DQ15
#Other net   PACKAGE_PIN AF25     - DDR4_DQ16                 Bank 504 - PS_DDR_DQ16
#Other net   PACKAGE_PIN AG25     - DDR4_DQ17                 Bank 504 - PS_DDR_DQ17
#Other net   PACKAGE_PIN AG26     - DDR4_DQ18                 Bank 504 - PS_DDR_DQ18
#Other net   PACKAGE_PIN AJ25     - DDR4_DQ19                 Bank 504 - PS_DDR_DQ19
#Other net   PACKAGE_PIN AP26     - DDR4_DQ2                  Bank 504 - PS_DDR_DQ2
#Other net   PACKAGE_PIN AG24     - DDR4_DQ20                 Bank 504 - PS_DDR_DQ20
#Other net   PACKAGE_PIN AK25     - DDR4_DQ21                 Bank 504 - PS_DDR_DQ21
#Other net   PACKAGE_PIN AJ24     - DDR4_DQ22                 Bank 504 - PS_DDR_DQ22
#Other net   PACKAGE_PIN AK24     - DDR4_DQ23                 Bank 504 - PS_DDR_DQ23
#Other net   PACKAGE_PIN AH28     - DDR4_DQ24                 Bank 504 - PS_DDR_DQ24
#Other net   PACKAGE_PIN AH27     - DDR4_DQ25                 Bank 504 - PS_DDR_DQ25
#Other net   PACKAGE_PIN AJ27     - DDR4_DQ26                 Bank 504 - PS_DDR_DQ26
#Other net   PACKAGE_PIN AK27     - DDR4_DQ27                 Bank 504 - PS_DDR_DQ27
#Other net   PACKAGE_PIN AL26     - DDR4_DQ28                 Bank 504 - PS_DDR_DQ28
#Other net   PACKAGE_PIN AL27     - DDR4_DQ29                 Bank 504 - PS_DDR_DQ29
#Other net   PACKAGE_PIN AM26     - DDR4_DQ3                  Bank 504 - PS_DDR_DQ3
#Other net   PACKAGE_PIN AH29     - DDR4_DQ30                 Bank 504 - PS_DDR_DQ30
#Other net   PACKAGE_PIN AL28     - DDR4_DQ31                 Bank 504 - PS_DDR_DQ31
#Other net   PACKAGE_PIN AB29     - DDR4_DQ32                 Bank 504 - PS_DDR_DQ32
#Other net   PACKAGE_PIN AB30     - DDR4_DQ33                 Bank 504 - PS_DDR_DQ33
#Other net   PACKAGE_PIN AC29     - DDR4_DQ34                 Bank 504 - PS_DDR_DQ34
#Other net   PACKAGE_PIN AD32     - DDR4_DQ35                 Bank 504 - PS_DDR_DQ35
#Other net   PACKAGE_PIN AC31     - DDR4_DQ36                 Bank 504 - PS_DDR_DQ36
#Other net   PACKAGE_PIN AE30     - DDR4_DQ37                 Bank 504 - PS_DDR_DQ37
#Other net   PACKAGE_PIN AC28     - DDR4_DQ38                 Bank 504 - PS_DDR_DQ38
#Other net   PACKAGE_PIN AE29     - DDR4_DQ39                 Bank 504 - PS_DDR_DQ39
#Other net   PACKAGE_PIN AP24     - DDR4_DQ4                  Bank 504 - PS_DDR_DQ4
#Other net   PACKAGE_PIN AC27     - DDR4_DQ40                 Bank 504 - PS_DDR_DQ40
#Other net   PACKAGE_PIN AA27     - DDR4_DQ41                 Bank 504 - PS_DDR_DQ41
#Other net   PACKAGE_PIN AA28     - DDR4_DQ42                 Bank 504 - PS_DDR_DQ42
#Other net   PACKAGE_PIN AB28     - DDR4_DQ43                 Bank 504 - PS_DDR_DQ43
#Other net   PACKAGE_PIN W27      - DDR4_DQ44                 Bank 504 - PS_DDR_DQ44
#Other net   PACKAGE_PIN W29      - DDR4_DQ45                 Bank 504 - PS_DDR_DQ45
#Other net   PACKAGE_PIN W28      - DDR4_DQ46                 Bank 504 - PS_DDR_DQ46
#Other net   PACKAGE_PIN V27      - DDR4_DQ47                 Bank 504 - PS_DDR_DQ47
#Other net   PACKAGE_PIN AA32     - DDR4_DQ48                 Bank 504 - PS_DDR_DQ48
#Other net   PACKAGE_PIN AA33     - DDR4_DQ49                 Bank 504 - PS_DDR_DQ49
#Other net   PACKAGE_PIN AL25     - DDR4_DQ5                  Bank 504 - PS_DDR_DQ5
#Other net   PACKAGE_PIN AA34     - DDR4_DQ50                 Bank 504 - PS_DDR_DQ50
#Other net   PACKAGE_PIN AE34     - DDR4_DQ51                 Bank 504 - PS_DDR_DQ51
#Other net   PACKAGE_PIN AD34     - DDR4_DQ52                 Bank 504 - PS_DDR_DQ52
#Other net   PACKAGE_PIN AB31     - DDR4_DQ53                 Bank 504 - PS_DDR_DQ53
#Other net   PACKAGE_PIN AC34     - DDR4_DQ54                 Bank 504 - PS_DDR_DQ54
#Other net   PACKAGE_PIN AC33     - DDR4_DQ55                 Bank 504 - PS_DDR_DQ55
#Other net   PACKAGE_PIN AA30     - DDR4_DQ56                 Bank 504 - PS_DDR_DQ56
#Other net   PACKAGE_PIN Y30      - DDR4_DQ57                 Bank 504 - PS_DDR_DQ57
#Other net   PACKAGE_PIN AA31     - DDR4_DQ58                 Bank 504 - PS_DDR_DQ58
#Other net   PACKAGE_PIN W30      - DDR4_DQ59                 Bank 504 - PS_DDR_DQ59
#Other net   PACKAGE_PIN AM25     - DDR4_DQ6                  Bank 504 - PS_DDR_DQ6
#Other net   PACKAGE_PIN Y33      - DDR4_DQ60                 Bank 504 - PS_DDR_DQ60
#Other net   PACKAGE_PIN W33      - DDR4_DQ61                 Bank 504 - PS_DDR_DQ61
#Other net   PACKAGE_PIN W34      - DDR4_DQ62                 Bank 504 - PS_DDR_DQ62
#Other net   PACKAGE_PIN Y34      - DDR4_DQ63                 Bank 504 - PS_DDR_DQ63
#Other net   PACKAGE_PIN AF32     - 68N7356                   Bank 504 - PS_DDR_DQ64
#Other net   PACKAGE_PIN AE32     - 68N7359                   Bank 504 - PS_DDR_DQ65
#Other net   PACKAGE_PIN AH33     - 68N7362                   Bank 504 - PS_DDR_DQ66
#Other net   PACKAGE_PIN AE33     - 68N7364                   Bank 504 - PS_DDR_DQ67
#Other net   PACKAGE_PIN AF33     - 68N7368                   Bank 504 - PS_DDR_DQ68
#Other net   PACKAGE_PIN AH34     - 68N7370                   Bank 504 - PS_DDR_DQ69
#Other net   PACKAGE_PIN AM24     - DDR4_DQ7                  Bank 504 - PS_DDR_DQ7
#Other net   PACKAGE_PIN AJ34     - 68N7374                   Bank 504 - PS_DDR_DQ70
#Other net   PACKAGE_PIN AK34     - 68N7376                   Bank 504 - PS_DDR_DQ71
#Other net   PACKAGE_PIN AM28     - DDR4_DQ8                  Bank 504 - PS_DDR_DQ8
#Other net   PACKAGE_PIN AN28     - DDR4_DQ9                  Bank 504 - PS_DDR_DQ9
#Other net   PACKAGE_PIN AN27     - DDR4_DQS0_C               Bank 504 - PS_DDR_DQS_N0
#Other net   PACKAGE_PIN AP30     - DDR4_DQS1_C               Bank 504 - PS_DDR_DQS_N1
#Other net   PACKAGE_PIN AJ26     - DDR4_DQS2_C               Bank 504 - PS_DDR_DQS_N2
#Other net   PACKAGE_PIN AK29     - DDR4_DQS3_C               Bank 504 - PS_DDR_DQS_N3
#Other net   PACKAGE_PIN AD31     - DDR4_DQS4_C               Bank 504 - PS_DDR_DQS_N4
#Other net   PACKAGE_PIN Y28      - DDR4_DQS5_C               Bank 504 - PS_DDR_DQS_N5
#Other net   PACKAGE_PIN AB34     - DDR4_DQS6_C               Bank 504 - PS_DDR_DQS_N6
#Other net   PACKAGE_PIN W32      - DDR4_DQS7_C               Bank 504 - PS_DDR_DQS_N7
#Other net   PACKAGE_PIN AG34     - 68N7350                   Bank 504 - PS_DDR_DQS_N8
#Other net   PACKAGE_PIN AN26     - DDR4_DQS0_T               Bank 504 - PS_DDR_DQS_P0
#Other net   PACKAGE_PIN AN29     - DDR4_DQS1_T               Bank 504 - PS_DDR_DQS_P1
#Other net   PACKAGE_PIN AH26     - DDR4_DQS2_T               Bank 504 - PS_DDR_DQS_P2
#Other net   PACKAGE_PIN AK28     - DDR4_DQS3_T               Bank 504 - PS_DDR_DQS_P3
#Other net   PACKAGE_PIN AD30     - DDR4_DQS4_T               Bank 504 - PS_DDR_DQS_P4
#Other net   PACKAGE_PIN Y27      - DDR4_DQS5_T               Bank 504 - PS_DDR_DQS_P5
#Other net   PACKAGE_PIN AB33     - DDR4_DQS6_T               Bank 504 - PS_DDR_DQS_P6
#Other net   PACKAGE_PIN W31      - DDR4_DQS7_T               Bank 504 - PS_DDR_DQS_P7
#Other net   PACKAGE_PIN AG33     - 68N7347                   Bank 504 - PS_DDR_DQS_P8
#Other net   PACKAGE_PIN AP32     - DDR4_ODT                  Bank 504 - PS_DDR_ODT0
#Other net   PACKAGE_PIN AJ32     - 68N7408                   Bank 504 - PS_DDR_ODT1
#Other net   PACKAGE_PIN AA26     - DDR4_PAR                  Bank 504 - PS_DDR_PARITY
#Other net   PACKAGE_PIN AD26     - DDR4_RESET_B              Bank 504 - PS_DDR_RAM_RST_N
#Other net   PACKAGE_PIN AC26     - SODIMM_ZQ                 Bank 504 - PS_DDR_ZQ
#Other net   PACKAGE_PIN U34      - 69N6524                   Bank 505 - PS_MGTRRXN0_505
#Other net   PACKAGE_PIN T32      - 69N6530                   Bank 505 - PS_MGTRRXN1_505
#Other net   PACKAGE_PIN R34      - GT2_USB0_RX_N             Bank 505 - PS_MGTRRXN2_505
#Other net   PACKAGE_PIN N34      - GT3_SATA1_RX_N            Bank 505 - PS_MGTRRXN3_505
#Other net   PACKAGE_PIN U33      - 69N6521                   Bank 505 - PS_MGTRRXP0_505
#Other net   PACKAGE_PIN T31      - 69N6527                   Bank 505 - PS_MGTRRXP1_505
#Other net   PACKAGE_PIN R33      - GT2_USB0_RX_P             Bank 505 - PS_MGTRRXP2_505
#Other net   PACKAGE_PIN N33      - GT3_SATA1_RX_P            Bank 505 - PS_MGTRRXP3_505
#Other net   PACKAGE_PIN U30      - GT0_DP_TX_N               Bank 505 - PS_MGTRTXN0_505
#Other net   PACKAGE_PIN R30      - GT1_DP_TX_N               Bank 505 - PS_MGTRTXN1_505
#Other net   PACKAGE_PIN P32      - GT2_USB0_TX_N             Bank 505 - PS_MGTRTXN2_505
#Other net   PACKAGE_PIN N30      - GT3_SATA1_TX_N            Bank 505 - PS_MGTRTXN3_505
#Other net   PACKAGE_PIN U29      - GT0_DP_TX_P               Bank 505 - PS_MGTRTXP0_505
#Other net   PACKAGE_PIN R29      - GT1_DP_TX_P               Bank 505 - PS_MGTRTXP1_505
#Other net   PACKAGE_PIN P31      - GT2_USB0_TX_P             Bank 505 - PS_MGTRTXP2_505
#Other net   PACKAGE_PIN N29      - GT3_SATA1_TX_P            Bank 505 - PS_MGTRTXP3_505
#Other net   PACKAGE_PIN T28      - 69N6536                   Bank 505 - PS_MGTREFCLK0N_505
#Other net   PACKAGE_PIN T27      - 69N6533                   Bank 505 - PS_MGTREFCLK0P_505
#Other net   PACKAGE_PIN P28      - GTR_REF_CLK_SATA_C_N      Bank 505 - PS_MGTREFCLK1N_505
#Other net   PACKAGE_PIN P27      - GTR_REF_CLK_SATA_C_P      Bank 505 - PS_MGTREFCLK1P_505
#Other net   PACKAGE_PIN M28      - GTR_REF_CLK_USB3_C_N      Bank 505 - PS_MGTREFCLK2N_505
#Other net   PACKAGE_PIN M27      - GTR_REF_CLK_USB3_C_P      Bank 505 - PS_MGTREFCLK2P_505
#Other net   PACKAGE_PIN M32      - GTR_REF_CLK_DP_C_N        Bank 505 - PS_MGTREFCLK3N_505
#Other net   PACKAGE_PIN M31      - GTR_REF_CLK_DP_C_P        Bank 505 - PS_MGTREFCLK3P_505
#Other net   PACKAGE_PIN U31      - 69N5804                   Bank 505 - PS_MGTRREF_505
#Other net   PACKAGE_PIN AE16     - VCC1V2                    Bank  64 - VCCO_64
#Other net   PACKAGE_PIN AH15     - VCC1V2                    Bank  64 - VCCO_64
#Other net   PACKAGE_PIN AJ18     - VCC1V2                    Bank  64 - VCCO_64
#Other net   PACKAGE_PIN AF19     - VCC1V2                    Bank  65 - VCCO_65
#Other net   PACKAGE_PIN AG22     - VCC1V2                    Bank  65 - VCCO_65
#Other net   PACKAGE_PIN AK21     - VCC1V2                    Bank  65 - VCCO_65
#Other net   PACKAGE_PIN AF9      - VCC1V2                    Bank  66 - VCCO_66
#Other net   PACKAGE_PIN AG12     - VCC1V2                    Bank  66 - VCCO_66
#Other net   PACKAGE_PIN AK11     - VCC1V2                    Bank  66 - VCCO_66
#Other net   PACKAGE_PIN E21      - VCC1V8                    Bank  28 - VCCO_28
#Other net   PACKAGE_PIN F24      - VCC1V8                    Bank  28 - VCCO_28
#Other net   PACKAGE_PIN H20      - VCC1V8                    Bank  28 - VCCO_28
#Other net   PACKAGE_PIN D13      - VADJ_FMC                  Bank  67 - VCCO_67
#Other net   PACKAGE_PIN E16      - VADJ_FMC                  Bank  67 - VCCO_67
#Other net   PACKAGE_PIN H15      - VADJ_FMC                  Bank  67 - VCCO_67
#Other net   PACKAGE_PIN F9       - VADJ_FMC                  Bank  68 - VCCO_68
#Other net   PACKAGE_PIN G12      - VADJ_FMC                  Bank  68 - VCCO_68
#Other net   PACKAGE_PIN K11      - VADJ_FMC                  Bank  68 - VCCO_68
#Other net   PACKAGE_PIN J8       - VCC3V3                    Bank  87 - VCCO_87
#Other net   PACKAGE_PIN N10      - VCC3V3                    Bank  87 - VCCO_87
#Other net   PACKAGE_PIN D3       - VCC3V3                    Bank  88 - VCCO_88
#Other net   PACKAGE_PIN E6       - VCC3V3                    Bank  88 - VCCO_88
#Other net   PACKAGE_PIN C25      - VCC1V8                    Bank 500 - VCCO_PSIO0_500
#Other net   PACKAGE_PIN D28      - VCC1V8                    Bank 500 - VCCO_PSIO0_500
#Other net   PACKAGE_PIN B32      - VCC1V8                    Bank 501 - VCCO_PSIO1_501
#Other net   PACKAGE_PIN E31      - VCC1V8                    Bank 501 - VCCO_PSIO1_501
#Other net   PACKAGE_PIN H30      - VCC1V8                    Bank 502 - VCCO_PSIO2_502
#Other net   PACKAGE_PIN J33      - VCC1V8                    Bank 502 - VCCO_PSIO2_502
#Other net   PACKAGE_PIN G27      - VCC1V8                    Bank 503 - VCCO_PSIO3_503
#Other net   PACKAGE_PIN N25      - VCC1V8                    Bank 503 - VCCO_PSIO3_503
#Other net   PACKAGE_PIN AE26     - VCC1V2                    Bank 504 - VCCO_PSDDR_504
#Other net   PACKAGE_PIN AE31     - VCC1V2                    Bank 504 - VCCO_PSDDR_504
#Other net   PACKAGE_PIN AG27     - VCC1V2                    Bank 504 - VCCO_PSDDR_504
#Other net   PACKAGE_PIN AG32     - VCC1V2                    Bank 504 - VCCO_PSDDR_504
#Other net   PACKAGE_PIN AJ28     - VCC1V2                    Bank 504 - VCCO_PSDDR_504
#Other net   PACKAGE_PIN AJ33     - VCC1V2                    Bank 504 - VCCO_PSDDR_504
#Other net   PACKAGE_PIN AL29     - VCC1V2                    Bank 504 - VCCO_PSDDR_504
#Other net   PACKAGE_PIN A1       - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN A34      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN A4       - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN AA11     - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN AA21     - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN AA29     - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN AA3      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN AA4      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN AA7      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN AB1      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN AB11     - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN AB17     - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN AB2      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN AB27     - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN AB32     - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN AB5      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN AB9      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN AC11     - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN AC15     - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN AC20     - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN AC23     - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN AC3      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN AC30     - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN AC4      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN AC7      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN AD1      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN AD11     - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN AD13     - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN AD18     - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN AD2      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN AD25     - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN AD28     - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN AD33     - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN AD5      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN AE10     - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN AE11     - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN AE21     - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN AE3      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN AE4      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN AE7      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN AE8      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN AE9      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN AF1      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN AF14     - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN AF2      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN AF24     - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN AF29     - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN AF5      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN AF7      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN AG17     - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN AG3      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN AG4      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN AG7      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN AH1      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN AH10     - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN AH2      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN AH20     - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN AH25     - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN AH30     - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN AH5      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN AH7      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN AJ13     - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN AJ23     - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN AJ3      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN AJ4      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN AJ7      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN AJ8      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN AK1      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN AK16     - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN AK2      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN AK26     - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN AK31     - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN AK5      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN AK7      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN AL14     - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN AL19     - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN AL24     - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN AL3      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN AL4      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN AL7      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN AL9      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN AM1      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN AM12     - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN AM17     - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN AM2      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN AM22     - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN AM27     - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN AM32     - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN AM5      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN AM7      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN AN10     - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN AN15     - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN AN20     - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN AN25     - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN AN3      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN AN30     - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN AN4      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN AN7      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN AP1      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN AP2      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN AP34     - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN AP5      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN AP7      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN B12      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN B17      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN B2       - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN B22      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN B27      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN B7       - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN C10      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN C15      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN C20      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN C30      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN C5       - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN D18      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN D23      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN D33      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN D8       - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN E11      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN E26      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN F1       - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN F14      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN F19      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN F2       - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN F29      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN F3       - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN G17      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN G22      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN G3       - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN G32      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN G4       - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN G5       - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN H1       - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN H10      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN H2       - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN H25      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN H5       - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN J13      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN J18      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN J23      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN J28      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN J3       - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN J4       - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN J5       - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN K1       - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN K16      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN K2       - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN K21      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN K5       - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN K6       - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN K7       - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN L19      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN L24      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN L26      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN L27      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN L28      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN L3       - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN L31      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN L32      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN L4       - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN L7       - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN L9       - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN M1       - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN M14      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN M16      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN M18      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN M2       - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN M20      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN M22      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN M26      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN M29      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN M30      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN M33      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN M34      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN M5       - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN M7       - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN N15      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN N17      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN N19      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN N21      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN N23      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN N26      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN N28      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN N3       - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN N32      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN N4       - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN N7       - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN P1       - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN P10      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN P11      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN P14      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN P16      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN P18      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN P2       - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN P20      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN P22      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN P26      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN P30      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN P33      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN P34      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN P5       - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN P7       - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN P8       - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN P9       - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN R11      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN R13      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN R15      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN R19      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN R21      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN R26      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN R28      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN R3       - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN R31      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN R32      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN R4       - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN R7       - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN T1       - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN T11      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN T14      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN T16      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN T2       - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN T20      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN T23      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN T26      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN T30      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN T33      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN T34      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN T5       - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN T9       - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN U11      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN U12      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN U15      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN U19      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN U21      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN U24      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN U26      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN U27      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN U28      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN U3       - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN U32      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN U4       - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN U7       - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN V1       - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN V11      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN V14      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN V16      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN V2       - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN V20      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN V28      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN V29      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN V30      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN V31      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN V32      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN V33      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN V34      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN V5       - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN V9       - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN W11      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN W13      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN W15      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN W17      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN W19      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN W23      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN W3       - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN W4       - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN W7       - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN Y1       - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN Y11      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN Y12      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN Y14      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN Y16      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN Y18      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN Y2       - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN Y20      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN Y26      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN Y31      - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN Y5       - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN Y9       - GND                       Bank 999 - GND
#Other net   PACKAGE_PIN AA8      - MGTAVCC                   Bank 999 - MGTAVCC_R
#Other net   PACKAGE_PIN AB10     - MGTAVCC                   Bank 999 - MGTAVCC_R
#Other net   PACKAGE_PIN AC8      - MGTAVCC                   Bank 999 - MGTAVCC_R
#Other net   PACKAGE_PIN R8       - MGTAVCC                   Bank 999 - MGTAVCC_R
#Other net   PACKAGE_PIN T10      - MGTAVCC                   Bank 999 - MGTAVCC_R
#Other net   PACKAGE_PIN U8       - MGTAVCC                   Bank 999 - MGTAVCC_R
#Other net   PACKAGE_PIN W8       - MGTAVCC                   Bank 999 - MGTAVCC_R
#Other net   PACKAGE_PIN AB6      - MGT1V2                    Bank 999 - MGTAVTT_R
#Other net   PACKAGE_PIN AD6      - MGT1V2                    Bank 999 - MGTAVTT_R
#Other net   PACKAGE_PIN AF6      - MGT1V2                    Bank 999 - MGTAVTT_R
#Other net   PACKAGE_PIN AH6      - MGT1V2                    Bank 999 - MGTAVTT_R
#Other net   PACKAGE_PIN AK6      - MGT1V2                    Bank 999 - MGTAVTT_R
#Other net   PACKAGE_PIN AM6      - MGT1V2                    Bank 999 - MGTAVTT_R
#Other net   PACKAGE_PIN AP6      - MGT1V2                    Bank 999 - MGTAVTT_R
#Other net   PACKAGE_PIN M6       - MGT1V2                    Bank 999 - MGTAVTT_R
#Other net   PACKAGE_PIN P6       - MGT1V2                    Bank 999 - MGTAVTT_R
#Other net   PACKAGE_PIN T6       - MGT1V2                    Bank 999 - MGTAVTT_R
#Other net   PACKAGE_PIN V6       - MGT1V2                    Bank 999 - MGTAVTT_R
#Other net   PACKAGE_PIN Y6       - MGT1V2                    Bank 999 - MGTAVTT_R
#Other net   PACKAGE_PIN V10      - MGT1V8                    Bank 999 - MGTVCCAUX_R
#Other net   PACKAGE_PIN Y10      - MGT1V8                    Bank 999 - MGTVCCAUX_R
#Other net   PACKAGE_PIN N27      - MGTRAVCC                  Bank 999 - PS_MGTRAVCC
#Other net   PACKAGE_PIN R27      - MGTRAVCC                  Bank 999 - PS_MGTRAVCC
#Other net   PACKAGE_PIN N31      - MGT1V8                    Bank 999 - PS_MGTRAVTT
#Other net   PACKAGE_PIN P29      - MGT1V8                    Bank 999 - PS_MGTRAVTT
#Other net   PACKAGE_PIN T29      - MGT1V8                    Bank 999 - PS_MGTRAVTT
#Other net   PACKAGE_PIN P23      - VCC1V8                    Bank 999 - VCCAUX
#Other net   PACKAGE_PIN R23      - VCC1V8                    Bank 999 - VCCAUX
#Other net   PACKAGE_PIN U23      - VCC1V8                    Bank 999 - VCCAUX
#Other net   PACKAGE_PIN V23      - VCC1V8                    Bank 999 - VCCAUX
#Other net   PACKAGE_PIN N22      - VCC1V8                    Bank 999 - VCCAUX_IO
#Other net   PACKAGE_PIN R22      - VCC1V8                    Bank 999 - VCCAUX_IO
#Other net   PACKAGE_PIN T22      - VCC1V8                    Bank 999 - VCCAUX_IO
#Other net   PACKAGE_PIN U22      - VCC1V8                    Bank 999 - VCCAUX_IO
#Other net   PACKAGE_PIN R12      - VCCINT                    Bank 999 - VCCBRAM
#Other net   PACKAGE_PIN T12      - VCCINT                    Bank 999 - VCCBRAM
#Other net   PACKAGE_PIN V12      - VCCINT                    Bank 999 - VCCBRAM
#Other net   PACKAGE_PIN W12      - VCCINT                    Bank 999 - VCCBRAM
#Other net   PACKAGE_PIN M15      - VCCINT                    Bank 999 - VCCINT
#Other net   PACKAGE_PIN M17      - VCCINT                    Bank 999 - VCCINT
#Other net   PACKAGE_PIN M19      - VCCINT                    Bank 999 - VCCINT
#Other net   PACKAGE_PIN M21      - VCCINT                    Bank 999 - VCCINT
#Other net   PACKAGE_PIN N14      - VCCINT                    Bank 999 - VCCINT
#Other net   PACKAGE_PIN N16      - VCCINT                    Bank 999 - VCCINT
#Other net   PACKAGE_PIN N18      - VCCINT                    Bank 999 - VCCINT
#Other net   PACKAGE_PIN N20      - VCCINT                    Bank 999 - VCCINT
#Other net   PACKAGE_PIN P15      - VCCINT                    Bank 999 - VCCINT
#Other net   PACKAGE_PIN P17      - VCCINT                    Bank 999 - VCCINT
#Other net   PACKAGE_PIN P19      - VCCINT                    Bank 999 - VCCINT
#Other net   PACKAGE_PIN P21      - VCCINT                    Bank 999 - VCCINT
#Other net   PACKAGE_PIN R14      - VCCINT                    Bank 999 - VCCINT
#Other net   PACKAGE_PIN R16      - VCCINT                    Bank 999 - VCCINT
#Other net   PACKAGE_PIN R20      - VCCINT                    Bank 999 - VCCINT
#Other net   PACKAGE_PIN T15      - VCCINT                    Bank 999 - VCCINT
#Other net   PACKAGE_PIN T19      - VCCINT                    Bank 999 - VCCINT
#Other net   PACKAGE_PIN T21      - VCCINT                    Bank 999 - VCCINT
#Other net   PACKAGE_PIN U14      - VCCINT                    Bank 999 - VCCINT
#Other net   PACKAGE_PIN U16      - VCCINT                    Bank 999 - VCCINT
#Other net   PACKAGE_PIN U20      - VCCINT                    Bank 999 - VCCINT
#Other net   PACKAGE_PIN V15      - VCCINT                    Bank 999 - VCCINT
#Other net   PACKAGE_PIN V19      - VCCINT                    Bank 999 - VCCINT
#Other net   PACKAGE_PIN V21      - VCCINT                    Bank 999 - VCCINT
#Other net   PACKAGE_PIN W14      - VCCINT                    Bank 999 - VCCINT
#Other net   PACKAGE_PIN W16      - VCCINT                    Bank 999 - VCCINT
#Other net   PACKAGE_PIN W18      - VCCINT                    Bank 999 - VCCINT
#Other net   PACKAGE_PIN W20      - VCCINT                    Bank 999 - VCCINT
#Other net   PACKAGE_PIN Y15      - VCCINT                    Bank 999 - VCCINT
#Other net   PACKAGE_PIN Y17      - VCCINT                    Bank 999 - VCCINT
#Other net   PACKAGE_PIN Y19      - VCCINT                    Bank 999 - VCCINT
#Other net   PACKAGE_PIN P13      - VCCINT                    Bank 999 - VCCINT_IO
#Other net   PACKAGE_PIN T13      - VCCINT                    Bank 999 - VCCINT_IO
#Other net   PACKAGE_PIN U13      - VCCINT                    Bank 999 - VCCINT_IO
#Other net   PACKAGE_PIN V13      - VCCINT                    Bank 999 - VCCINT_IO
#Other net   PACKAGE_PIN Y13      - VCCINT                    Bank 999 - VCCINT_IO
#Other net   PACKAGE_PIN V26      - VCC1V8                    Bank 999 - VCC_PSAUX
#Other net   PACKAGE_PIN W25      - VCC1V8                    Bank 999 - VCC_PSAUX
#Other net   PACKAGE_PIN W26      - VCC1V8                    Bank 999 - VCC_PSAUX
#Other net   PACKAGE_PIN Y25      - VCC1V8                    Bank 999 - VCC_PSAUX
#Other net   PACKAGE_PIN Y23      - VCC_PSBATT                Bank 999 - VCC_PSBATT
#Other net   PACKAGE_PIN U25      - VCCPSDDRPLL               Bank 999 - VCC_PSDDR_PLL
#Other net   PACKAGE_PIN V25      - VCCPSDDRPLL               Bank 999 - VCC_PSDDR_PLL
#Other net   PACKAGE_PIN AA23     - VCCINT                    Bank 999 - VCC_PSINTFP
#Other net   PACKAGE_PIN AB21     - VCCINT                    Bank 999 - VCC_PSINTFP
#Other net   PACKAGE_PIN AB22     - VCCINT                    Bank 999 - VCC_PSINTFP
#Other net   PACKAGE_PIN AB23     - VCCINT                    Bank 999 - VCC_PSINTFP
#Other net   PACKAGE_PIN AB24     - VCCINT                    Bank 999 - VCC_PSINTFP
#Other net   PACKAGE_PIN AC21     - VCCINT                    Bank 999 - VCC_PSINTFP
#Other net   PACKAGE_PIN AC22     - VCCINT                    Bank 999 - VCC_PSINTFP
#Other net   PACKAGE_PIN AB25     - VCCINT                    Bank 999 - VCC_PSINTFP_DDR
#Other net   PACKAGE_PIN AC24     - VCCINT                    Bank 999 - VCC_PSINTFP_DDR
#Other net   PACKAGE_PIN AC25     - VCCINT                    Bank 999 - VCC_PSINTFP_DDR
#Other net   PACKAGE_PIN AA22     - VCCINT                    Bank 999 - VCC_PSINTLP
#Other net   PACKAGE_PIN V22      - VCCINT                    Bank 999 - VCC_PSINTLP
#Other net   PACKAGE_PIN W21      - VCCINT                    Bank 999 - VCC_PSINTLP
#Other net   PACKAGE_PIN W22      - VCCINT                    Bank 999 - VCC_PSINTLP
#Other net   PACKAGE_PIN Y21      - VCCINT                    Bank 999 - VCC_PSINTLP
#Other net   PACKAGE_PIN Y22      - VCCINT                    Bank 999 - VCC_PSINTLP
#Other net   PACKAGE_PIN V24      - MGT1V2                    Bank 999 - VCC_PSPLL
#Other net   PACKAGE_PIN W24      - MGT1V2                    Bank 999 - VCC_PSPLL
#Other net   PACKAGE_PIN Y24      - MGT1V2                    Bank 999 - VCC_PSPLL
#Other net   PACKAGE_PIN AD21     - VCCINT_VCU                Bank 999 - VCCINT_VCU
#Other net   PACKAGE_PIN AD22     - VCCINT_VCU                Bank 999 - VCCINT_VCU
#Other net   PACKAGE_PIN AD23     - VCCINT_VCU                Bank 999 - VCCINT_VCU
#Other net   PACKAGE_PIN AD24     - VCCINT_VCU                Bank 999 - VCCINT_VCU
