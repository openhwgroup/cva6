############################################################################
### VCU118 Rev2.0 XDC 12/08/2017
############################################################################
# Buttons
set_property -dict {PACKAGE_PIN L19 IOSTANDARD  LVCMOS12}  [get_ports cpu_reset] ;# Bank  73 VCCO - VCC1V2_FPGA - IO_T1U_N12_73
set_property PULLDOWN true [get_ports cpu_reset]
# PCIe
set_false_path -from                  [get_ports sys_rst_n]
set_property PULLUP true              [get_ports sys_rst_n]
set_property IOSTANDARD LVCMOS18      [get_ports sys_rst_n]
set_property PACKAGE_PIN AM17         [get_ports sys_rst_n]
create_clock -name sys_clk -period 10 [get_ports sys_clk_p]

set_property -dict {PACKAGE_PIN AC9}  [get_ports sys_clk_p]
set_property -dict {PACKAGE_PIN AC8}  [get_ports sys_clk_n]

# JTAG
set_property -dict {PACKAGE_PIN N28 IOSTANDARD  LVCMOS12}  [get_ports tck] ;   # PMOD1_0
set_property -dict {PACKAGE_PIN M30 IOSTANDARD  LVCMOS12}  [get_ports tdi] ;   # PMOD1_1
set_property -dict {PACKAGE_PIN N30 IOSTANDARD  LVCMOS12}  [get_ports tdo] ;   # PMOD1_2
set_property -dict {PACKAGE_PIN P30 IOSTANDARD  LVCMOS12}  [get_ports tms] ;   # PMOD1_3
set_property -dict {PACKAGE_PIN P29 IOSTANDARD  LVCMOS12}  [get_ports trst_n] ;# PMOD1_4
# accept sub-optimal placement
set_property CLOCK_DEDICATED_ROUTE FALSE [get_nets tck_IBUF_inst/O]

set_property -dict {PACKAGE_PIN AW25 IOSTANDARD  LVCMOS18} [get_ports tx] ;# Bank  64 VCCO - VCC1V8_FPGA - IO_L9P_T1L_N4_AD12P_64
set_property -dict {PACKAGE_PIN BB21 IOSTANDARD  LVCMOS18} [get_ports rx] ;# Bank  64 VCCO - VCC1V8_FPGA - IO_L8N_T1L_N3_AD5N_64

## SD Card **TODO(zarubaf)*** This is wrong for the VCU118
set_property -dict {PACKAGE_PIN AY14 IOSTANDARD  LVCMOS18} [get_ports spi_clk_o] ;# Bank  47 VCCO - VCC1V2_FPGA - IO_L13N_T2L_N1_GC_QBC_47
set_property -dict {PACKAGE_PIN AY15 IOSTANDARD  LVCMOS18} [get_ports spi_clk_o_2] ;# Bank  47 VCCO - VCC1V2_FPGA - IO_L13P_T2L_N0_GC_QBC_47

set_property -dict {PACKAGE_PIN BF16 IOSTANDARD  LVCMOS18} [get_ports spi_ss] ;# Bank  65 VCCO - VCC1V8_FPGA - IO_L2N_T0L_N3_FWE_FCS2_B_65
set_property -dict {PACKAGE_PIN BF20 IOSTANDARD  LVCMOS18} [get_ports spi_ss_2] ;# Bank  65 VCCO - VCC1V8_FPGA - IO_L1N_T0L_N1_DBC_RS1_65

set_property -dict {PACKAGE_PIN AM18 IOSTANDARD  LVCMOS18} [get_ports spi_miso] ;# Bank  65 VCCO - VCC1V8_FPGA - IO_L22N_T3U_N7_DBC_AD0N_D05_65
set_property -dict {PACKAGE_PIN AM19 IOSTANDARD  LVCMOS18} [get_ports spi_mosi] ;# Bank  65 VCCO - VCC1V8_FPGA - IO_L22P_T3U_N6_DBC_AD0P_D04_65
set_property -dict {PACKAGE_PIN AP20 IOSTANDARD  LVCMOS18} [get_ports spi_miso_2] ;# Bank  65 VCCO - VCC1V8_FPGA - IO_L21N_T3L_N5_AD8N_D07_65
set_property -dict {PACKAGE_PIN AN20 IOSTANDARD  LVCMOS18} [get_ports spi_mosi_2] ;# Bank  65 VCCO - VCC1V8_FPGA - IO_L21P_T3L_N4_AD8P_D06_65

# #Other net   PACKAGE_PIN AE17     - DXN                       Bank   0 - DXN
# #Other net   PACKAGE_PIN AE18     - DXP                       Bank   0 - DXP
# #Other net   PACKAGE_PIN AD18     - GND                       Bank   0 - VREFP
# #Other net   PACKAGE_PIN AC17     - GND                       Bank   0 - VREFN
# #Other net   PACKAGE_PIN AC18     - SYSMON_VP                 Bank   0 - VP
# #Other net   PACKAGE_PIN AD17     - SYSMON_VN                 Bank   0 - VN
# #Other net   PACKAGE_PIN U10      - FPGA_M0                   Bank   0 - M0_0
# #Other net   PACKAGE_PIN Y11      - FPGA_M1                   Bank   0 - M1_0
# #Other net   PACKAGE_PIN AC12     - FPGA_INIT_B               Bank   0 - INIT_B_0
# #Other net   PACKAGE_PIN W11      - FPGA_M2                   Bank   0 - M2_0
# #Other net   PACKAGE_PIN AB11     - GND                       Bank   0 - RSVDGND
# #Other net   PACKAGE_PIN AD12     - PUDC_B_PIN                Bank   0 - PUDC_B_0
# #Other net   PACKAGE_PIN AG12     - POR_OVERRIDE_PIN          Bank   0 - POR_OVERRIDE
# #Other net   PACKAGE_PIN AE12     - FPGA_DONE                 Bank   0 - DONE_0
# #Other net   PACKAGE_PIN AH11     - FPGA_PROG_B               Bank   0 - PROGRAM_B_0
# #Other net   PACKAGE_PIN AD13     - FPGA_TDO_FMC_TDI          Bank   0 - TDO_0
# #Other net   PACKAGE_PIN AD15     - JTAG_TDI                  Bank   0 - TDI_0
# #Other net   PACKAGE_PIN AJ11     - QSPI0_CS_B                Bank   0 - RDWR_FCS_B_0
# #Other net   PACKAGE_PIN AM11     - QSPI0_DQ2                 Bank   0 - D02_0
# #Other net   PACKAGE_PIN AP11     - QSPI0_DQ0                 Bank   0 - D00_MOSI_0
# #Other net   PACKAGE_PIN AL11     - QSPI0_DQ3                 Bank   0 - D03_0
# #Other net   PACKAGE_PIN AN11     - QSPI0_DQ1                 Bank   0 - D01_DIN_0
# #Other net   PACKAGE_PIN AF15     - JTAG_TMS                  Bank   0 - TMS_0
# #Other net   PACKAGE_PIN AF13     - QSPI_CCLK                 Bank   0 - CCLK_0
# #Other net   PACKAGE_PIN AE13     - JTAG_TCK                  Bank   0 - TCK_0
# #Other net   PACKAGE_PIN AT11     - FPGA_VBATT                Bank   0 - VBATT
# set_property PACKAGE_PIN B25      [get_ports "RLD3_C3_72B_DM3"] ;# Bank  48 VCCO - VCC1V2_FPGA - IO_L24N_T3U_N11_48
# set_property IOSTANDARD  SSTL12 [get_ports "RLD3_C3_72B_DM3"] ;# Bank  48 VCCO - VCC1V2_FPGA - IO_L24N_T3U_N11_48
# set_property PACKAGE_PIN C25      [get_ports "RLD3_C3_72B_DQ71"] ;# Bank  48 VCCO - VCC1V2_FPGA - IO_L24P_T3U_N10_48
# set_property IOSTANDARD  SSTL12 [get_ports "RLD3_C3_72B_DQ71"] ;# Bank  48 VCCO - VCC1V2_FPGA - IO_L24P_T3U_N10_48
# set_property PACKAGE_PIN D26      [get_ports "RLD3_C3_72B_DQ70"] ;# Bank  48 VCCO - VCC1V2_FPGA - IO_L23N_T3U_N9_48
# set_property IOSTANDARD  SSTL12 [get_ports "RLD3_C3_72B_DQ70"] ;# Bank  48 VCCO - VCC1V2_FPGA - IO_L23N_T3U_N9_48
# set_property PACKAGE_PIN D25      [get_ports "RLD3_C3_72B_DQ69"] ;# Bank  48 VCCO - VCC1V2_FPGA - IO_L23P_T3U_N8_48
# set_property IOSTANDARD  SSTL12 [get_ports "RLD3_C3_72B_DQ69"] ;# Bank  48 VCCO - VCC1V2_FPGA - IO_L23P_T3U_N8_48
# set_property PACKAGE_PIN A26      [get_ports "RLD3_C3_72B_DQ68"] ;# Bank  48 VCCO - VCC1V2_FPGA - IO_L22N_T3U_N7_DBC_AD0N_48
# set_property IOSTANDARD  SSTL12 [get_ports "RLD3_C3_72B_DQ68"] ;# Bank  48 VCCO - VCC1V2_FPGA - IO_L22N_T3U_N7_DBC_AD0N_48
# set_property PACKAGE_PIN B26      [get_ports "RLD3_C3_72B_DQ67"] ;# Bank  48 VCCO - VCC1V2_FPGA - IO_L22P_T3U_N6_DBC_AD0P_48
# set_property IOSTANDARD  SSTL12 [get_ports "RLD3_C3_72B_DQ67"] ;# Bank  48 VCCO - VCC1V2_FPGA - IO_L22P_T3U_N6_DBC_AD0P_48
# set_property PACKAGE_PIN B27      [get_ports "RLD3_C3_72B_DQ66"] ;# Bank  48 VCCO - VCC1V2_FPGA - IO_L21N_T3L_N5_AD8N_48
# set_property IOSTANDARD  SSTL12 [get_ports "RLD3_C3_72B_DQ66"] ;# Bank  48 VCCO - VCC1V2_FPGA - IO_L21N_T3L_N5_AD8N_48
# set_property PACKAGE_PIN C27      [get_ports "RLD3_C3_72B_DQ65"] ;# Bank  48 VCCO - VCC1V2_FPGA - IO_L21P_T3L_N4_AD8P_48
# set_property IOSTANDARD  SSTL12 [get_ports "RLD3_C3_72B_DQ65"] ;# Bank  48 VCCO - VCC1V2_FPGA - IO_L21P_T3L_N4_AD8P_48
# set_property PACKAGE_PIN A28      [get_ports "RLD3_C3_72B_DQ64"] ;# Bank  48 VCCO - VCC1V2_FPGA - IO_L20N_T3L_N3_AD1N_48
# set_property IOSTANDARD  SSTL12 [get_ports "RLD3_C3_72B_DQ64"] ;# Bank  48 VCCO - VCC1V2_FPGA - IO_L20N_T3L_N3_AD1N_48
# set_property PACKAGE_PIN B28      [get_ports "RLD3_C3_72B_DQ63"] ;# Bank  48 VCCO - VCC1V2_FPGA - IO_L20P_T3L_N2_AD1P_48
# set_property IOSTANDARD  SSTL12 [get_ports "RLD3_C3_72B_DQ63"] ;# Bank  48 VCCO - VCC1V2_FPGA - IO_L20P_T3L_N2_AD1P_48
# set_property PACKAGE_PIN C28      [get_ports "RLD3_C3_72B_QK7_N"] ;# Bank  48 VCCO - VCC1V2_FPGA - IO_L19N_T3L_N1_DBC_AD9N_48
# set_property IOSTANDARD  DIFF_SSTL12 [get_ports "RLD3_C3_72B_QK7_N"] ;# Bank  48 VCCO - VCC1V2_FPGA - IO_L19N_T3L_N1_DBC_AD9N_48
# set_property PACKAGE_PIN D27      [get_ports "RLD3_C3_72B_QK7_P"] ;# Bank  48 VCCO - VCC1V2_FPGA - IO_L19P_T3L_N0_DBC_AD9P_48
# set_property IOSTANDARD  DIFF_SSTL12 [get_ports "RLD3_C3_72B_QK7_P"] ;# Bank  48 VCCO - VCC1V2_FPGA - IO_L19P_T3L_N0_DBC_AD9P_48
# #set_property PACKAGE_PIN A25      [get_ports ""] ;# Bank  48 VCCO - VCC1V2_FPGA - IO_T3U_N12_48
# #set_property IOSTANDARD  LVCMOSxx [get_ports ""] ;# Bank  48 VCCO - VCC1V2_FPGA - IO_T3U_N12_48
# #set_property PACKAGE_PIN H25      [get_ports ""] ;# Bank  48 VCCO - VCC1V2_FPGA - IO_T2U_N12_48
# #set_property IOSTANDARD  LVCMOSxx [get_ports ""] ;# Bank  48 VCCO - VCC1V2_FPGA - IO_T2U_N12_48
# set_property PACKAGE_PIN F25      [get_ports "RLD3_C3_72B_QVLD3"] ;# Bank  48 VCCO - VCC1V2_FPGA - IO_L18N_T2U_N11_AD2N_48
# set_property IOSTANDARD  SSTL12 [get_ports "RLD3_C3_72B_QVLD3"] ;# Bank  48 VCCO - VCC1V2_FPGA - IO_L18N_T2U_N11_AD2N_48
# set_property PACKAGE_PIN G25      [get_ports "RLD3_C3_72B_DQ62"] ;# Bank  48 VCCO - VCC1V2_FPGA - IO_L18P_T2U_N10_AD2P_48
# set_property IOSTANDARD  SSTL12 [get_ports "RLD3_C3_72B_DQ62"] ;# Bank  48 VCCO - VCC1V2_FPGA - IO_L18P_T2U_N10_AD2P_48
# set_property PACKAGE_PIN E27      [get_ports "RLD3_C3_72B_DQ61"] ;# Bank  48 VCCO - VCC1V2_FPGA - IO_L17N_T2U_N9_AD10N_48
# set_property IOSTANDARD  SSTL12 [get_ports "RLD3_C3_72B_DQ61"] ;# Bank  48 VCCO - VCC1V2_FPGA - IO_L17N_T2U_N9_AD10N_48
# set_property PACKAGE_PIN E26      [get_ports "RLD3_C3_72B_DQ60"] ;# Bank  48 VCCO - VCC1V2_FPGA - IO_L17P_T2U_N8_AD10P_48
# set_property IOSTANDARD  SSTL12 [get_ports "RLD3_C3_72B_DQ60"] ;# Bank  48 VCCO - VCC1V2_FPGA - IO_L17P_T2U_N8_AD10P_48
# set_property PACKAGE_PIN G28      [get_ports "RLD3_C3_72B_DQ59"] ;# Bank  48 VCCO - VCC1V2_FPGA - IO_L16N_T2U_N7_QBC_AD3N_48
# set_property IOSTANDARD  SSTL12 [get_ports "RLD3_C3_72B_DQ59"] ;# Bank  48 VCCO - VCC1V2_FPGA - IO_L16N_T2U_N7_QBC_AD3N_48
# set_property PACKAGE_PIN H28      [get_ports "RLD3_C3_72B_DQ58"] ;# Bank  48 VCCO - VCC1V2_FPGA - IO_L16P_T2U_N6_QBC_AD3P_48
# set_property IOSTANDARD  SSTL12 [get_ports "RLD3_C3_72B_DQ58"] ;# Bank  48 VCCO - VCC1V2_FPGA - IO_L16P_T2U_N6_QBC_AD3P_48
# set_property PACKAGE_PIN E28      [get_ports "RLD3_C3_72B_DQ57"] ;# Bank  48 VCCO - VCC1V2_FPGA - IO_L15N_T2L_N5_AD11N_48
# set_property IOSTANDARD  SSTL12 [get_ports "RLD3_C3_72B_DQ57"] ;# Bank  48 VCCO - VCC1V2_FPGA - IO_L15N_T2L_N5_AD11N_48
# set_property PACKAGE_PIN F28      [get_ports "RLD3_C3_72B_DQ56"] ;# Bank  48 VCCO - VCC1V2_FPGA - IO_L15P_T2L_N4_AD11P_48
# set_property IOSTANDARD  SSTL12 [get_ports "RLD3_C3_72B_DQ56"] ;# Bank  48 VCCO - VCC1V2_FPGA - IO_L15P_T2L_N4_AD11P_48
# set_property PACKAGE_PIN G27      [get_ports "RLD3_C3_72B_DQ55"] ;# Bank  48 VCCO - VCC1V2_FPGA - IO_L14N_T2L_N3_GC_48
# set_property IOSTANDARD  SSTL12 [get_ports "RLD3_C3_72B_DQ55"] ;# Bank  48 VCCO - VCC1V2_FPGA - IO_L14N_T2L_N3_GC_48
# set_property PACKAGE_PIN H27      [get_ports "RLD3_C3_72B_DQ54"] ;# Bank  48 VCCO - VCC1V2_FPGA - IO_L14P_T2L_N2_GC_48
# set_property IOSTANDARD  SSTL12 [get_ports "RLD3_C3_72B_DQ54"] ;# Bank  48 VCCO - VCC1V2_FPGA - IO_L14P_T2L_N2_GC_48
# set_property PACKAGE_PIN F26      [get_ports "RLD3_C3_72B_QK6_N"] ;# Bank  48 VCCO - VCC1V2_FPGA - IO_L13N_T2L_N1_GC_QBC_48
# set_property IOSTANDARD  DIFF_SSTL12 [get_ports "RLD3_C3_72B_QK6_N"] ;# Bank  48 VCCO - VCC1V2_FPGA - IO_L13N_T2L_N1_GC_QBC_48
# set_property PACKAGE_PIN G26      [get_ports "RLD3_C3_72B_QK6_P"] ;# Bank  48 VCCO - VCC1V2_FPGA - IO_L13P_T2L_N0_GC_QBC_48
# set_property IOSTANDARD  DIFF_SSTL12 [get_ports "RLD3_C3_72B_QK6_P"] ;# Bank  48 VCCO - VCC1V2_FPGA - IO_L13P_T2L_N0_GC_QBC_48
# set_property PACKAGE_PIN J27      [get_ports "RLD3_C3_72B_QVLD2"] ;# Bank  48 VCCO - VCC1V2_FPGA - IO_L12N_T1U_N11_GC_48
# set_property IOSTANDARD  SSTL12 [get_ports "RLD3_C3_72B_QVLD2"] ;# Bank  48 VCCO - VCC1V2_FPGA - IO_L12N_T1U_N11_GC_48
# set_property PACKAGE_PIN K27      [get_ports "RLD3_C3_72B_DQ53"] ;# Bank  48 VCCO - VCC1V2_FPGA - IO_L12P_T1U_N10_GC_48
# set_property IOSTANDARD  SSTL12 [get_ports "RLD3_C3_72B_DQ53"] ;# Bank  48 VCCO - VCC1V2_FPGA - IO_L12P_T1U_N10_GC_48
# set_property PACKAGE_PIN J26      [get_ports "RLD3_C3_72B_DQ52"] ;# Bank  48 VCCO - VCC1V2_FPGA - IO_L11N_T1U_N9_GC_48
# set_property IOSTANDARD  SSTL12 [get_ports "RLD3_C3_72B_DQ52"] ;# Bank  48 VCCO - VCC1V2_FPGA - IO_L11N_T1U_N9_GC_48
# set_property PACKAGE_PIN K26      [get_ports "RLD3_C3_72B_DQ51"] ;# Bank  48 VCCO - VCC1V2_FPGA - IO_L11P_T1U_N8_GC_48
# set_property IOSTANDARD  SSTL12 [get_ports "RLD3_C3_72B_DQ51"] ;# Bank  48 VCCO - VCC1V2_FPGA - IO_L11P_T1U_N8_GC_48
# set_property PACKAGE_PIN L25      [get_ports "RLD3_C3_72B_DQ50"] ;# Bank  48 VCCO - VCC1V2_FPGA - IO_L10N_T1U_N7_QBC_AD4N_48
# set_property IOSTANDARD  SSTL12 [get_ports "RLD3_C3_72B_DQ50"] ;# Bank  48 VCCO - VCC1V2_FPGA - IO_L10N_T1U_N7_QBC_AD4N_48
# set_property PACKAGE_PIN L24      [get_ports "RLD3_C3_72B_DQ49"] ;# Bank  48 VCCO - VCC1V2_FPGA - IO_L10P_T1U_N6_QBC_AD4P_48
# set_property IOSTANDARD  SSTL12 [get_ports "RLD3_C3_72B_DQ49"] ;# Bank  48 VCCO - VCC1V2_FPGA - IO_L10P_T1U_N6_QBC_AD4P_48
# set_property PACKAGE_PIN K28      [get_ports "RLD3_C3_72B_DQ48"] ;# Bank  48 VCCO - VCC1V2_FPGA - IO_L9N_T1L_N5_AD12N_48
# set_property IOSTANDARD  SSTL12 [get_ports "RLD3_C3_72B_DQ48"] ;# Bank  48 VCCO - VCC1V2_FPGA - IO_L9N_T1L_N5_AD12N_48
# set_property PACKAGE_PIN L28      [get_ports "RLD3_C3_72B_DQ47"] ;# Bank  48 VCCO - VCC1V2_FPGA - IO_L9P_T1L_N4_AD12P_48
# set_property IOSTANDARD  SSTL12 [get_ports "RLD3_C3_72B_DQ47"] ;# Bank  48 VCCO - VCC1V2_FPGA - IO_L9P_T1L_N4_AD12P_48
# set_property PACKAGE_PIN L26      [get_ports "RLD3_C3_72B_DQ46"] ;# Bank  48 VCCO - VCC1V2_FPGA - IO_L8N_T1L_N3_AD5N_48
# set_property IOSTANDARD  SSTL12 [get_ports "RLD3_C3_72B_DQ46"] ;# Bank  48 VCCO - VCC1V2_FPGA - IO_L8N_T1L_N3_AD5N_48
# set_property PACKAGE_PIN M25      [get_ports "RLD3_C3_72B_DQ45"] ;# Bank  48 VCCO - VCC1V2_FPGA - IO_L8P_T1L_N2_AD5P_48
# set_property IOSTANDARD  SSTL12 [get_ports "RLD3_C3_72B_DQ45"] ;# Bank  48 VCCO - VCC1V2_FPGA - IO_L8P_T1L_N2_AD5P_48
# set_property PACKAGE_PIN M28      [get_ports "RLD3_C3_72B_QK5_N"] ;# Bank  48 VCCO - VCC1V2_FPGA - IO_L7N_T1L_N1_QBC_AD13N_48
# set_property IOSTANDARD  DIFF_SSTL12 [get_ports "RLD3_C3_72B_QK5_N"] ;# Bank  48 VCCO - VCC1V2_FPGA - IO_L7N_T1L_N1_QBC_AD13N_48
# set_property PACKAGE_PIN M27      [get_ports "RLD3_C3_72B_QK5_P"] ;# Bank  48 VCCO - VCC1V2_FPGA - IO_L7P_T1L_N0_QBC_AD13P_48
# set_property IOSTANDARD  DIFF_SSTL12 [get_ports "RLD3_C3_72B_QK5_P"] ;# Bank  48 VCCO - VCC1V2_FPGA - IO_L7P_T1L_N0_QBC_AD13P_48
# #set_property PACKAGE_PIN J25      [get_ports ""] ;# Bank  48 VCCO - VCC1V2_FPGA - IO_T1U_N12_48
# #set_property IOSTANDARD  LVCMOSxx [get_ports ""] ;# Bank  48 VCCO - VCC1V2_FPGA - IO_T1U_N12_48
# #set_property PACKAGE_PIN M26      [get_ports "VRP_48"] ;# Bank  48 VCCO - VCC1V2_FPGA - IO_T0U_N12_VRP_48
# #set_property IOSTANDARD  LVCMOSxx [get_ports "VRP_48"] ;# Bank  48 VCCO - VCC1V2_FPGA - IO_T0U_N12_VRP_48
# set_property PACKAGE_PIN N24      [get_ports "RLD3_C3_72B_DM2"] ;# Bank  48 VCCO - VCC1V2_FPGA - IO_L6N_T0U_N11_AD6N_48
# set_property IOSTANDARD  SSTL12 [get_ports "RLD3_C3_72B_DM2"] ;# Bank  48 VCCO - VCC1V2_FPGA - IO_L6N_T0U_N11_AD6N_48
# set_property PACKAGE_PIN P24      [get_ports "RLD3_C3_72B_DQ44"] ;# Bank  48 VCCO - VCC1V2_FPGA - IO_L6P_T0U_N10_AD6P_48
# set_property IOSTANDARD  SSTL12 [get_ports "RLD3_C3_72B_DQ44"] ;# Bank  48 VCCO - VCC1V2_FPGA - IO_L6P_T0U_N10_AD6P_48
# set_property PACKAGE_PIN N27      [get_ports "RLD3_C3_72B_DQ43"] ;# Bank  48 VCCO - VCC1V2_FPGA - IO_L5N_T0U_N9_AD14N_48
# set_property IOSTANDARD  SSTL12 [get_ports "RLD3_C3_72B_DQ43"] ;# Bank  48 VCCO - VCC1V2_FPGA - IO_L5N_T0U_N9_AD14N_48
# set_property PACKAGE_PIN P26      [get_ports "RLD3_C3_72B_DQ42"] ;# Bank  48 VCCO - VCC1V2_FPGA - IO_L5P_T0U_N8_AD14P_48
# set_property IOSTANDARD  SSTL12 [get_ports "RLD3_C3_72B_DQ42"] ;# Bank  48 VCCO - VCC1V2_FPGA - IO_L5P_T0U_N8_AD14P_48
# set_property PACKAGE_PIN N25      [get_ports "RLD3_C3_72B_DQ41"] ;# Bank  48 VCCO - VCC1V2_FPGA - IO_L4N_T0U_N7_DBC_AD7N_48
# set_property IOSTANDARD  SSTL12 [get_ports "RLD3_C3_72B_DQ41"] ;# Bank  48 VCCO - VCC1V2_FPGA - IO_L4N_T0U_N7_DBC_AD7N_48
# set_property PACKAGE_PIN P25      [get_ports "RLD3_C3_72B_DQ40"] ;# Bank  48 VCCO - VCC1V2_FPGA - IO_L4P_T0U_N6_DBC_AD7P_48
# set_property IOSTANDARD  SSTL12 [get_ports "RLD3_C3_72B_DQ40"] ;# Bank  48 VCCO - VCC1V2_FPGA - IO_L4P_T0U_N6_DBC_AD7P_48
# set_property PACKAGE_PIN P27      [get_ports "RLD3_C3_72B_DQ39"] ;# Bank  48 VCCO - VCC1V2_FPGA - IO_L3N_T0L_N5_AD15N_48
# set_property IOSTANDARD  SSTL12 [get_ports "RLD3_C3_72B_DQ39"] ;# Bank  48 VCCO - VCC1V2_FPGA - IO_L3N_T0L_N5_AD15N_48
# set_property PACKAGE_PIN R27      [get_ports "RLD3_C3_72B_DQ38"] ;# Bank  48 VCCO - VCC1V2_FPGA - IO_L3P_T0L_N4_AD15P_48
# set_property IOSTANDARD  SSTL12 [get_ports "RLD3_C3_72B_DQ38"] ;# Bank  48 VCCO - VCC1V2_FPGA - IO_L3P_T0L_N4_AD15P_48
# set_property PACKAGE_PIN R24      [get_ports "RLD3_C3_72B_DQ37"] ;# Bank  48 VCCO - VCC1V2_FPGA - IO_L2N_T0L_N3_48
# set_property IOSTANDARD  SSTL12 [get_ports "RLD3_C3_72B_DQ37"] ;# Bank  48 VCCO - VCC1V2_FPGA - IO_L2N_T0L_N3_48
# set_property PACKAGE_PIN T24      [get_ports "RLD3_C3_72B_DQ36"] ;# Bank  48 VCCO - VCC1V2_FPGA - IO_L2P_T0L_N2_48
# set_property IOSTANDARD  SSTL12 [get_ports "RLD3_C3_72B_DQ36"] ;# Bank  48 VCCO - VCC1V2_FPGA - IO_L2P_T0L_N2_48
# set_property PACKAGE_PIN R26      [get_ports "RLD3_C3_72B_QK4_N"] ;# Bank  48 VCCO - VCC1V2_FPGA - IO_L1N_T0L_N1_DBC_48
# set_property IOSTANDARD  DIFF_SSTL12 [get_ports "RLD3_C3_72B_QK4_N"] ;# Bank  48 VCCO - VCC1V2_FPGA - IO_L1N_T0L_N1_DBC_48
# set_property PACKAGE_PIN T26      [get_ports "RLD3_C3_72B_QK4_P"] ;# Bank  48 VCCO - VCC1V2_FPGA - IO_L1P_T0L_N0_DBC_48
# set_property IOSTANDARD  DIFF_SSTL12 [get_ports "RLD3_C3_72B_QK4_P"] ;# Bank  48 VCCO - VCC1V2_FPGA - IO_L1P_T0L_N0_DBC_48
# #Other net   PACKAGE_PIN T25      -                  Bank  48 - VREF_48
# set_property PACKAGE_PIN C29      [get_ports "RLD3_C3_72B_A1"] ;# Bank  47 VCCO - VCC1V2_FPGA - IO_L24N_T3U_N11_47
# set_property IOSTANDARD  SSTL12 [get_ports "RLD3_C3_72B_A1"] ;# Bank  47 VCCO - VCC1V2_FPGA - IO_L24N_T3U_N11_47
# set_property PACKAGE_PIN D29      [get_ports "RLD3_C3_72B_A2"] ;# Bank  47 VCCO - VCC1V2_FPGA - IO_L24P_T3U_N10_47
# set_property IOSTANDARD  SSTL12 [get_ports "RLD3_C3_72B_A2"] ;# Bank  47 VCCO - VCC1V2_FPGA - IO_L24P_T3U_N10_47
# set_property PACKAGE_PIN B30      [get_ports "RLD3_C3_72B_A3"] ;# Bank  47 VCCO - VCC1V2_FPGA - IO_L23N_T3U_N9_47
# set_property IOSTANDARD  SSTL12 [get_ports "RLD3_C3_72B_A3"] ;# Bank  47 VCCO - VCC1V2_FPGA - IO_L23N_T3U_N9_47
# set_property PACKAGE_PIN C30      [get_ports "RLD3_C3_72B_A4"] ;# Bank  47 VCCO - VCC1V2_FPGA - IO_L23P_T3U_N8_47
# set_property IOSTANDARD  SSTL12 [get_ports "RLD3_C3_72B_A4"] ;# Bank  47 VCCO - VCC1V2_FPGA - IO_L23P_T3U_N8_47
# set_property PACKAGE_PIN A31      [get_ports "RLD3_C3_72B_A5"] ;# Bank  47 VCCO - VCC1V2_FPGA - IO_L22N_T3U_N7_DBC_AD0N_47
# set_property IOSTANDARD  SSTL12 [get_ports "RLD3_C3_72B_A5"] ;# Bank  47 VCCO - VCC1V2_FPGA - IO_L22N_T3U_N7_DBC_AD0N_47
# set_property PACKAGE_PIN A30      [get_ports "RLD3_C3_72B_A6"] ;# Bank  47 VCCO - VCC1V2_FPGA - IO_L22P_T3U_N6_DBC_AD0P_47
# set_property IOSTANDARD  SSTL12 [get_ports "RLD3_C3_72B_A6"] ;# Bank  47 VCCO - VCC1V2_FPGA - IO_L22P_T3U_N6_DBC_AD0P_47
# set_property PACKAGE_PIN A33      [get_ports "RLD3_C3_72B_A7"] ;# Bank  47 VCCO - VCC1V2_FPGA - IO_L21N_T3L_N5_AD8N_47
# set_property IOSTANDARD  SSTL12 [get_ports "RLD3_C3_72B_A7"] ;# Bank  47 VCCO - VCC1V2_FPGA - IO_L21N_T3L_N5_AD8N_47
# set_property PACKAGE_PIN B33      [get_ports "RLD3_C3_72B_A8"] ;# Bank  47 VCCO - VCC1V2_FPGA - IO_L21P_T3L_N4_AD8P_47
# set_property IOSTANDARD  SSTL12 [get_ports "RLD3_C3_72B_A8"] ;# Bank  47 VCCO - VCC1V2_FPGA - IO_L21P_T3L_N4_AD8P_47
# set_property PACKAGE_PIN B32      [get_ports "RLD3_C3_72B_A9"] ;# Bank  47 VCCO - VCC1V2_FPGA - IO_L20N_T3L_N3_AD1N_47
# set_property IOSTANDARD  SSTL12 [get_ports "RLD3_C3_72B_A9"] ;# Bank  47 VCCO - VCC1V2_FPGA - IO_L20N_T3L_N3_AD1N_47
# set_property PACKAGE_PIN B31      [get_ports "RLD3_C3_72B_A10"] ;# Bank  47 VCCO - VCC1V2_FPGA - IO_L20P_T3L_N2_AD1P_47
# set_property IOSTANDARD  SSTL12 [get_ports "RLD3_C3_72B_A10"] ;# Bank  47 VCCO - VCC1V2_FPGA - IO_L20P_T3L_N2_AD1P_47
# set_property PACKAGE_PIN C33      [get_ports "RLD3_C3_72B_A11"] ;# Bank  47 VCCO - VCC1V2_FPGA - IO_L19N_T3L_N1_DBC_AD9N_47
# set_property IOSTANDARD  SSTL12 [get_ports "RLD3_C3_72B_A11"] ;# Bank  47 VCCO - VCC1V2_FPGA - IO_L19N_T3L_N1_DBC_AD9N_47
# set_property PACKAGE_PIN C32      [get_ports "RLD3_C3_72B_A12"] ;# Bank  47 VCCO - VCC1V2_FPGA - IO_L19P_T3L_N0_DBC_AD9P_47
# set_property IOSTANDARD  SSTL12 [get_ports "RLD3_C3_72B_A12"] ;# Bank  47 VCCO - VCC1V2_FPGA - IO_L19P_T3L_N0_DBC_AD9P_47
# set_property PACKAGE_PIN A29      [get_ports "RLD3_C3_72B_A0"] ;# Bank  47 VCCO - VCC1V2_FPGA - IO_T3U_N12_47
# set_property IOSTANDARD  SSTL12 [get_ports "RLD3_C3_72B_A0"] ;# Bank  47 VCCO - VCC1V2_FPGA - IO_T3U_N12_47
# set_property PACKAGE_PIN D30      [get_ports "RLD3_C3_72B_A13"] ;# Bank  47 VCCO - VCC1V2_FPGA - IO_T2U_N12_47
# set_property IOSTANDARD  SSTL12 [get_ports "RLD3_C3_72B_A13"] ;# Bank  47 VCCO - VCC1V2_FPGA - IO_T2U_N12_47
# set_property PACKAGE_PIN E29      [get_ports "RLD3_C3_72B_A14"] ;# Bank  47 VCCO - VCC1V2_FPGA - IO_L18N_T2U_N11_AD2N_47
# set_property IOSTANDARD  SSTL12 [get_ports "RLD3_C3_72B_A14"] ;# Bank  47 VCCO - VCC1V2_FPGA - IO_L18N_T2U_N11_AD2N_47
# set_property PACKAGE_PIN F29      [get_ports "RLD3_C3_72B_A15"] ;# Bank  47 VCCO - VCC1V2_FPGA - IO_L18P_T2U_N10_AD2P_47
# set_property IOSTANDARD  SSTL12 [get_ports "RLD3_C3_72B_A15"] ;# Bank  47 VCCO - VCC1V2_FPGA - IO_L18P_T2U_N10_AD2P_47
# set_property PACKAGE_PIN D32      [get_ports "RLD3_C3_72B_A16"] ;# Bank  47 VCCO - VCC1V2_FPGA - IO_L17N_T2U_N9_AD10N_47
# set_property IOSTANDARD  SSTL12 [get_ports "RLD3_C3_72B_A16"] ;# Bank  47 VCCO - VCC1V2_FPGA - IO_L17N_T2U_N9_AD10N_47
# set_property PACKAGE_PIN E32      [get_ports "RLD3_C3_72B_A17"] ;# Bank  47 VCCO - VCC1V2_FPGA - IO_L17P_T2U_N8_AD10P_47
# set_property IOSTANDARD  SSTL12 [get_ports "RLD3_C3_72B_A17"] ;# Bank  47 VCCO - VCC1V2_FPGA - IO_L17P_T2U_N8_AD10P_47
# set_property PACKAGE_PIN D31      [get_ports "RLD3_C3_72B_A18"] ;# Bank  47 VCCO - VCC1V2_FPGA - IO_L16N_T2U_N7_QBC_AD3N_47
# set_property IOSTANDARD  SSTL12 [get_ports "RLD3_C3_72B_A18"] ;# Bank  47 VCCO - VCC1V2_FPGA - IO_L16N_T2U_N7_QBC_AD3N_47
# set_property PACKAGE_PIN E31      [get_ports "RLD3_C3_72B_A19"] ;# Bank  47 VCCO - VCC1V2_FPGA - IO_L16P_T2U_N6_QBC_AD3P_47
# set_property IOSTANDARD  SSTL12 [get_ports "RLD3_C3_72B_A19"] ;# Bank  47 VCCO - VCC1V2_FPGA - IO_L16P_T2U_N6_QBC_AD3P_47
# set_property PACKAGE_PIN E33      [get_ports "RLD3_C3_72B_BA0"] ;# Bank  47 VCCO - VCC1V2_FPGA - IO_L15N_T2L_N5_AD11N_47
# set_property IOSTANDARD  SSTL12 [get_ports "RLD3_C3_72B_BA0"] ;# Bank  47 VCCO - VCC1V2_FPGA - IO_L15N_T2L_N5_AD11N_47
# set_property PACKAGE_PIN F33      [get_ports "RLD3_C3_72B_BA1"] ;# Bank  47 VCCO - VCC1V2_FPGA - IO_L15P_T2L_N4_AD11P_47
# set_property IOSTANDARD  SSTL12 [get_ports "RLD3_C3_72B_BA1"] ;# Bank  47 VCCO - VCC1V2_FPGA - IO_L15P_T2L_N4_AD11P_47
# set_property PACKAGE_PIN F30      [get_ports "RLD3_C3_72B_BA2"] ;# Bank  47 VCCO - VCC1V2_FPGA - IO_L14N_T2L_N3_GC_47
# set_property IOSTANDARD  SSTL12 [get_ports "RLD3_C3_72B_BA2"] ;# Bank  47 VCCO - VCC1V2_FPGA - IO_L14N_T2L_N3_GC_47
# set_property PACKAGE_PIN G30      [get_ports "RLD3_C3_72B_BA3"] ;# Bank  47 VCCO - VCC1V2_FPGA - IO_L14P_T2L_N2_GC_47
# set_property IOSTANDARD  SSTL12 [get_ports "RLD3_C3_72B_BA3"] ;# Bank  47 VCCO - VCC1V2_FPGA - IO_L14P_T2L_N2_GC_47
# set_property PACKAGE_PIN F31      [get_ports "SYSCLK1_300_N"] ;# Bank  47 VCCO - VCC1V2_FPGA - IO_L13N_T2L_N1_GC_QBC_47
# set_property IOSTANDARD  DIFF_SSTL12 [get_ports "SYSCLK1_300_N"] ;# Bank  47 VCCO - VCC1V2_FPGA - IO_L13N_T2L_N1_GC_QBC_47
# set_property PACKAGE_PIN G31      [get_ports "SYSCLK1_300_P"] ;# Bank  47 VCCO - VCC1V2_FPGA - IO_L13P_T2L_N0_GC_QBC_47
# set_property IOSTANDARD  DIFF_SSTL12 [get_ports "SYSCLK1_300_P"] ;# Bank  47 VCCO - VCC1V2_FPGA - IO_L13P_T2L_N0_GC_QBC_47
# set_property PACKAGE_PIN G32      [get_ports "USER_SI570_CLOCK_N"] ;# Bank  47 VCCO - VCC1V2_FPGA - IO_L12N_T1U_N11_GC_47
# set_property IOSTANDARD  DIFF_SSTL12 [get_ports "USER_SI570_CLOCK_N"] ;# Bank  47 VCCO - VCC1V2_FPGA - IO_L12N_T1U_N11_GC_47
# set_property PACKAGE_PIN H32      [get_ports "USER_SI570_CLOCK_P"] ;# Bank  47 VCCO - VCC1V2_FPGA - IO_L12P_T1U_N10_GC_47
# set_property IOSTANDARD  DIFF_SSTL12 [get_ports "USER_SI570_CLOCK_P"] ;# Bank  47 VCCO - VCC1V2_FPGA - IO_L12P_T1U_N10_GC_47
# set_property PACKAGE_PIN H30      [get_ports "RLD3_C3_72B_CK_N"] ;# Bank  47 VCCO - VCC1V2_FPGA - IO_L11N_T1U_N9_GC_47
# set_property IOSTANDARD  DIFF_SSTL12 [get_ports "RLD3_C3_72B_CK_N"] ;# Bank  47 VCCO - VCC1V2_FPGA - IO_L11N_T1U_N9_GC_47
# set_property PACKAGE_PIN H29      [get_ports "RLD3_C3_72B_CK_P"] ;# Bank  47 VCCO - VCC1V2_FPGA - IO_L11P_T1U_N8_GC_47
# set_property IOSTANDARD  DIFF_SSTL12 [get_ports "RLD3_C3_72B_CK_P"] ;# Bank  47 VCCO - VCC1V2_FPGA - IO_L11P_T1U_N8_GC_47
# set_property PACKAGE_PIN G33      [get_ports "RLD3_C3_72B_DK3_N"] ;# Bank  47 VCCO - VCC1V2_FPGA - IO_L10N_T1U_N7_QBC_AD4N_47
# set_property IOSTANDARD  DIFF_SSTL12 [get_ports "RLD3_C3_72B_DK3_N"] ;# Bank  47 VCCO - VCC1V2_FPGA - IO_L10N_T1U_N7_QBC_AD4N_47
# set_property PACKAGE_PIN H33      [get_ports "RLD3_C3_72B_DK3_P"] ;# Bank  47 VCCO - VCC1V2_FPGA - IO_L10P_T1U_N6_QBC_AD4P_47
# set_property IOSTANDARD  DIFF_SSTL12 [get_ports "RLD3_C3_72B_DK3_P"] ;# Bank  47 VCCO - VCC1V2_FPGA - IO_L10P_T1U_N6_QBC_AD4P_47
# set_property PACKAGE_PIN J30      [get_ports "RLD3_C3_72B_DK2_N"] ;# Bank  47 VCCO - VCC1V2_FPGA - IO_L9N_T1L_N5_AD12N_47
# set_property IOSTANDARD  DIFF_SSTL12 [get_ports "RLD3_C3_72B_DK2_N"] ;# Bank  47 VCCO - VCC1V2_FPGA - IO_L9N_T1L_N5_AD12N_47
# set_property PACKAGE_PIN J29      [get_ports "RLD3_C3_72B_DK2_P"] ;# Bank  47 VCCO - VCC1V2_FPGA - IO_L9P_T1L_N4_AD12P_47
# set_property IOSTANDARD  DIFF_SSTL12 [get_ports "RLD3_C3_72B_DK2_P"] ;# Bank  47 VCCO - VCC1V2_FPGA - IO_L9P_T1L_N4_AD12P_47
# set_property PACKAGE_PIN J32      [get_ports "RLD3_C3_72B_DK1_N"] ;# Bank  47 VCCO - VCC1V2_FPGA - IO_L8N_T1L_N3_AD5N_47
# set_property IOSTANDARD  DIFF_SSTL12 [get_ports "RLD3_C3_72B_DK1_N"] ;# Bank  47 VCCO - VCC1V2_FPGA - IO_L8N_T1L_N3_AD5N_47
# set_property PACKAGE_PIN K32      [get_ports "RLD3_C3_72B_DK1_P"] ;# Bank  47 VCCO - VCC1V2_FPGA - IO_L8P_T1L_N2_AD5P_47
# set_property IOSTANDARD  DIFF_SSTL12 [get_ports "RLD3_C3_72B_DK1_P"] ;# Bank  47 VCCO - VCC1V2_FPGA - IO_L8P_T1L_N2_AD5P_47
# set_property PACKAGE_PIN J31      [get_ports "RLD3_C3_72B_DK0_N"] ;# Bank  47 VCCO - VCC1V2_FPGA - IO_L7N_T1L_N1_QBC_AD13N_47
# set_property IOSTANDARD  DIFF_SSTL12 [get_ports "RLD3_C3_72B_DK0_N"] ;# Bank  47 VCCO - VCC1V2_FPGA - IO_L7N_T1L_N1_QBC_AD13N_47
# set_property PACKAGE_PIN K31      [get_ports "RLD3_C3_72B_DK0_P"] ;# Bank  47 VCCO - VCC1V2_FPGA - IO_L7P_T1L_N0_QBC_AD13P_47
# set_property IOSTANDARD  DIFF_SSTL12 [get_ports "RLD3_C3_72B_DK0_P"] ;# Bank  47 VCCO - VCC1V2_FPGA - IO_L7P_T1L_N0_QBC_AD13P_47
# set_property PACKAGE_PIN K29      [get_ports "RLD3_C3_72B_WE_B"] ;# Bank  47 VCCO - VCC1V2_FPGA - IO_T1U_N12_47
# set_property IOSTANDARD  SSTL12 [get_ports "RLD3_C3_72B_WE_B"] ;# Bank  47 VCCO - VCC1V2_FPGA - IO_T1U_N12_47
# #set_property PACKAGE_PIN T29      [get_ports "VRP_47"] ;# Bank  47 VCCO - VCC1V2_FPGA - IO_T0U_N12_VRP_47
# #set_property IOSTANDARD  LVCMOSxx [get_ports "VRP_47"] ;# Bank  47 VCCO - VCC1V2_FPGA - IO_T0U_N12_VRP_47
# set_property PACKAGE_PIN L30      [get_ports "RLD3_C3_72B_REF_B"] ;# Bank  47 VCCO - VCC1V2_FPGA - IO_L6N_T0U_N11_AD6N_47
# set_property IOSTANDARD  SSTL12 [get_ports "RLD3_C3_72B_REF_B"] ;# Bank  47 VCCO - VCC1V2_FPGA - IO_L6N_T0U_N11_AD6N_47
# set_property PACKAGE_PIN L29      [get_ports "RLD3_C3_72B_RESET_B"] ;# Bank  47 VCCO - VCC1V2_FPGA - IO_L6P_T0U_N10_AD6P_47
# set_property IOSTANDARD  LVCMOS12 [get_ports "RLD3_C3_72B_RESET_B"] ;# Bank  47 VCCO - VCC1V2_FPGA - IO_L6P_T0U_N10_AD6P_47
# set_property PACKAGE_PIN N29      [get_ports "RLD3_C3_72B_CS_B"] ;# Bank  47 VCCO - VCC1V2_FPGA - IO_L5N_T0U_N9_AD14N_47
# set_property IOSTANDARD  SSTL12 [get_ports "RLD3_C3_72B_CS_B"] ;# Bank  47 VCCO - VCC1V2_FPGA - IO_L5N_T0U_N9_AD14N_47

# set_property PACKAGE_PIN R28      [get_ports "RLD3_C3_72B_A20"] ;# Bank  47 VCCO - VCC1V2_FPGA - IO_L1P_T0L_N0_DBC_47
# set_property IOSTANDARD  SSTL12 [get_ports "RLD3_C3_72B_A20"] ;# Bank  47 VCCO - VCC1V2_FPGA - IO_L1P_T0L_N0_DBC_47
# #Other net   PACKAGE_PIN T28      - 43N2999                   Bank  47 - VREF_47
# set_property PACKAGE_PIN A35      [get_ports "RLD3_C3_72B_DM1"] ;# Bank  46 VCCO - VCC1V2_FPGA - IO_L24N_T3U_N11_46
# set_property IOSTANDARD  SSTL12 [get_ports "RLD3_C3_72B_DM1"] ;# Bank  46 VCCO - VCC1V2_FPGA - IO_L24N_T3U_N11_46
# set_property PACKAGE_PIN A34      [get_ports "RLD3_C3_72B_DQ35"] ;# Bank  46 VCCO - VCC1V2_FPGA - IO_L24P_T3U_N10_46
# set_property IOSTANDARD  SSTL12 [get_ports "RLD3_C3_72B_DQ35"] ;# Bank  46 VCCO - VCC1V2_FPGA - IO_L24P_T3U_N10_46
# set_property PACKAGE_PIN A36      [get_ports "RLD3_C3_72B_DQ34"] ;# Bank  46 VCCO - VCC1V2_FPGA - IO_L23N_T3U_N9_46
# set_property IOSTANDARD  SSTL12 [get_ports "RLD3_C3_72B_DQ34"] ;# Bank  46 VCCO - VCC1V2_FPGA - IO_L23N_T3U_N9_46
# set_property PACKAGE_PIN B35      [get_ports "RLD3_C3_72B_DQ33"] ;# Bank  46 VCCO - VCC1V2_FPGA - IO_L23P_T3U_N8_46
# set_property IOSTANDARD  SSTL12 [get_ports "RLD3_C3_72B_DQ33"] ;# Bank  46 VCCO - VCC1V2_FPGA - IO_L23P_T3U_N8_46
# set_property PACKAGE_PIN B37      [get_ports "RLD3_C3_72B_DQ32"] ;# Bank  46 VCCO - VCC1V2_FPGA - IO_L22N_T3U_N7_DBC_AD0N_46
# set_property IOSTANDARD  SSTL12 [get_ports "RLD3_C3_72B_DQ32"] ;# Bank  46 VCCO - VCC1V2_FPGA - IO_L22N_T3U_N7_DBC_AD0N_46
# set_property PACKAGE_PIN B36      [get_ports "RLD3_C3_72B_DQ31"] ;# Bank  46 VCCO - VCC1V2_FPGA - IO_L22P_T3U_N6_DBC_AD0P_46
# set_property IOSTANDARD  SSTL12 [get_ports "RLD3_C3_72B_DQ31"] ;# Bank  46 VCCO - VCC1V2_FPGA - IO_L22P_T3U_N6_DBC_AD0P_46
# set_property PACKAGE_PIN C34      [get_ports "RLD3_C3_72B_DQ30"] ;# Bank  46 VCCO - VCC1V2_FPGA - IO_L21N_T3L_N5_AD8N_46
# set_property IOSTANDARD  SSTL12 [get_ports "RLD3_C3_72B_DQ30"] ;# Bank  46 VCCO - VCC1V2_FPGA - IO_L21N_T3L_N5_AD8N_46
# set_property PACKAGE_PIN D34      [get_ports "RLD3_C3_72B_DQ29"] ;# Bank  46 VCCO - VCC1V2_FPGA - IO_L21P_T3L_N4_AD8P_46
# set_property IOSTANDARD  SSTL12 [get_ports "RLD3_C3_72B_DQ29"] ;# Bank  46 VCCO - VCC1V2_FPGA - IO_L21P_T3L_N4_AD8P_46
# set_property PACKAGE_PIN C35      [get_ports "RLD3_C3_72B_DQ28"] ;# Bank  46 VCCO - VCC1V2_FPGA - IO_L20N_T3L_N3_AD1N_46
# set_property IOSTANDARD  SSTL12 [get_ports "RLD3_C3_72B_DQ28"] ;# Bank  46 VCCO - VCC1V2_FPGA - IO_L20N_T3L_N3_AD1N_46
# set_property PACKAGE_PIN D35      [get_ports "RLD3_C3_72B_DQ27"] ;# Bank  46 VCCO - VCC1V2_FPGA - IO_L20P_T3L_N2_AD1P_46
# set_property IOSTANDARD  SSTL12 [get_ports "RLD3_C3_72B_DQ27"] ;# Bank  46 VCCO - VCC1V2_FPGA - IO_L20P_T3L_N2_AD1P_46
# set_property PACKAGE_PIN C37      [get_ports "RLD3_C3_72B_QK3_N"] ;# Bank  46 VCCO - VCC1V2_FPGA - IO_L19N_T3L_N1_DBC_AD9N_46
# set_property IOSTANDARD  DIFF_SSTL12 [get_ports "RLD3_C3_72B_QK3_N"] ;# Bank  46 VCCO - VCC1V2_FPGA - IO_L19N_T3L_N1_DBC_AD9N_46
# set_property PACKAGE_PIN D37      [get_ports "RLD3_C3_72B_QK3_P"] ;# Bank  46 VCCO - VCC1V2_FPGA - IO_L19P_T3L_N0_DBC_AD9P_46
# set_property IOSTANDARD  DIFF_SSTL12 [get_ports "RLD3_C3_72B_QK3_P"] ;# Bank  46 VCCO - VCC1V2_FPGA - IO_L19P_T3L_N0_DBC_AD9P_46
# #set_property PACKAGE_PIN D36      [get_ports ""] ;# Bank  46 VCCO - VCC1V2_FPGA - IO_T3U_N12_46
# #set_property IOSTANDARD  LVCMOSxx [get_ports ""] ;# Bank  46 VCCO - VCC1V2_FPGA - IO_T3U_N12_46
# #set_property PACKAGE_PIN C38      [get_ports ""] ;# Bank  46 VCCO - VCC1V2_FPGA - IO_T2U_N12_46
# #set_property IOSTANDARD  LVCMOSxx [get_ports ""] ;# Bank  46 VCCO - VCC1V2_FPGA - IO_T2U_N12_46
# set_property PACKAGE_PIN A38      [get_ports "RLD3_C3_72B_QVLD1"] ;# Bank  46 VCCO - VCC1V2_FPGA - IO_L18N_T2U_N11_AD2N_46
# set_property IOSTANDARD  SSTL12 [get_ports "RLD3_C3_72B_QVLD1"] ;# Bank  46 VCCO - VCC1V2_FPGA - IO_L18N_T2U_N11_AD2N_46
# set_property PACKAGE_PIN B38      [get_ports "RLD3_C3_72B_DQ26"] ;# Bank  46 VCCO - VCC1V2_FPGA - IO_L18P_T2U_N10_AD2P_46
# set_property IOSTANDARD  SSTL12 [get_ports "RLD3_C3_72B_DQ26"] ;# Bank  46 VCCO - VCC1V2_FPGA - IO_L18P_T2U_N10_AD2P_46
# set_property PACKAGE_PIN C40      [get_ports "RLD3_C3_72B_DQ25"] ;# Bank  46 VCCO - VCC1V2_FPGA - IO_L17N_T2U_N9_AD10N_46
# set_property IOSTANDARD  SSTL12 [get_ports "RLD3_C3_72B_DQ25"] ;# Bank  46 VCCO - VCC1V2_FPGA - IO_L17N_T2U_N9_AD10N_46
# set_property PACKAGE_PIN D40      [get_ports "RLD3_C3_72B_DQ24"] ;# Bank  46 VCCO - VCC1V2_FPGA - IO_L17P_T2U_N8_AD10P_46
# set_property IOSTANDARD  SSTL12 [get_ports "RLD3_C3_72B_DQ24"] ;# Bank  46 VCCO - VCC1V2_FPGA - IO_L17P_T2U_N8_AD10P_46
# set_property PACKAGE_PIN A40      [get_ports "RLD3_C3_72B_DQ23"] ;# Bank  46 VCCO - VCC1V2_FPGA - IO_L16N_T2U_N7_QBC_AD3N_46
# set_property IOSTANDARD  SSTL12 [get_ports "RLD3_C3_72B_DQ23"] ;# Bank  46 VCCO - VCC1V2_FPGA - IO_L16N_T2U_N7_QBC_AD3N_46
# set_property PACKAGE_PIN A39      [get_ports "RLD3_C3_72B_DQ22"] ;# Bank  46 VCCO - VCC1V2_FPGA - IO_L16P_T2U_N6_QBC_AD3P_46
# set_property IOSTANDARD  SSTL12 [get_ports "RLD3_C3_72B_DQ22"] ;# Bank  46 VCCO - VCC1V2_FPGA - IO_L16P_T2U_N6_QBC_AD3P_46
# set_property PACKAGE_PIN B40      [get_ports "RLD3_C3_72B_DQ21"] ;# Bank  46 VCCO - VCC1V2_FPGA - IO_L15N_T2L_N5_AD11N_46
# set_property IOSTANDARD  SSTL12 [get_ports "RLD3_C3_72B_DQ21"] ;# Bank  46 VCCO - VCC1V2_FPGA - IO_L15N_T2L_N5_AD11N_46
# set_property PACKAGE_PIN C39      [get_ports "RLD3_C3_72B_DQ20"] ;# Bank  46 VCCO - VCC1V2_FPGA - IO_L15P_T2L_N4_AD11P_46
# set_property IOSTANDARD  SSTL12 [get_ports "RLD3_C3_72B_DQ20"] ;# Bank  46 VCCO - VCC1V2_FPGA - IO_L15P_T2L_N4_AD11P_46
# set_property PACKAGE_PIN E38      [get_ports "RLD3_C3_72B_DQ19"] ;# Bank  46 VCCO - VCC1V2_FPGA - IO_L14N_T2L_N3_GC_46
# set_property IOSTANDARD  SSTL12 [get_ports "RLD3_C3_72B_DQ19"] ;# Bank  46 VCCO - VCC1V2_FPGA - IO_L14N_T2L_N3_GC_46
# set_property PACKAGE_PIN E37      [get_ports "RLD3_C3_72B_DQ18"] ;# Bank  46 VCCO - VCC1V2_FPGA - IO_L14P_T2L_N2_GC_46
# set_property IOSTANDARD  SSTL12 [get_ports "RLD3_C3_72B_DQ18"] ;# Bank  46 VCCO - VCC1V2_FPGA - IO_L14P_T2L_N2_GC_46
# set_property PACKAGE_PIN D39      [get_ports "RLD3_C3_72B_QK2_N"] ;# Bank  46 VCCO - VCC1V2_FPGA - IO_L13N_T2L_N1_GC_QBC_46
# set_property IOSTANDARD  DIFF_SSTL12 [get_ports "RLD3_C3_72B_QK2_N"] ;# Bank  46 VCCO - VCC1V2_FPGA - IO_L13N_T2L_N1_GC_QBC_46
# set_property PACKAGE_PIN E39      [get_ports "RLD3_C3_72B_QK2_P"] ;# Bank  46 VCCO - VCC1V2_FPGA - IO_L13P_T2L_N0_GC_QBC_46
# set_property IOSTANDARD  DIFF_SSTL12 [get_ports "RLD3_C3_72B_QK2_P"] ;# Bank  46 VCCO - VCC1V2_FPGA - IO_L13P_T2L_N0_GC_QBC_46
# set_property PACKAGE_PIN G37      [get_ports "RLD3_C3_72B_QVLD0"] ;# Bank  46 VCCO - VCC1V2_FPGA - IO_L12N_T1U_N11_GC_46
# set_property IOSTANDARD  SSTL12 [get_ports "RLD3_C3_72B_QVLD0"] ;# Bank  46 VCCO - VCC1V2_FPGA - IO_L12N_T1U_N11_GC_46
# set_property PACKAGE_PIN G36      [get_ports "RLD3_C3_72B_DQ17"] ;# Bank  46 VCCO - VCC1V2_FPGA - IO_L12P_T1U_N10_GC_46
# set_property IOSTANDARD  SSTL12 [get_ports "RLD3_C3_72B_DQ17"] ;# Bank  46 VCCO - VCC1V2_FPGA - IO_L12P_T1U_N10_GC_46
# set_property PACKAGE_PIN F36      [get_ports "RLD3_C3_72B_DQ16"] ;# Bank  46 VCCO - VCC1V2_FPGA - IO_L11N_T1U_N9_GC_46
# set_property IOSTANDARD  SSTL12 [get_ports "RLD3_C3_72B_DQ16"] ;# Bank  46 VCCO - VCC1V2_FPGA - IO_L11N_T1U_N9_GC_46
# set_property PACKAGE_PIN F35      [get_ports "RLD3_C3_72B_DQ15"] ;# Bank  46 VCCO - VCC1V2_FPGA - IO_L11P_T1U_N8_GC_46
# set_property IOSTANDARD  SSTL12 [get_ports "RLD3_C3_72B_DQ15"] ;# Bank  46 VCCO - VCC1V2_FPGA - IO_L11P_T1U_N8_GC_46
# set_property PACKAGE_PIN G35      [get_ports "RLD3_C3_72B_DQ14"] ;# Bank  46 VCCO - VCC1V2_FPGA - IO_L10N_T1U_N7_QBC_AD4N_46
# set_property IOSTANDARD  SSTL12 [get_ports "RLD3_C3_72B_DQ14"] ;# Bank  46 VCCO - VCC1V2_FPGA - IO_L10N_T1U_N7_QBC_AD4N_46
# set_property PACKAGE_PIN H34      [get_ports "RLD3_C3_72B_DQ13"] ;# Bank  46 VCCO - VCC1V2_FPGA - IO_L10P_T1U_N6_QBC_AD4P_46
# set_property IOSTANDARD  SSTL12 [get_ports "RLD3_C3_72B_DQ13"] ;# Bank  46 VCCO - VCC1V2_FPGA - IO_L10P_T1U_N6_QBC_AD4P_46
# set_property PACKAGE_PIN H37      [get_ports "RLD3_C3_72B_DQ12"] ;# Bank  46 VCCO - VCC1V2_FPGA - IO_L9N_T1L_N5_AD12N_46
# set_property IOSTANDARD  SSTL12 [get_ports "RLD3_C3_72B_DQ12"] ;# Bank  46 VCCO - VCC1V2_FPGA - IO_L9N_T1L_N5_AD12N_46
# set_property PACKAGE_PIN J36      [get_ports "RLD3_C3_72B_DQ11"] ;# Bank  46 VCCO - VCC1V2_FPGA - IO_L9P_T1L_N4_AD12P_46
# set_property IOSTANDARD  SSTL12 [get_ports "RLD3_C3_72B_DQ11"] ;# Bank  46 VCCO - VCC1V2_FPGA - IO_L9P_T1L_N4_AD12P_46
# set_property PACKAGE_PIN H35      [get_ports "RLD3_C3_72B_DQ10"] ;# Bank  46 VCCO - VCC1V2_FPGA - IO_L8N_T1L_N3_AD5N_46
# set_property IOSTANDARD  SSTL12 [get_ports "RLD3_C3_72B_DQ10"] ;# Bank  46 VCCO - VCC1V2_FPGA - IO_L8N_T1L_N3_AD5N_46
# set_property PACKAGE_PIN J35      [get_ports "RLD3_C3_72B_DQ9"] ;# Bank  46 VCCO - VCC1V2_FPGA - IO_L8P_T1L_N2_AD5P_46
# set_property IOSTANDARD  SSTL12 [get_ports "RLD3_C3_72B_DQ9"] ;# Bank  46 VCCO - VCC1V2_FPGA - IO_L8P_T1L_N2_AD5P_46
# set_property PACKAGE_PIN E34      [get_ports "RLD3_C3_72B_QK1_N"] ;# Bank  46 VCCO - VCC1V2_FPGA - IO_L7N_T1L_N1_QBC_AD13N_46
# set_property IOSTANDARD  DIFF_SSTL12 [get_ports "RLD3_C3_72B_QK1_N"] ;# Bank  46 VCCO - VCC1V2_FPGA - IO_L7N_T1L_N1_QBC_AD13N_46
# set_property PACKAGE_PIN F34      [get_ports "RLD3_C3_72B_QK1_P"] ;# Bank  46 VCCO - VCC1V2_FPGA - IO_L7P_T1L_N0_QBC_AD13P_46
# set_property IOSTANDARD  DIFF_SSTL12 [get_ports "RLD3_C3_72B_QK1_P"] ;# Bank  46 VCCO - VCC1V2_FPGA - IO_L7P_T1L_N0_QBC_AD13P_46
# #set_property PACKAGE_PIN E36      [get_ports ""] ;# Bank  46 VCCO - VCC1V2_FPGA - IO_T1U_N12_46
# #set_property IOSTANDARD  LVCMOSxx [get_ports ""] ;# Bank  46 VCCO - VCC1V2_FPGA - IO_T1U_N12_46
# #set_property PACKAGE_PIN K38      [get_ports "VRP_46"] ;# Bank  46 VCCO - VCC1V2_FPGA - IO_T0U_N12_VRP_46
# #set_property IOSTANDARD  LVCMOSxx [get_ports "VRP_46"] ;# Bank  46 VCCO - VCC1V2_FPGA - IO_T0U_N12_VRP_46
# set_property PACKAGE_PIN F39      [get_ports "RLD3_C3_72B_DM0"] ;# Bank  46 VCCO - VCC1V2_FPGA - IO_L6N_T0U_N11_AD6N_46
# set_property IOSTANDARD  SSTL12 [get_ports "RLD3_C3_72B_DM0"] ;# Bank  46 VCCO - VCC1V2_FPGA - IO_L6N_T0U_N11_AD6N_46
# set_property PACKAGE_PIN F38      [get_ports "RLD3_C3_72B_DQ8"] ;# Bank  46 VCCO - VCC1V2_FPGA - IO_L6P_T0U_N10_AD6P_46
# set_property IOSTANDARD  SSTL12 [get_ports "RLD3_C3_72B_DQ8"] ;# Bank  46 VCCO - VCC1V2_FPGA - IO_L6P_T0U_N10_AD6P_46
# set_property PACKAGE_PIN J37      [get_ports "RLD3_C3_72B_DQ7"] ;# Bank  46 VCCO - VCC1V2_FPGA - IO_L5N_T0U_N9_AD14N_46
# set_property IOSTANDARD  SSTL12 [get_ports "RLD3_C3_72B_DQ7"] ;# Bank  46 VCCO - VCC1V2_FPGA - IO_L5N_T0U_N9_AD14N_46
# set_property PACKAGE_PIN K37      [get_ports "RLD3_C3_72B_DQ6"] ;# Bank  46 VCCO - VCC1V2_FPGA - IO_L5P_T0U_N8_AD14P_46
# set_property IOSTANDARD  SSTL12 [get_ports "RLD3_C3_72B_DQ6"] ;# Bank  46 VCCO - VCC1V2_FPGA - IO_L5P_T0U_N8_AD14P_46
# set_property PACKAGE_PIN G38      [get_ports "RLD3_C3_72B_DQ5"] ;# Bank  46 VCCO - VCC1V2_FPGA - IO_L4N_T0U_N7_DBC_AD7N_46
# set_property IOSTANDARD  SSTL12 [get_ports "RLD3_C3_72B_DQ5"] ;# Bank  46 VCCO - VCC1V2_FPGA - IO_L4N_T0U_N7_DBC_AD7N_46
# set_property PACKAGE_PIN H38      [get_ports "RLD3_C3_72B_DQ4"] ;# Bank  46 VCCO - VCC1V2_FPGA - IO_L4P_T0U_N6_DBC_AD7P_46
# set_property IOSTANDARD  SSTL12 [get_ports "RLD3_C3_72B_DQ4"] ;# Bank  46 VCCO - VCC1V2_FPGA - IO_L4P_T0U_N6_DBC_AD7P_46
# set_property PACKAGE_PIN F40      [get_ports "RLD3_C3_72B_DQ3"] ;# Bank  46 VCCO - VCC1V2_FPGA - IO_L3N_T0L_N5_AD15N_46
# set_property IOSTANDARD  SSTL12 [get_ports "RLD3_C3_72B_DQ3"] ;# Bank  46 VCCO - VCC1V2_FPGA - IO_L3N_T0L_N5_AD15N_46
# set_property PACKAGE_PIN G40      [get_ports "RLD3_C3_72B_DQ2"] ;# Bank  46 VCCO - VCC1V2_FPGA - IO_L3P_T0L_N4_AD15P_46
# set_property IOSTANDARD  SSTL12 [get_ports "RLD3_C3_72B_DQ2"] ;# Bank  46 VCCO - VCC1V2_FPGA - IO_L3P_T0L_N4_AD15P_46
# set_property PACKAGE_PIN H40      [get_ports "RLD3_C3_72B_DQ1"] ;# Bank  46 VCCO - VCC1V2_FPGA - IO_L2N_T0L_N3_46
# set_property IOSTANDARD  SSTL12 [get_ports "RLD3_C3_72B_DQ1"] ;# Bank  46 VCCO - VCC1V2_FPGA - IO_L2N_T0L_N3_46
# set_property PACKAGE_PIN H39      [get_ports "RLD3_C3_72B_DQ0"] ;# Bank  46 VCCO - VCC1V2_FPGA - IO_L2P_T0L_N2_46
# set_property IOSTANDARD  SSTL12 [get_ports "RLD3_C3_72B_DQ0"] ;# Bank  46 VCCO - VCC1V2_FPGA - IO_L2P_T0L_N2_46
# set_property PACKAGE_PIN J40      [get_ports "RLD3_C3_72B_QK0_N"] ;# Bank  46 VCCO - VCC1V2_FPGA - IO_L1N_T0L_N1_DBC_46
# set_property IOSTANDARD  DIFF_SSTL12 [get_ports "RLD3_C3_72B_QK0_N"] ;# Bank  46 VCCO - VCC1V2_FPGA - IO_L1N_T0L_N1_DBC_46
# set_property PACKAGE_PIN J39      [get_ports "RLD3_C3_72B_QK0_P"] ;# Bank  46 VCCO - VCC1V2_FPGA - IO_L1P_T0L_N0_DBC_46
# set_property IOSTANDARD  DIFF_SSTL12 [get_ports "RLD3_C3_72B_QK0_P"] ;# Bank  46 VCCO - VCC1V2_FPGA - IO_L1P_T0L_N0_DBC_46
# #Other net   PACKAGE_PIN J34      -                  Bank  46 - VREF_46
# set_property PACKAGE_PIN L35      [get_ports "FMCP_HSPC_LA21_N"] ;# Bank  45 VCCO - VADJ_1V8_FPGA - IO_L24N_T3U_N11_45
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_LA21_N"] ;# Bank  45 VCCO - VADJ_1V8_FPGA - IO_L24N_T3U_N11_45
# set_property PACKAGE_PIN M35      [get_ports "FMCP_HSPC_LA21_P"] ;# Bank  45 VCCO - VADJ_1V8_FPGA - IO_L24P_T3U_N10_45
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_LA21_P"] ;# Bank  45 VCCO - VADJ_1V8_FPGA - IO_L24P_T3U_N10_45
# set_property PACKAGE_PIN M32      [get_ports "FMCP_HSPC_LA20_N"] ;# Bank  45 VCCO - VADJ_1V8_FPGA - IO_L23N_T3U_N9_45
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_LA20_N"] ;# Bank  45 VCCO - VADJ_1V8_FPGA - IO_L23N_T3U_N9_45
# set_property PACKAGE_PIN N32      [get_ports "FMCP_HSPC_LA20_P"] ;# Bank  45 VCCO - VADJ_1V8_FPGA - IO_L23P_T3U_N8_45
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_LA20_P"] ;# Bank  45 VCCO - VADJ_1V8_FPGA - IO_L23P_T3U_N8_45
# set_property PACKAGE_PIN M33      [get_ports "FMCP_HSPC_LA19_N"] ;# Bank  45 VCCO - VADJ_1V8_FPGA - IO_L22N_T3U_N7_DBC_AD0N_45
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_LA19_N"] ;# Bank  45 VCCO - VADJ_1V8_FPGA - IO_L22N_T3U_N7_DBC_AD0N_45
# set_property PACKAGE_PIN N33      [get_ports "FMCP_HSPC_LA19_P"] ;# Bank  45 VCCO - VADJ_1V8_FPGA - IO_L22P_T3U_N6_DBC_AD0P_45
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_LA19_P"] ;# Bank  45 VCCO - VADJ_1V8_FPGA - IO_L22P_T3U_N6_DBC_AD0P_45
# set_property PACKAGE_PIN K33      [get_ports "FMCP_HSPC_LA32_N"] ;# Bank  45 VCCO - VADJ_1V8_FPGA - IO_L21N_T3L_N5_AD8N_45
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_LA32_N"] ;# Bank  45 VCCO - VADJ_1V8_FPGA - IO_L21N_T3L_N5_AD8N_45
# set_property PACKAGE_PIN L33      [get_ports "FMCP_HSPC_LA32_P"] ;# Bank  45 VCCO - VADJ_1V8_FPGA - IO_L21P_T3L_N4_AD8P_45
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_LA32_P"] ;# Bank  45 VCCO - VADJ_1V8_FPGA - IO_L21P_T3L_N4_AD8P_45
# set_property PACKAGE_PIN N35      [get_ports "FMCP_HSPC_LA22_N"] ;# Bank  45 VCCO - VADJ_1V8_FPGA - IO_L20N_T3L_N3_AD1N_45
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_LA22_N"] ;# Bank  45 VCCO - VADJ_1V8_FPGA - IO_L20N_T3L_N3_AD1N_45
# set_property PACKAGE_PIN N34      [get_ports "FMCP_HSPC_LA22_P"] ;# Bank  45 VCCO - VADJ_1V8_FPGA - IO_L20P_T3L_N2_AD1P_45
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_LA22_P"] ;# Bank  45 VCCO - VADJ_1V8_FPGA - IO_L20P_T3L_N2_AD1P_45
# set_property PACKAGE_PIN K34      [get_ports "FMCP_HSPC_LA33_N"] ;# Bank  45 VCCO - VADJ_1V8_FPGA - IO_L19N_T3L_N1_DBC_AD9N_45
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_LA33_N"] ;# Bank  45 VCCO - VADJ_1V8_FPGA - IO_L19N_T3L_N1_DBC_AD9N_45
# set_property PACKAGE_PIN L34      [get_ports "FMCP_HSPC_LA33_P"] ;# Bank  45 VCCO - VADJ_1V8_FPGA - IO_L19P_T3L_N0_DBC_AD9P_45
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_LA33_P"] ;# Bank  45 VCCO - VADJ_1V8_FPGA - IO_L19P_T3L_N0_DBC_AD9P_45
# #set_property PACKAGE_PIN K36      [get_ports ""] ;# Bank  45 VCCO - VADJ_1V8_FPGA - IO_T3U_N12_45
# #set_property IOSTANDARD  LVCMOSxx [get_ports ""] ;# Bank  45 VCCO - VADJ_1V8_FPGA - IO_T3U_N12_45
# #set_property PACKAGE_PIN R36      [get_ports ""] ;# Bank  45 VCCO - VADJ_1V8_FPGA - IO_T2U_N12_45
# #set_property IOSTANDARD  LVCMOSxx [get_ports ""] ;# Bank  45 VCCO - VADJ_1V8_FPGA - IO_T2U_N12_45
# set_property PACKAGE_PIN M38      [get_ports "FMCP_HSPC_LA30_N"] ;# Bank  45 VCCO - VADJ_1V8_FPGA - IO_L18N_T2U_N11_AD2N_45
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_LA30_N"] ;# Bank  45 VCCO - VADJ_1V8_FPGA - IO_L18N_T2U_N11_AD2N_45
# set_property PACKAGE_PIN N38      [get_ports "FMCP_HSPC_LA30_P"] ;# Bank  45 VCCO - VADJ_1V8_FPGA - IO_L18P_T2U_N10_AD2P_45
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_LA30_P"] ;# Bank  45 VCCO - VADJ_1V8_FPGA - IO_L18P_T2U_N10_AD2P_45
# set_property PACKAGE_PIN L36      [get_ports "FMCP_HSPC_LA28_N"] ;# Bank  45 VCCO - VADJ_1V8_FPGA - IO_L17N_T2U_N9_AD10N_45
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_LA28_N"] ;# Bank  45 VCCO - VADJ_1V8_FPGA - IO_L17N_T2U_N9_AD10N_45
# set_property PACKAGE_PIN M36      [get_ports "FMCP_HSPC_LA28_P"] ;# Bank  45 VCCO - VADJ_1V8_FPGA - IO_L17P_T2U_N8_AD10P_45
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_LA28_P"] ;# Bank  45 VCCO - VADJ_1V8_FPGA - IO_L17P_T2U_N8_AD10P_45
# set_property PACKAGE_PIN N37      [get_ports "FMCP_HSPC_LA31_N"] ;# Bank  45 VCCO - VADJ_1V8_FPGA - IO_L16N_T2U_N7_QBC_AD3N_45
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_LA31_N"] ;# Bank  45 VCCO - VADJ_1V8_FPGA - IO_L16N_T2U_N7_QBC_AD3N_45
# set_property PACKAGE_PIN P37      [get_ports "FMCP_HSPC_LA31_P"] ;# Bank  45 VCCO - VADJ_1V8_FPGA - IO_L16P_T2U_N6_QBC_AD3P_45
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_LA31_P"] ;# Bank  45 VCCO - VADJ_1V8_FPGA - IO_L16P_T2U_N6_QBC_AD3P_45
# #set_property PACKAGE_PIN L38      [get_ports ""] ;# Bank  45 VCCO - VADJ_1V8_FPGA - IO_L15N_T2L_N5_AD11N_45
# #set_property IOSTANDARD  LVCMOSxx [get_ports ""] ;# Bank  45 VCCO - VADJ_1V8_FPGA - IO_L15N_T2L_N5_AD11N_45
# #set_property PACKAGE_PIN M37      [get_ports ""] ;# Bank  45 VCCO - VADJ_1V8_FPGA - IO_L15P_T2L_N4_AD11P_45
# #set_property IOSTANDARD  LVCMOSxx [get_ports ""] ;# Bank  45 VCCO - VADJ_1V8_FPGA - IO_L15P_T2L_N4_AD11P_45
# set_property PACKAGE_PIN P36      [get_ports "FMCP_HSPC_CLK1_M2C_N"] ;# Bank  45 VCCO - VADJ_1V8_FPGA - IO_L14N_T2L_N3_GC_45
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_CLK1_M2C_N"] ;# Bank  45 VCCO - VADJ_1V8_FPGA - IO_L14N_T2L_N3_GC_45
# set_property PACKAGE_PIN P35      [get_ports "FMCP_HSPC_CLK1_M2C_P"] ;# Bank  45 VCCO - VADJ_1V8_FPGA - IO_L14P_T2L_N2_GC_45
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_CLK1_M2C_P"] ;# Bank  45 VCCO - VADJ_1V8_FPGA - IO_L14P_T2L_N2_GC_45
# set_property PACKAGE_PIN P34      [get_ports "FMCP_HSPC_LA17_CC_N"] ;# Bank  45 VCCO - VADJ_1V8_FPGA - IO_L13N_T2L_N1_GC_QBC_45
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_LA17_CC_N"] ;# Bank  45 VCCO - VADJ_1V8_FPGA - IO_L13N_T2L_N1_GC_QBC_45
# set_property PACKAGE_PIN R34      [get_ports "FMCP_HSPC_LA17_CC_P"] ;# Bank  45 VCCO - VADJ_1V8_FPGA - IO_L13P_T2L_N0_GC_QBC_45
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_LA17_CC_P"] ;# Bank  45 VCCO - VADJ_1V8_FPGA - IO_L13P_T2L_N0_GC_QBC_45
# #set_property PACKAGE_PIN R33      [get_ports ""] ;# Bank  45 VCCO - VADJ_1V8_FPGA - IO_L12N_T1U_N11_GC_45
# #set_property IOSTANDARD  LVCMOSxx [get_ports ""] ;# Bank  45 VCCO - VADJ_1V8_FPGA - IO_L12N_T1U_N11_GC_45
# #set_property PACKAGE_PIN T33      [get_ports ""] ;# Bank  45 VCCO - VADJ_1V8_FPGA - IO_L12P_T1U_N10_GC_45
# #set_property IOSTANDARD  LVCMOSxx [get_ports ""] ;# Bank  45 VCCO - VADJ_1V8_FPGA - IO_L12P_T1U_N10_GC_45
# set_property PACKAGE_PIN P32      [get_ports "USER_SMA_CLOCK_N"] ;# Bank  45 VCCO - VADJ_1V8_FPGA - IO_L11N_T1U_N9_GC_45
# set_property IOSTANDARD  LVDS [get_ports "USER_SMA_CLOCK_N"] ;# Bank  45 VCCO - VADJ_1V8_FPGA - IO_L11N_T1U_N9_GC_45
# set_property PACKAGE_PIN R32      [get_ports "USER_SMA_CLOCK_P"] ;# Bank  45 VCCO - VADJ_1V8_FPGA - IO_L11P_T1U_N8_GC_45
# set_property IOSTANDARD  LVDS [get_ports "USER_SMA_CLOCK_P"] ;# Bank  45 VCCO - VADJ_1V8_FPGA - IO_L11P_T1U_N8_GC_45
# set_property PACKAGE_PIN P31      [get_ports "FMCP_HSPC_LA18_CC_N"] ;# Bank  45 VCCO - VADJ_1V8_FPGA - IO_L10N_T1U_N7_QBC_AD4N_45
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_LA18_CC_N"] ;# Bank  45 VCCO - VADJ_1V8_FPGA - IO_L10N_T1U_N7_QBC_AD4N_45
# set_property PACKAGE_PIN R31      [get_ports "FMCP_HSPC_LA18_CC_P"] ;# Bank  45 VCCO - VADJ_1V8_FPGA - IO_L10P_T1U_N6_QBC_AD4P_45
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_LA18_CC_P"] ;# Bank  45 VCCO - VADJ_1V8_FPGA - IO_L10P_T1U_N6_QBC_AD4P_45
# #set_property PACKAGE_PIN W31      [get_ports ""] ;# Bank  45 VCCO - VADJ_1V8_FPGA - IO_L9N_T1L_N5_AD12N_45
# #set_property IOSTANDARD  LVCMOSxx [get_ports ""] ;# Bank  45 VCCO - VADJ_1V8_FPGA - IO_L9N_T1L_N5_AD12N_45
# #set_property PACKAGE_PIN Y31      [get_ports ""] ;# Bank  45 VCCO - VADJ_1V8_FPGA - IO_L9P_T1L_N4_AD12P_45
# #set_property IOSTANDARD  LVCMOSxx [get_ports ""] ;# Bank  45 VCCO - VADJ_1V8_FPGA - IO_L9P_T1L_N4_AD12P_45
# #set_property PACKAGE_PIN U32      [get_ports ""] ;# Bank  45 VCCO - VADJ_1V8_FPGA - IO_L8N_T1L_N3_AD5N_45
# #set_property IOSTANDARD  LVCMOSxx [get_ports ""] ;# Bank  45 VCCO - VADJ_1V8_FPGA - IO_L8N_T1L_N3_AD5N_45
# #set_property PACKAGE_PIN U31      [get_ports ""] ;# Bank  45 VCCO - VADJ_1V8_FPGA - IO_L8P_T1L_N2_AD5P_45
# #set_property IOSTANDARD  LVCMOSxx [get_ports ""] ;# Bank  45 VCCO - VADJ_1V8_FPGA - IO_L8P_T1L_N2_AD5P_45
# #set_property PACKAGE_PIN T31      [get_ports ""] ;# Bank  45 VCCO - VADJ_1V8_FPGA - IO_L7N_T1L_N1_QBC_AD13N_45
# #set_property IOSTANDARD  LVCMOSxx [get_ports ""] ;# Bank  45 VCCO - VADJ_1V8_FPGA - IO_L7N_T1L_N1_QBC_AD13N_45
# #set_property PACKAGE_PIN T30      [get_ports ""] ;# Bank  45 VCCO - VADJ_1V8_FPGA - IO_L7P_T1L_N0_QBC_AD13P_45
# #set_property IOSTANDARD  LVCMOSxx [get_ports ""] ;# Bank  45 VCCO - VADJ_1V8_FPGA - IO_L7P_T1L_N0_QBC_AD13P_45
# #set_property PACKAGE_PIN V30      [get_ports ""] ;# Bank  45 VCCO - VADJ_1V8_FPGA - IO_T1U_N12_45
# #set_property IOSTANDARD  LVCMOSxx [get_ports ""] ;# Bank  45 VCCO - VADJ_1V8_FPGA - IO_T1U_N12_45
# #set_property PACKAGE_PIN Y33      [get_ports "VRP_45"] ;# Bank  45 VCCO - VADJ_1V8_FPGA - IO_T0U_N12_VRP_45
# #set_property IOSTANDARD  LVCMOSxx [get_ports "VRP_45"] ;# Bank  45 VCCO - VADJ_1V8_FPGA - IO_T0U_N12_VRP_45
# set_property PACKAGE_PIN T35      [get_ports "FMCP_HSPC_LA24_N"] ;# Bank  45 VCCO - VADJ_1V8_FPGA - IO_L6N_T0U_N11_AD6N_45
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_LA24_N"] ;# Bank  45 VCCO - VADJ_1V8_FPGA - IO_L6N_T0U_N11_AD6N_45
# set_property PACKAGE_PIN T34      [get_ports "FMCP_HSPC_LA24_P"] ;# Bank  45 VCCO - VADJ_1V8_FPGA - IO_L6P_T0U_N10_AD6P_45
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_LA24_P"] ;# Bank  45 VCCO - VADJ_1V8_FPGA - IO_L6P_T0U_N10_AD6P_45
# set_property PACKAGE_PIN V34      [get_ports "FMCP_HSPC_LA27_N"] ;# Bank  45 VCCO - VADJ_1V8_FPGA - IO_L5N_T0U_N9_AD14N_45
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_LA27_N"] ;# Bank  45 VCCO - VADJ_1V8_FPGA - IO_L5N_T0U_N9_AD14N_45
# set_property PACKAGE_PIN V33      [get_ports "FMCP_HSPC_LA27_P"] ;# Bank  45 VCCO - VADJ_1V8_FPGA - IO_L5P_T0U_N8_AD14P_45
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_LA27_P"] ;# Bank  45 VCCO - VADJ_1V8_FPGA - IO_L5P_T0U_N8_AD14P_45
# set_property PACKAGE_PIN T36      [get_ports "FMCP_HSPC_LA29_N"] ;# Bank  45 VCCO - VADJ_1V8_FPGA - IO_L4N_T0U_N7_DBC_AD7N_45
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_LA29_N"] ;# Bank  45 VCCO - VADJ_1V8_FPGA - IO_L4N_T0U_N7_DBC_AD7N_45
# set_property PACKAGE_PIN U35      [get_ports "FMCP_HSPC_LA29_P"] ;# Bank  45 VCCO - VADJ_1V8_FPGA - IO_L4P_T0U_N6_DBC_AD7P_45
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_LA29_P"] ;# Bank  45 VCCO - VADJ_1V8_FPGA - IO_L4P_T0U_N6_DBC_AD7P_45
# set_property PACKAGE_PIN W34      [get_ports "FMCP_HSPC_LA25_N"] ;# Bank  45 VCCO - VADJ_1V8_FPGA - IO_L3N_T0L_N5_AD15N_45
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_LA25_N"] ;# Bank  45 VCCO - VADJ_1V8_FPGA - IO_L3N_T0L_N5_AD15N_45
# set_property PACKAGE_PIN Y34      [get_ports "FMCP_HSPC_LA25_P"] ;# Bank  45 VCCO - VADJ_1V8_FPGA - IO_L3P_T0L_N4_AD15P_45
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_LA25_P"] ;# Bank  45 VCCO - VADJ_1V8_FPGA - IO_L3P_T0L_N4_AD15P_45
# set_property PACKAGE_PIN U33      [get_ports "FMCP_HSPC_LA26_N"] ;# Bank  45 VCCO - VADJ_1V8_FPGA - IO_L2N_T0L_N3_45
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_LA26_N"] ;# Bank  45 VCCO - VADJ_1V8_FPGA - IO_L2N_T0L_N3_45
# set_property PACKAGE_PIN V32      [get_ports "FMCP_HSPC_LA26_P"] ;# Bank  45 VCCO - VADJ_1V8_FPGA - IO_L2P_T0L_N2_45
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_LA26_P"] ;# Bank  45 VCCO - VADJ_1V8_FPGA - IO_L2P_T0L_N2_45
# set_property PACKAGE_PIN W32      [get_ports "FMCP_HSPC_LA23_N"] ;# Bank  45 VCCO - VADJ_1V8_FPGA - IO_L1N_T0L_N1_DBC_45
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_LA23_N"] ;# Bank  45 VCCO - VADJ_1V8_FPGA - IO_L1N_T0L_N1_DBC_45
# set_property PACKAGE_PIN Y32      [get_ports "FMCP_HSPC_LA23_P"] ;# Bank  45 VCCO - VADJ_1V8_FPGA - IO_L1P_T0L_N0_DBC_45
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_LA23_P"] ;# Bank  45 VCCO - VADJ_1V8_FPGA - IO_L1P_T0L_N0_DBC_45
# #Other net   PACKAGE_PIN U30      - VREF_45                   Bank  45 - VREF_45
# set_property PACKAGE_PIN AK13     [get_ports "FMC_HPC1_LA33_N"] ;# Bank  67 VCCO - VADJ_1V8_FPGA - IO_L24N_T3U_N11_67
# set_property IOSTANDARD  LVDS [get_ports "FMC_HPC1_LA33_N"] ;# Bank  67 VCCO - VADJ_1V8_FPGA - IO_L24N_T3U_N11_67
# set_property PACKAGE_PIN AK14     [get_ports "FMC_HPC1_LA33_P"] ;# Bank  67 VCCO - VADJ_1V8_FPGA - IO_L24P_T3U_N10_67
# set_property IOSTANDARD  LVDS [get_ports "FMC_HPC1_LA33_P"] ;# Bank  67 VCCO - VADJ_1V8_FPGA - IO_L24P_T3U_N10_67
# set_property PACKAGE_PIN AM12     [get_ports "FMC_HPC1_LA31_N"] ;# Bank  67 VCCO - VADJ_1V8_FPGA - IO_L23N_T3U_N9_67
# set_property IOSTANDARD  LVDS [get_ports "FMC_HPC1_LA31_N"] ;# Bank  67 VCCO - VADJ_1V8_FPGA - IO_L23N_T3U_N9_67
# set_property PACKAGE_PIN AM13     [get_ports "FMC_HPC1_LA31_P"] ;# Bank  67 VCCO - VADJ_1V8_FPGA - IO_L23P_T3U_N8_67
# set_property IOSTANDARD  LVDS [get_ports "FMC_HPC1_LA31_P"] ;# Bank  67 VCCO - VADJ_1V8_FPGA - IO_L23P_T3U_N8_67
# set_property PACKAGE_PIN AJ12     [get_ports "FMC_HPC1_LA32_N"] ;# Bank  67 VCCO - VADJ_1V8_FPGA - IO_L22N_T3U_N7_DBC_AD0N_67
# set_property IOSTANDARD  LVDS [get_ports "FMC_HPC1_LA32_N"] ;# Bank  67 VCCO - VADJ_1V8_FPGA - IO_L22N_T3U_N7_DBC_AD0N_67
# set_property PACKAGE_PIN AJ13     [get_ports "FMC_HPC1_LA32_P"] ;# Bank  67 VCCO - VADJ_1V8_FPGA - IO_L22P_T3U_N6_DBC_AD0P_67
# set_property IOSTANDARD  LVDS [get_ports "FMC_HPC1_LA32_P"] ;# Bank  67 VCCO - VADJ_1V8_FPGA - IO_L22P_T3U_N6_DBC_AD0P_67
# set_property PACKAGE_PIN AL12     [get_ports "FMC_HPC1_LA30_N"] ;# Bank  67 VCCO - VADJ_1V8_FPGA - IO_L21N_T3L_N5_AD8N_67
# set_property IOSTANDARD  LVDS [get_ports "FMC_HPC1_LA30_N"] ;# Bank  67 VCCO - VADJ_1V8_FPGA - IO_L21N_T3L_N5_AD8N_67
# set_property PACKAGE_PIN AK12     [get_ports "FMC_HPC1_LA30_P"] ;# Bank  67 VCCO - VADJ_1V8_FPGA - IO_L21P_T3L_N4_AD8P_67
# set_property IOSTANDARD  LVDS [get_ports "FMC_HPC1_LA30_P"] ;# Bank  67 VCCO - VADJ_1V8_FPGA - IO_L21P_T3L_N4_AD8P_67
# set_property PACKAGE_PIN AL15     [get_ports "FMC_HPC1_LA26_N"] ;# Bank  67 VCCO - VADJ_1V8_FPGA - IO_L20N_T3L_N3_AD1N_67
# set_property IOSTANDARD  LVDS [get_ports "FMC_HPC1_LA26_N"] ;# Bank  67 VCCO - VADJ_1V8_FPGA - IO_L20N_T3L_N3_AD1N_67
# set_property PACKAGE_PIN AK15     [get_ports "FMC_HPC1_LA26_P"] ;# Bank  67 VCCO - VADJ_1V8_FPGA - IO_L20P_T3L_N2_AD1P_67
# set_property IOSTANDARD  LVDS [get_ports "FMC_HPC1_LA26_P"] ;# Bank  67 VCCO - VADJ_1V8_FPGA - IO_L20P_T3L_N2_AD1P_67
# set_property PACKAGE_PIN AM14     [get_ports "FMC_HPC1_LA27_N"] ;# Bank  67 VCCO - VADJ_1V8_FPGA - IO_L19N_T3L_N1_DBC_AD9N_67
# set_property IOSTANDARD  LVDS [get_ports "FMC_HPC1_LA27_N"] ;# Bank  67 VCCO - VADJ_1V8_FPGA - IO_L19N_T3L_N1_DBC_AD9N_67
# set_property PACKAGE_PIN AL14     [get_ports "FMC_HPC1_LA27_P"] ;# Bank  67 VCCO - VADJ_1V8_FPGA - IO_L19P_T3L_N0_DBC_AD9P_67
# set_property IOSTANDARD  LVDS [get_ports "FMC_HPC1_LA27_P"] ;# Bank  67 VCCO - VADJ_1V8_FPGA - IO_L19P_T3L_N0_DBC_AD9P_67
# #set_property PACKAGE_PIN AM16     [get_ports ""] ;# Bank  67 VCCO - VADJ_1V8_FPGA - IO_T3U_N12_67
# #set_property IOSTANDARD  LVCMOSxx [get_ports ""] ;# Bank  67 VCCO - VADJ_1V8_FPGA - IO_T3U_N12_67
# #set_property PACKAGE_PIN AR15     [get_ports ""] ;# Bank  67 VCCO - VADJ_1V8_FPGA - IO_T2U_N12_67
# #set_property IOSTANDARD  LVCMOSxx [get_ports ""] ;# Bank  67 VCCO - VADJ_1V8_FPGA - IO_T2U_N12_67
# set_property PACKAGE_PIN AP15     [get_ports "FMC_HPC1_LA29_N"] ;# Bank  67 VCCO - VADJ_1V8_FPGA - IO_L18N_T2U_N11_AD2N_67
# set_property IOSTANDARD  LVDS [get_ports "FMC_HPC1_LA29_N"] ;# Bank  67 VCCO - VADJ_1V8_FPGA - IO_L18N_T2U_N11_AD2N_67
# set_property PACKAGE_PIN AN15     [get_ports "FMC_HPC1_LA29_P"] ;# Bank  67 VCCO - VADJ_1V8_FPGA - IO_L18P_T2U_N10_AD2P_67
# set_property IOSTANDARD  LVDS [get_ports "FMC_HPC1_LA29_P"] ;# Bank  67 VCCO - VADJ_1V8_FPGA - IO_L18P_T2U_N10_AD2P_67
# set_property PACKAGE_PIN AP16     [get_ports "FMC_HPC1_LA23_N"] ;# Bank  67 VCCO - VADJ_1V8_FPGA - IO_L17N_T2U_N9_AD10N_67
# set_property IOSTANDARD  LVDS [get_ports "FMC_HPC1_LA23_N"] ;# Bank  67 VCCO - VADJ_1V8_FPGA - IO_L17N_T2U_N9_AD10N_67
# set_property PACKAGE_PIN AN16     [get_ports "FMC_HPC1_LA23_P"] ;# Bank  67 VCCO - VADJ_1V8_FPGA - IO_L17P_T2U_N8_AD10P_67
# set_property IOSTANDARD  LVDS [get_ports "FMC_HPC1_LA23_P"] ;# Bank  67 VCCO - VADJ_1V8_FPGA - IO_L17P_T2U_N8_AD10P_67
# set_property PACKAGE_PIN AR12     [get_ports "FMC_HPC1_LA18_CC_N"] ;# Bank  67 VCCO - VADJ_1V8_FPGA - IO_L16N_T2U_N7_QBC_AD3N_67
# set_property IOSTANDARD  LVDS [get_ports "FMC_HPC1_LA18_CC_N"] ;# Bank  67 VCCO - VADJ_1V8_FPGA - IO_L16N_T2U_N7_QBC_AD3N_67
# set_property PACKAGE_PIN AP12     [get_ports "FMC_HPC1_LA18_CC_P"] ;# Bank  67 VCCO - VADJ_1V8_FPGA - IO_L16P_T2U_N6_QBC_AD3P_67
# set_property IOSTANDARD  LVDS [get_ports "FMC_HPC1_LA18_CC_P"] ;# Bank  67 VCCO - VADJ_1V8_FPGA - IO_L16P_T2U_N6_QBC_AD3P_67
# #set_property PACKAGE_PIN AN13     [get_ports ""] ;# Bank  67 VCCO - VADJ_1V8_FPGA - IO_L15N_T2L_N5_AD11N_67
# #set_property IOSTANDARD  LVCMOSxx [get_ports ""] ;# Bank  67 VCCO - VADJ_1V8_FPGA - IO_L15N_T2L_N5_AD11N_67
# #set_property PACKAGE_PIN AN14     [get_ports ""] ;# Bank  67 VCCO - VADJ_1V8_FPGA - IO_L15P_T2L_N4_AD11P_67
# #set_property IOSTANDARD  LVCMOSxx [get_ports ""] ;# Bank  67 VCCO - VADJ_1V8_FPGA - IO_L15P_T2L_N4_AD11P_67
# set_property PACKAGE_PIN AR13     [get_ports "FMC_HPC1_LA24_N"] ;# Bank  67 VCCO - VADJ_1V8_FPGA - IO_L14N_T2L_N3_GC_67
# set_property IOSTANDARD  LVDS [get_ports "FMC_HPC1_LA24_N"] ;# Bank  67 VCCO - VADJ_1V8_FPGA - IO_L14N_T2L_N3_GC_67
# set_property PACKAGE_PIN AP13     [get_ports "FMC_HPC1_LA24_P"] ;# Bank  67 VCCO - VADJ_1V8_FPGA - IO_L14P_T2L_N2_GC_67
# set_property IOSTANDARD  LVDS [get_ports "FMC_HPC1_LA24_P"] ;# Bank  67 VCCO - VADJ_1V8_FPGA - IO_L14P_T2L_N2_GC_67
# set_property PACKAGE_PIN AT14     [get_ports "FMC_HPC1_LA17_CC_N"] ;# Bank  67 VCCO - VADJ_1V8_FPGA - IO_L13N_T2L_N1_GC_QBC_67
# set_property IOSTANDARD  LVDS [get_ports "FMC_HPC1_LA17_CC_N"] ;# Bank  67 VCCO - VADJ_1V8_FPGA - IO_L13N_T2L_N1_GC_QBC_67
# set_property PACKAGE_PIN AR14     [get_ports "FMC_HPC1_LA17_CC_P"] ;# Bank  67 VCCO - VADJ_1V8_FPGA - IO_L13P_T2L_N0_GC_QBC_67
# set_property IOSTANDARD  LVDS [get_ports "FMC_HPC1_LA17_CC_P"] ;# Bank  67 VCCO - VADJ_1V8_FPGA - IO_L13P_T2L_N0_GC_QBC_67
# set_property PACKAGE_PIN AV13     [get_ports "FMC_HPC1_CLK1_M2C_N"] ;# Bank  67 VCCO - VADJ_1V8_FPGA - IO_L12N_T1U_N11_GC_67
# set_property IOSTANDARD  LVDS [get_ports "FMC_HPC1_CLK1_M2C_N"] ;# Bank  67 VCCO - VADJ_1V8_FPGA - IO_L12N_T1U_N11_GC_67
# set_property PACKAGE_PIN AV14     [get_ports "FMC_HPC1_CLK1_M2C_P"] ;# Bank  67 VCCO - VADJ_1V8_FPGA - IO_L12P_T1U_N10_GC_67
# set_property IOSTANDARD  LVDS [get_ports "FMC_HPC1_CLK1_M2C_P"] ;# Bank  67 VCCO - VADJ_1V8_FPGA - IO_L12P_T1U_N10_GC_67
# #set_property PACKAGE_PIN AU13     [get_ports ""] ;# Bank  67 VCCO - VADJ_1V8_FPGA - IO_L11N_T1U_N9_GC_67
# #set_property IOSTANDARD  LVCMOSxx [get_ports ""] ;# Bank  67 VCCO - VADJ_1V8_FPGA - IO_L11N_T1U_N9_GC_67
# #set_property PACKAGE_PIN AU14     [get_ports ""] ;# Bank  67 VCCO - VADJ_1V8_FPGA - IO_L11P_T1U_N8_GC_67
# #set_property IOSTANDARD  LVCMOSxx [get_ports ""] ;# Bank  67 VCCO - VADJ_1V8_FPGA - IO_L11P_T1U_N8_GC_67
# set_property PACKAGE_PIN AY14     [get_ports "PMOD0_0_LS"] ;# Bank  67 VCCO - VADJ_1V8_FPGA - IO_L10N_T1U_N7_QBC_AD4N_67
# set_property IOSTANDARD  LVCMOS18 [get_ports "PMOD0_0_LS"] ;# Bank  67 VCCO - VADJ_1V8_FPGA - IO_L10N_T1U_N7_QBC_AD4N_67
# set_property PACKAGE_PIN AY15     [get_ports "PMOD0_1_LS"] ;# Bank  67 VCCO - VADJ_1V8_FPGA - IO_L10P_T1U_N6_QBC_AD4P_67
# set_property IOSTANDARD  LVCMOS18 [get_ports "PMOD0_1_LS"] ;# Bank  67 VCCO - VADJ_1V8_FPGA - IO_L10P_T1U_N6_QBC_AD4P_67
# set_property PACKAGE_PIN AW15     [get_ports "PMOD0_2_LS"] ;# Bank  67 VCCO - VADJ_1V8_FPGA - IO_L9N_T1L_N5_AD12N_67
# set_property IOSTANDARD  LVCMOS18 [get_ports "PMOD0_2_LS"] ;# Bank  67 VCCO - VADJ_1V8_FPGA - IO_L9N_T1L_N5_AD12N_67
# set_property PACKAGE_PIN AV15     [get_ports "PMOD0_3_LS"] ;# Bank  67 VCCO - VADJ_1V8_FPGA - IO_L9P_T1L_N4_AD12P_67
# set_property IOSTANDARD  LVCMOS18 [get_ports "PMOD0_3_LS"] ;# Bank  67 VCCO - VADJ_1V8_FPGA - IO_L9P_T1L_N4_AD12P_67
# set_property PACKAGE_PIN AV16     [get_ports "PMOD0_4_LS"] ;# Bank  67 VCCO - VADJ_1V8_FPGA - IO_L8N_T1L_N3_AD5N_67
# set_property IOSTANDARD  LVCMOS18 [get_ports "PMOD0_4_LS"] ;# Bank  67 VCCO - VADJ_1V8_FPGA - IO_L8N_T1L_N3_AD5N_67
# set_property PACKAGE_PIN AU16     [get_ports "PMOD0_5_LS"] ;# Bank  67 VCCO - VADJ_1V8_FPGA - IO_L8P_T1L_N2_AD5P_67
# set_property IOSTANDARD  LVCMOS18 [get_ports "PMOD0_5_LS"] ;# Bank  67 VCCO - VADJ_1V8_FPGA - IO_L8P_T1L_N2_AD5P_67
# set_property PACKAGE_PIN AT15     [get_ports "PMOD0_6_LS"] ;# Bank  67 VCCO - VADJ_1V8_FPGA - IO_L7N_T1L_N1_QBC_AD13N_67
# set_property IOSTANDARD  LVCMOS18 [get_ports "PMOD0_6_LS"] ;# Bank  67 VCCO - VADJ_1V8_FPGA - IO_L7N_T1L_N1_QBC_AD13N_67
# set_property PACKAGE_PIN AT16     [get_ports "PMOD0_7_LS"] ;# Bank  67 VCCO - VADJ_1V8_FPGA - IO_L7P_T1L_N0_QBC_AD13P_67
# set_property IOSTANDARD  LVCMOS18 [get_ports "PMOD0_7_LS"] ;# Bank  67 VCCO - VADJ_1V8_FPGA - IO_L7P_T1L_N0_QBC_AD13P_67
# set_property PACKAGE_PIN AW16     [get_ports "10N8842"] ;# Bank  67 VCCO - VADJ_1V8_FPGA - IO_T1U_N12_67
# set_property IOSTANDARD  LVCMOSxx [get_ports "10N8842"] ;# Bank  67 VCCO - VADJ_1V8_FPGA - IO_T1U_N12_67
# #set_property PACKAGE_PIN BA12     [get_ports "VRP_67"] ;# Bank  67 VCCO - VADJ_1V8_FPGA - IO_T0U_N12_VRP_67
# #set_property IOSTANDARD  LVCMOSxx [get_ports "VRP_67"] ;# Bank  67 VCCO - VADJ_1V8_FPGA - IO_T0U_N12_VRP_67
# set_property PACKAGE_PIN AV11     [get_ports "FMC_HPC1_LA21_N"] ;# Bank  67 VCCO - VADJ_1V8_FPGA - IO_L6N_T0U_N11_AD6N_67
# set_property IOSTANDARD  LVDS [get_ports "FMC_HPC1_LA21_N"] ;# Bank  67 VCCO - VADJ_1V8_FPGA - IO_L6N_T0U_N11_AD6N_67
# set_property PACKAGE_PIN AU11     [get_ports "FMC_HPC1_LA21_P"] ;# Bank  67 VCCO - VADJ_1V8_FPGA - IO_L6P_T0U_N10_AD6P_67
# set_property IOSTANDARD  LVDS [get_ports "FMC_HPC1_LA21_P"] ;# Bank  67 VCCO - VADJ_1V8_FPGA - IO_L6P_T0U_N10_AD6P_67
# set_property PACKAGE_PIN AY13     [get_ports "FMC_HPC1_LA22_N"] ;# Bank  67 VCCO - VADJ_1V8_FPGA - IO_L5N_T0U_N9_AD14N_67
# set_property IOSTANDARD  LVDS [get_ports "FMC_HPC1_LA22_N"] ;# Bank  67 VCCO - VADJ_1V8_FPGA - IO_L5N_T0U_N9_AD14N_67
# set_property PACKAGE_PIN AW13     [get_ports "FMC_HPC1_LA22_P"] ;# Bank  67 VCCO - VADJ_1V8_FPGA - IO_L5P_T0U_N8_AD14P_67
# set_property IOSTANDARD  LVDS [get_ports "FMC_HPC1_LA22_P"] ;# Bank  67 VCCO - VADJ_1V8_FPGA - IO_L5P_T0U_N8_AD14P_67
# set_property PACKAGE_PIN AW10     [get_ports "FMC_HPC1_LA28_N"] ;# Bank  67 VCCO - VADJ_1V8_FPGA - IO_L4N_T0U_N7_DBC_AD7N_67
# set_property IOSTANDARD  LVDS [get_ports "FMC_HPC1_LA28_N"] ;# Bank  67 VCCO - VADJ_1V8_FPGA - IO_L4N_T0U_N7_DBC_AD7N_67
# set_property PACKAGE_PIN AV10     [get_ports "FMC_HPC1_LA28_P"] ;# Bank  67 VCCO - VADJ_1V8_FPGA - IO_L4P_T0U_N6_DBC_AD7P_67
# set_property IOSTANDARD  LVDS [get_ports "FMC_HPC1_LA28_P"] ;# Bank  67 VCCO - VADJ_1V8_FPGA - IO_L4P_T0U_N6_DBC_AD7P_67
# set_property PACKAGE_PIN AY10     [get_ports "FMC_HPC1_LA20_N"] ;# Bank  67 VCCO - VADJ_1V8_FPGA - IO_L3N_T0L_N5_AD15N_67
# set_property IOSTANDARD  LVDS [get_ports "FMC_HPC1_LA20_N"] ;# Bank  67 VCCO - VADJ_1V8_FPGA - IO_L3N_T0L_N5_AD15N_67
# set_property PACKAGE_PIN AW11     [get_ports "FMC_HPC1_LA20_P"] ;# Bank  67 VCCO - VADJ_1V8_FPGA - IO_L3P_T0L_N4_AD15P_67
# set_property IOSTANDARD  LVDS [get_ports "FMC_HPC1_LA20_P"] ;# Bank  67 VCCO - VADJ_1V8_FPGA - IO_L3P_T0L_N4_AD15P_67
# set_property PACKAGE_PIN AY12     [get_ports "FMC_HPC1_LA19_N"] ;# Bank  67 VCCO - VADJ_1V8_FPGA - IO_L2N_T0L_N3_67
# set_property IOSTANDARD  LVDS [get_ports "FMC_HPC1_LA19_N"] ;# Bank  67 VCCO - VADJ_1V8_FPGA - IO_L2N_T0L_N3_67
# set_property PACKAGE_PIN AW12     [get_ports "FMC_HPC1_LA19_P"] ;# Bank  67 VCCO - VADJ_1V8_FPGA - IO_L2P_T0L_N2_67
# set_property IOSTANDARD  LVDS [get_ports "FMC_HPC1_LA19_P"] ;# Bank  67 VCCO - VADJ_1V8_FPGA - IO_L2P_T0L_N2_67
# set_property PACKAGE_PIN AU12     [get_ports "FMC_HPC1_LA25_N"] ;# Bank  67 VCCO - VADJ_1V8_FPGA - IO_L1N_T0L_N1_DBC_67
# set_property IOSTANDARD  LVDS [get_ports "FMC_HPC1_LA25_N"] ;# Bank  67 VCCO - VADJ_1V8_FPGA - IO_L1N_T0L_N1_DBC_67
# set_property PACKAGE_PIN AT12     [get_ports "FMC_HPC1_LA25_P"] ;# Bank  67 VCCO - VADJ_1V8_FPGA - IO_L1P_T0L_N0_DBC_67
# set_property IOSTANDARD  LVDS [get_ports "FMC_HPC1_LA25_P"] ;# Bank  67 VCCO - VADJ_1V8_FPGA - IO_L1P_T0L_N0_DBC_67
# #Other net   PACKAGE_PIN AL16     - VREF_67                   Bank  67 - VREF_67
# set_property PACKAGE_PIN BB12     [get_ports "FMC_HPC1_LA10_N"] ;# Bank  66 VCCO - VADJ_1V8_FPGA - IO_L24N_T3U_N11_66
# set_property IOSTANDARD  LVDS [get_ports "FMC_HPC1_LA10_N"] ;# Bank  66 VCCO - VADJ_1V8_FPGA - IO_L24N_T3U_N11_66
# set_property PACKAGE_PIN BB13     [get_ports "FMC_HPC1_LA10_P"] ;# Bank  66 VCCO - VADJ_1V8_FPGA - IO_L24P_T3U_N10_66
# set_property IOSTANDARD  LVDS [get_ports "FMC_HPC1_LA10_P"] ;# Bank  66 VCCO - VADJ_1V8_FPGA - IO_L24P_T3U_N10_66
# set_property PACKAGE_PIN BB14     [get_ports "FMC_HPC1_LA09_N"] ;# Bank  66 VCCO - VADJ_1V8_FPGA - IO_L23N_T3U_N9_66
# set_property IOSTANDARD  LVDS [get_ports "FMC_HPC1_LA09_N"] ;# Bank  66 VCCO - VADJ_1V8_FPGA - IO_L23N_T3U_N9_66
# set_property PACKAGE_PIN BA14     [get_ports "FMC_HPC1_LA09_P"] ;# Bank  66 VCCO - VADJ_1V8_FPGA - IO_L23P_T3U_N8_66
# set_property IOSTANDARD  LVDS [get_ports "FMC_HPC1_LA09_P"] ;# Bank  66 VCCO - VADJ_1V8_FPGA - IO_L23P_T3U_N8_66
# set_property PACKAGE_PIN BA15     [get_ports "FMC_HPC1_LA11_N"] ;# Bank  66 VCCO - VADJ_1V8_FPGA - IO_L22N_T3U_N7_DBC_AD0N_66
# set_property IOSTANDARD  LVDS [get_ports "FMC_HPC1_LA11_N"] ;# Bank  66 VCCO - VADJ_1V8_FPGA - IO_L22N_T3U_N7_DBC_AD0N_66
# set_property PACKAGE_PIN BA16     [get_ports "FMC_HPC1_LA11_P"] ;# Bank  66 VCCO - VADJ_1V8_FPGA - IO_L22P_T3U_N6_DBC_AD0P_66
# set_property IOSTANDARD  LVDS [get_ports "FMC_HPC1_LA11_P"] ;# Bank  66 VCCO - VADJ_1V8_FPGA - IO_L22P_T3U_N6_DBC_AD0P_66
# set_property PACKAGE_PIN BD15     [get_ports "FMC_HPC1_LA07_N"] ;# Bank  66 VCCO - VADJ_1V8_FPGA - IO_L21N_T3L_N5_AD8N_66
# set_property IOSTANDARD  LVDS [get_ports "FMC_HPC1_LA07_N"] ;# Bank  66 VCCO - VADJ_1V8_FPGA - IO_L21N_T3L_N5_AD8N_66
# set_property PACKAGE_PIN BC15     [get_ports "FMC_HPC1_LA07_P"] ;# Bank  66 VCCO - VADJ_1V8_FPGA - IO_L21P_T3L_N4_AD8P_66
# set_property IOSTANDARD  LVDS [get_ports "FMC_HPC1_LA07_P"] ;# Bank  66 VCCO - VADJ_1V8_FPGA - IO_L21P_T3L_N4_AD8P_66
# set_property PACKAGE_PIN BC16     [get_ports "FMC_HPC1_LA15_N"] ;# Bank  66 VCCO - VADJ_1V8_FPGA - IO_L20N_T3L_N3_AD1N_66
# set_property IOSTANDARD  LVDS [get_ports "FMC_HPC1_LA15_N"] ;# Bank  66 VCCO - VADJ_1V8_FPGA - IO_L20N_T3L_N3_AD1N_66
# set_property PACKAGE_PIN BB16     [get_ports "FMC_HPC1_LA15_P"] ;# Bank  66 VCCO - VADJ_1V8_FPGA - IO_L20P_T3L_N2_AD1P_66
# set_property IOSTANDARD  LVDS [get_ports "FMC_HPC1_LA15_P"] ;# Bank  66 VCCO - VADJ_1V8_FPGA - IO_L20P_T3L_N2_AD1P_66
# set_property PACKAGE_PIN BC13     [get_ports "FMC_HPC1_LA12_N"] ;# Bank  66 VCCO - VADJ_1V8_FPGA - IO_L19N_T3L_N1_DBC_AD9N_66
# set_property IOSTANDARD  LVDS [get_ports "FMC_HPC1_LA12_N"] ;# Bank  66 VCCO - VADJ_1V8_FPGA - IO_L19N_T3L_N1_DBC_AD9N_66
# set_property PACKAGE_PIN BC14     [get_ports "FMC_HPC1_LA12_P"] ;# Bank  66 VCCO - VADJ_1V8_FPGA - IO_L19P_T3L_N0_DBC_AD9P_66
# set_property IOSTANDARD  LVDS [get_ports "FMC_HPC1_LA12_P"] ;# Bank  66 VCCO - VADJ_1V8_FPGA - IO_L19P_T3L_N0_DBC_AD9P_66
# set_property PACKAGE_PIN BB11     [get_ports "10N8224"] ;# Bank  66 VCCO - VADJ_1V8_FPGA - IO_T3U_N12_66
# set_property IOSTANDARD  LVCMOSxx [get_ports "10N8224"] ;# Bank  66 VCCO - VADJ_1V8_FPGA - IO_T3U_N12_66
# set_property PACKAGE_PIN BA10     [get_ports "10N9644"] ;# Bank  66 VCCO - VADJ_1V8_FPGA - IO_T2U_N12_66
# set_property IOSTANDARD  LVCMOSxx [get_ports "10N9644"] ;# Bank  66 VCCO - VADJ_1V8_FPGA - IO_T2U_N12_66
# set_property PACKAGE_PIN AW7      [get_ports "FMC_HPC1_LA14_N"] ;# Bank  66 VCCO - VADJ_1V8_FPGA - IO_L18N_T2U_N11_AD2N_66
# set_property IOSTANDARD  LVDS [get_ports "FMC_HPC1_LA14_N"] ;# Bank  66 VCCO - VADJ_1V8_FPGA - IO_L18N_T2U_N11_AD2N_66
# set_property PACKAGE_PIN AW8      [get_ports "FMC_HPC1_LA14_P"] ;# Bank  66 VCCO - VADJ_1V8_FPGA - IO_L18P_T2U_N10_AD2P_66
# set_property IOSTANDARD  LVDS [get_ports "FMC_HPC1_LA14_P"] ;# Bank  66 VCCO - VADJ_1V8_FPGA - IO_L18P_T2U_N10_AD2P_66
# set_property PACKAGE_PIN AY7      [get_ports "FMC_HPC1_LA13_N"] ;# Bank  66 VCCO - VADJ_1V8_FPGA - IO_L17N_T2U_N9_AD10N_66
# set_property IOSTANDARD  LVDS [get_ports "FMC_HPC1_LA13_N"] ;# Bank  66 VCCO - VADJ_1V8_FPGA - IO_L17N_T2U_N9_AD10N_66
# set_property PACKAGE_PIN AY8      [get_ports "FMC_HPC1_LA13_P"] ;# Bank  66 VCCO - VADJ_1V8_FPGA - IO_L17P_T2U_N8_AD10P_66
# set_property IOSTANDARD  LVDS [get_ports "FMC_HPC1_LA13_P"] ;# Bank  66 VCCO - VADJ_1V8_FPGA - IO_L17P_T2U_N8_AD10P_66
# set_property PACKAGE_PIN AV8      [get_ports "FMC_HPC1_LA16_N"] ;# Bank  66 VCCO - VADJ_1V8_FPGA - IO_L16N_T2U_N7_QBC_AD3N_66
# set_property IOSTANDARD  LVDS [get_ports "FMC_HPC1_LA16_N"] ;# Bank  66 VCCO - VADJ_1V8_FPGA - IO_L16N_T2U_N7_QBC_AD3N_66
# set_property PACKAGE_PIN AV9      [get_ports "FMC_HPC1_LA16_P"] ;# Bank  66 VCCO - VADJ_1V8_FPGA - IO_L16P_T2U_N6_QBC_AD3P_66
# set_property IOSTANDARD  LVDS [get_ports "FMC_HPC1_LA16_P"] ;# Bank  66 VCCO - VADJ_1V8_FPGA - IO_L16P_T2U_N6_QBC_AD3P_66
# set_property PACKAGE_PIN BB7      [get_ports "FMC_HPC1_PRSNT_M2C_B_LS"] ;# Bank  66 VCCO - VADJ_1V8_FPGA - IO_L15N_T2L_N5_AD11N_66
# set_property IOSTANDARD  LVCMOS18 [get_ports "FMC_HPC1_PRSNT_M2C_B_LS"] ;# Bank  66 VCCO - VADJ_1V8_FPGA - IO_L15N_T2L_N5_AD11N_66
# set_property PACKAGE_PIN BA7      [get_ports "FMC_HPC1_PG_M2C_LS"] ;# Bank  66 VCCO - VADJ_1V8_FPGA - IO_L15P_T2L_N4_AD11P_66
# set_property IOSTANDARD  LVCMOS18 [get_ports "FMC_HPC1_PG_M2C_LS"] ;# Bank  66 VCCO - VADJ_1V8_FPGA - IO_L15P_T2L_N4_AD11P_66
# #set_property PACKAGE_PIN BB8      [get_ports ""] ;# Bank  66 VCCO - VADJ_1V8_FPGA - IO_L14N_T2L_N3_GC_66
# #set_property IOSTANDARD  LVCMOSxx [get_ports ""] ;# Bank  66 VCCO - VADJ_1V8_FPGA - IO_L14N_T2L_N3_GC_66
# #set_property PACKAGE_PIN BB9      [get_ports ""] ;# Bank  66 VCCO - VADJ_1V8_FPGA - IO_L14P_T2L_N2_GC_66
# #set_property IOSTANDARD  LVCMOSxx [get_ports ""] ;# Bank  66 VCCO - VADJ_1V8_FPGA - IO_L14P_T2L_N2_GC_66
# set_property PACKAGE_PIN BA9      [get_ports "FMC_HPC1_LA00_CC_N"] ;# Bank  66 VCCO - VADJ_1V8_FPGA - IO_L13N_T2L_N1_GC_QBC_66
# set_property IOSTANDARD  LVDS [get_ports "FMC_HPC1_LA00_CC_N"] ;# Bank  66 VCCO - VADJ_1V8_FPGA - IO_L13N_T2L_N1_GC_QBC_66
# set_property PACKAGE_PIN AY9      [get_ports "FMC_HPC1_LA00_CC_P"] ;# Bank  66 VCCO - VADJ_1V8_FPGA - IO_L13P_T2L_N0_GC_QBC_66
# set_property IOSTANDARD  LVDS [get_ports "FMC_HPC1_LA00_CC_P"] ;# Bank  66 VCCO - VADJ_1V8_FPGA - IO_L13P_T2L_N0_GC_QBC_66
# set_property PACKAGE_PIN BC8      [get_ports "FMC_HPC1_CLK0_M2C_N"] ;# Bank  66 VCCO - VADJ_1V8_FPGA - IO_L12N_T1U_N11_GC_66
# set_property IOSTANDARD  LVDS [get_ports "FMC_HPC1_CLK0_M2C_N"] ;# Bank  66 VCCO - VADJ_1V8_FPGA - IO_L12N_T1U_N11_GC_66
# set_property PACKAGE_PIN BC9      [get_ports "FMC_HPC1_CLK0_M2C_P"] ;# Bank  66 VCCO - VADJ_1V8_FPGA - IO_L12P_T1U_N10_GC_66
# set_property IOSTANDARD  LVDS [get_ports "FMC_HPC1_CLK0_M2C_P"] ;# Bank  66 VCCO - VADJ_1V8_FPGA - IO_L12P_T1U_N10_GC_66
# #set_property PACKAGE_PIN BD10     [get_ports ""] ;# Bank  66 VCCO - VADJ_1V8_FPGA - IO_L11N_T1U_N9_GC_66
# #set_property IOSTANDARD  LVCMOSxx [get_ports ""] ;# Bank  66 VCCO - VADJ_1V8_FPGA - IO_L11N_T1U_N9_GC_66
# #set_property PACKAGE_PIN BC10     [get_ports ""] ;# Bank  66 VCCO - VADJ_1V8_FPGA - IO_L11P_T1U_N8_GC_66
# #set_property IOSTANDARD  LVCMOSxx [get_ports ""] ;# Bank  66 VCCO - VADJ_1V8_FPGA - IO_L11P_T1U_N8_GC_66
# set_property PACKAGE_PIN BF9      [get_ports "FMC_HPC1_LA01_CC_N"] ;# Bank  66 VCCO - VADJ_1V8_FPGA - IO_L10N_T1U_N7_QBC_AD4N_66
# set_property IOSTANDARD  LVDS [get_ports "FMC_HPC1_LA01_CC_N"] ;# Bank  66 VCCO - VADJ_1V8_FPGA - IO_L10N_T1U_N7_QBC_AD4N_66
# set_property PACKAGE_PIN BF10     [get_ports "FMC_HPC1_LA01_CC_P"] ;# Bank  66 VCCO - VADJ_1V8_FPGA - IO_L10P_T1U_N6_QBC_AD4P_66
# set_property IOSTANDARD  LVDS [get_ports "FMC_HPC1_LA01_CC_P"] ;# Bank  66 VCCO - VADJ_1V8_FPGA - IO_L10P_T1U_N6_QBC_AD4P_66
# #set_property PACKAGE_PIN BE9      [get_ports ""] ;# Bank  66 VCCO - VADJ_1V8_FPGA - IO_L9N_T1L_N5_AD12N_66
# #set_property IOSTANDARD  LVCMOSxx [get_ports ""] ;# Bank  66 VCCO - VADJ_1V8_FPGA - IO_L9N_T1L_N5_AD12N_66
# #set_property PACKAGE_PIN BE10     [get_ports ""] ;# Bank  66 VCCO - VADJ_1V8_FPGA - IO_L9P_T1L_N4_AD12P_66
# #set_property IOSTANDARD  LVCMOSxx [get_ports ""] ;# Bank  66 VCCO - VADJ_1V8_FPGA - IO_L9P_T1L_N4_AD12P_66
# #set_property PACKAGE_PIN BE7      [get_ports ""] ;# Bank  66 VCCO - VADJ_1V8_FPGA - IO_L8N_T1L_N3_AD5N_66
# #set_property IOSTANDARD  LVCMOSxx [get_ports ""] ;# Bank  66 VCCO - VADJ_1V8_FPGA - IO_L8N_T1L_N3_AD5N_66
# #set_property PACKAGE_PIN BE8      [get_ports ""] ;# Bank  66 VCCO - VADJ_1V8_FPGA - IO_L8P_T1L_N2_AD5P_66
# #set_property IOSTANDARD  LVCMOSxx [get_ports ""] ;# Bank  66 VCCO - VADJ_1V8_FPGA - IO_L8P_T1L_N2_AD5P_66
# #set_property PACKAGE_PIN BD7      [get_ports ""] ;# Bank  66 VCCO - VADJ_1V8_FPGA - IO_L7N_T1L_N1_QBC_AD13N_66
# #set_property IOSTANDARD  LVCMOSxx [get_ports ""] ;# Bank  66 VCCO - VADJ_1V8_FPGA - IO_L7N_T1L_N1_QBC_AD13N_66
# #set_property PACKAGE_PIN BD8      [get_ports ""] ;# Bank  66 VCCO - VADJ_1V8_FPGA - IO_L7P_T1L_N0_QBC_AD13P_66
# #set_property IOSTANDARD  LVCMOSxx [get_ports ""] ;# Bank  66 VCCO - VADJ_1V8_FPGA - IO_L7P_T1L_N0_QBC_AD13P_66
# #set_property PACKAGE_PIN BF7      [get_ports ""] ;# Bank  66 VCCO - VADJ_1V8_FPGA - IO_T1U_N12_66
# #set_property IOSTANDARD  LVCMOSxx [get_ports ""] ;# Bank  66 VCCO - VADJ_1V8_FPGA - IO_T1U_N12_66
# #set_property PACKAGE_PIN BD16     [get_ports "VRP_66"] ;# Bank  66 VCCO - VADJ_1V8_FPGA - IO_T0U_N12_VRP_66
# #set_property IOSTANDARD  LVCMOSxx [get_ports "VRP_66"] ;# Bank  66 VCCO - VADJ_1V8_FPGA - IO_T0U_N12_VRP_66
# set_property PACKAGE_PIN BF15     [get_ports "FMC_HPC1_LA08_N"] ;# Bank  66 VCCO - VADJ_1V8_FPGA - IO_L6N_T0U_N11_AD6N_66
# set_property IOSTANDARD  LVDS [get_ports "FMC_HPC1_LA08_N"] ;# Bank  66 VCCO - VADJ_1V8_FPGA - IO_L6N_T0U_N11_AD6N_66
# set_property PACKAGE_PIN BE15     [get_ports "FMC_HPC1_LA08_P"] ;# Bank  66 VCCO - VADJ_1V8_FPGA - IO_L6P_T0U_N10_AD6P_66
# set_property IOSTANDARD  LVDS [get_ports "FMC_HPC1_LA08_P"] ;# Bank  66 VCCO - VADJ_1V8_FPGA - IO_L6P_T0U_N10_AD6P_66
# set_property PACKAGE_PIN BF14     [get_ports "FMC_HPC1_LA05_N"] ;# Bank  66 VCCO - VADJ_1V8_FPGA - IO_L5N_T0U_N9_AD14N_66
# set_property IOSTANDARD  LVDS [get_ports "FMC_HPC1_LA05_N"] ;# Bank  66 VCCO - VADJ_1V8_FPGA - IO_L5N_T0U_N9_AD14N_66
# set_property PACKAGE_PIN BE14     [get_ports "FMC_HPC1_LA05_P"] ;# Bank  66 VCCO - VADJ_1V8_FPGA - IO_L5P_T0U_N8_AD14P_66
# set_property IOSTANDARD  LVDS [get_ports "FMC_HPC1_LA05_P"] ;# Bank  66 VCCO - VADJ_1V8_FPGA - IO_L5P_T0U_N8_AD14P_66
# set_property PACKAGE_PIN BE13     [get_ports "FMC_HPC1_LA06_N"] ;# Bank  66 VCCO - VADJ_1V8_FPGA - IO_L4N_T0U_N7_DBC_AD7N_66
# set_property IOSTANDARD  LVDS [get_ports "FMC_HPC1_LA06_N"] ;# Bank  66 VCCO - VADJ_1V8_FPGA - IO_L4N_T0U_N7_DBC_AD7N_66
# set_property PACKAGE_PIN BD13     [get_ports "FMC_HPC1_LA06_P"] ;# Bank  66 VCCO - VADJ_1V8_FPGA - IO_L4P_T0U_N6_DBC_AD7P_66
# set_property IOSTANDARD  LVDS [get_ports "FMC_HPC1_LA06_P"] ;# Bank  66 VCCO - VADJ_1V8_FPGA - IO_L4P_T0U_N6_DBC_AD7P_66
# set_property PACKAGE_PIN BD11     [get_ports "FMC_HPC1_LA02_N"] ;# Bank  66 VCCO - VADJ_1V8_FPGA - IO_L3N_T0L_N5_AD15N_66
# set_property IOSTANDARD  LVDS [get_ports "FMC_HPC1_LA02_N"] ;# Bank  66 VCCO - VADJ_1V8_FPGA - IO_L3N_T0L_N5_AD15N_66
# set_property PACKAGE_PIN BC11     [get_ports "FMC_HPC1_LA02_P"] ;# Bank  66 VCCO - VADJ_1V8_FPGA - IO_L3P_T0L_N4_AD15P_66
# set_property IOSTANDARD  LVDS [get_ports "FMC_HPC1_LA02_P"] ;# Bank  66 VCCO - VADJ_1V8_FPGA - IO_L3P_T0L_N4_AD15P_66
# set_property PACKAGE_PIN BF11     [get_ports "FMC_HPC1_LA04_N"] ;# Bank  66 VCCO - VADJ_1V8_FPGA - IO_L2N_T0L_N3_66
# set_property IOSTANDARD  LVDS [get_ports "FMC_HPC1_LA04_N"] ;# Bank  66 VCCO - VADJ_1V8_FPGA - IO_L2N_T0L_N3_66
# set_property PACKAGE_PIN BF12     [get_ports "FMC_HPC1_LA04_P"] ;# Bank  66 VCCO - VADJ_1V8_FPGA - IO_L2P_T0L_N2_66
# set_property IOSTANDARD  LVDS [get_ports "FMC_HPC1_LA04_P"] ;# Bank  66 VCCO - VADJ_1V8_FPGA - IO_L2P_T0L_N2_66
# set_property PACKAGE_PIN BE12     [get_ports "FMC_HPC1_LA03_N"] ;# Bank  66 VCCO - VADJ_1V8_FPGA - IO_L1N_T0L_N1_DBC_66
# set_property IOSTANDARD  LVDS [get_ports "FMC_HPC1_LA03_N"] ;# Bank  66 VCCO - VADJ_1V8_FPGA - IO_L1N_T0L_N1_DBC_66
# set_property PACKAGE_PIN BD12     [get_ports "FMC_HPC1_LA03_P"] ;# Bank  66 VCCO - VADJ_1V8_FPGA - IO_L1P_T0L_N0_DBC_66
# set_property IOSTANDARD  LVDS [get_ports "FMC_HPC1_LA03_P"] ;# Bank  66 VCCO - VADJ_1V8_FPGA - IO_L1P_T0L_N0_DBC_66
# #Other net   PACKAGE_PIN BA11     - VREF_66                   Bank  66 - VREF_66
# #set_property PACKAGE_PIN AL19     [get_ports ""] ;# Bank  65 VCCO - VCC1V8_FPGA - IO_L24N_T3U_N11_DOUT_CSO_B_65
# #set_property IOSTANDARD  LVCMOSxx [get_ports ""] ;# Bank  65 VCCO - VCC1V8_FPGA - IO_L24N_T3U_N11_DOUT_CSO_B_65
# set_property PACKAGE_PIN AL20     [get_ports "FPGA_EMCCLK"] ;# Bank  65 VCCO - VCC1V8_FPGA - IO_L24P_T3U_N10_EMCCLK_65
# set_property IOSTANDARD  LVCMOS18 [get_ports "FPGA_EMCCLK"] ;# Bank  65 VCCO - VCC1V8_FPGA - IO_L24P_T3U_N10_EMCCLK_65
# set_property PACKAGE_PIN AP17     [get_ports "SYSMON_SDA"] ;# Bank  65 VCCO - VCC1V8_FPGA - IO_L23N_T3U_N9_PERSTN1_I2C_SDA_65
# set_property IOSTANDARD  LVCMOS18 [get_ports "SYSMON_SDA"] ;# Bank  65 VCCO - VCC1V8_FPGA - IO_L23N_T3U_N9_PERSTN1_I2C_SDA_65
# set_property PACKAGE_PIN AP18     [get_ports "SYSMON_SCL"] ;# Bank  65 VCCO - VCC1V8_FPGA - IO_L23P_T3U_N8_I2C_SCLK_65
# set_property IOSTANDARD  LVCMOS18 [get_ports "SYSMON_SCL"] ;# Bank  65 VCCO - VCC1V8_FPGA - IO_L23P_T3U_N8_I2C_SCLK_65
# set_property PACKAGE_PIN AM18     [get_ports "QSPI1_DQ1"] ;# Bank  65 VCCO - VCC1V8_FPGA - IO_L22N_T3U_N7_DBC_AD0N_D05_65
# set_property IOSTANDARD  LVCMOS18 [get_ports "QSPI1_DQ1"] ;# Bank  65 VCCO - VCC1V8_FPGA - IO_L22N_T3U_N7_DBC_AD0N_D05_65
# set_property PACKAGE_PIN AM19     [get_ports "QSPI1_DQ0"] ;# Bank  65 VCCO - VCC1V8_FPGA - IO_L22P_T3U_N6_DBC_AD0P_D04_65
# set_property IOSTANDARD  LVCMOS18 [get_ports "QSPI1_DQ0"] ;# Bank  65 VCCO - VCC1V8_FPGA - IO_L22P_T3U_N6_DBC_AD0P_D04_65
# set_property PACKAGE_PIN AP20     [get_ports "QSPI1_DQ3"] ;# Bank  65 VCCO - VCC1V8_FPGA - IO_L21N_T3L_N5_AD8N_D07_65
# set_property IOSTANDARD  LVCMOS18 [get_ports "QSPI1_DQ3"] ;# Bank  65 VCCO - VCC1V8_FPGA - IO_L21N_T3L_N5_AD8N_D07_65
# set_property PACKAGE_PIN AN20     [get_ports "QSPI1_DQ2"] ;# Bank  65 VCCO - VCC1V8_FPGA - IO_L21P_T3L_N4_AD8P_D06_65
# set_property IOSTANDARD  LVCMOS18 [get_ports "QSPI1_DQ2"] ;# Bank  65 VCCO - VCC1V8_FPGA - IO_L21P_T3L_N4_AD8P_D06_65
# #set_property PACKAGE_PIN AN18     [get_ports ""] ;# Bank  65 VCCO - VCC1V8_FPGA - IO_L20N_T3L_N3_AD1N_D09_65
# #set_property IOSTANDARD  LVCMOSxx [get_ports ""] ;# Bank  65 VCCO - VCC1V8_FPGA - IO_L20N_T3L_N3_AD1N_D09_65
# #set_property PACKAGE_PIN AN19     [get_ports ""] ;# Bank  65 VCCO - VCC1V8_FPGA - IO_L20P_T3L_N2_AD1P_D08_65
# #set_property IOSTANDARD  LVCMOSxx [get_ports ""] ;# Bank  65 VCCO - VCC1V8_FPGA - IO_L20P_T3L_N2_AD1P_D08_65
# #set_property PACKAGE_PIN AR17     [get_ports ""] ;# Bank  65 VCCO - VCC1V8_FPGA - IO_L19N_T3L_N1_DBC_AD9N_D11_65
# #set_property IOSTANDARD  LVCMOSxx [get_ports ""] ;# Bank  65 VCCO - VCC1V8_FPGA - IO_L19N_T3L_N1_DBC_AD9N_D11_65
# #set_property PACKAGE_PIN AR18     [get_ports ""] ;# Bank  65 VCCO - VCC1V8_FPGA - IO_L19P_T3L_N0_DBC_AD9P_D10_65
# #set_property IOSTANDARD  LVCMOSxx [get_ports ""] ;# Bank  65 VCCO - VCC1V8_FPGA - IO_L19P_T3L_N0_DBC_AD9P_D10_65
# set_property PACKAGE_PIN AM17     [get_ports "PCIE_PERST_LS"] ;# Bank  65 VCCO - VCC1V8_FPGA - IO_T3U_N12_PERSTN0_65
# set_property IOSTANDARD  LVCMOS18 [get_ports "PCIE_PERST_LS"] ;# Bank  65 VCCO - VCC1V8_FPGA - IO_T3U_N12_PERSTN0_65
# #set_property PACKAGE_PIN AW17     [get_ports ""] ;# Bank  65 VCCO - VCC1V8_FPGA - IO_T2U_N12_CSI_ADV_B_65
# #set_property IOSTANDARD  LVCMOSxx [get_ports ""] ;# Bank  65 VCCO - VCC1V8_FPGA - IO_T2U_N12_CSI_ADV_B_65
# #set_property PACKAGE_PIN AT19     [get_ports ""] ;# Bank  65 VCCO - VCC1V8_FPGA - IO_L18N_T2U_N11_AD2N_D13_65
# #set_property IOSTANDARD  LVCMOSxx [get_ports ""] ;# Bank  65 VCCO - VCC1V8_FPGA - IO_L18N_T2U_N11_AD2N_D13_65
# #set_property PACKAGE_PIN AT20     [get_ports ""] ;# Bank  65 VCCO - VCC1V8_FPGA - IO_L18P_T2U_N10_AD2P_D12_65
# #set_property IOSTANDARD  LVCMOSxx [get_ports ""] ;# Bank  65 VCCO - VCC1V8_FPGA - IO_L18P_T2U_N10_AD2P_D12_65
# #set_property PACKAGE_PIN AU17     [get_ports ""] ;# Bank  65 VCCO - VCC1V8_FPGA - IO_L17N_T2U_N9_AD10N_D15_65
# #set_property IOSTANDARD  LVCMOSxx [get_ports ""] ;# Bank  65 VCCO - VCC1V8_FPGA - IO_L17N_T2U_N9_AD10N_D15_65
# #set_property PACKAGE_PIN AT17     [get_ports ""] ;# Bank  65 VCCO - VCC1V8_FPGA - IO_L17P_T2U_N8_AD10P_D14_65
# #set_property IOSTANDARD  LVCMOSxx [get_ports ""] ;# Bank  65 VCCO - VCC1V8_FPGA - IO_L17P_T2U_N8_AD10P_D14_65
# #set_property PACKAGE_PIN AR19     [get_ports ""] ;# Bank  65 VCCO - VCC1V8_FPGA - IO_L16N_T2U_N7_QBC_AD3N_A01_D17_65
# #set_property IOSTANDARD  LVCMOSxx [get_ports ""] ;# Bank  65 VCCO - VCC1V8_FPGA - IO_L16N_T2U_N7_QBC_AD3N_A01_D17_65
# #set_property PACKAGE_PIN AR20     [get_ports ""] ;# Bank  65 VCCO - VCC1V8_FPGA - IO_L16P_T2U_N6_QBC_AD3P_A00_D16_65
# #set_property IOSTANDARD  LVCMOSxx [get_ports ""] ;# Bank  65 VCCO - VCC1V8_FPGA - IO_L16P_T2U_N6_QBC_AD3P_A00_D16_65
# #set_property PACKAGE_PIN AW20     [get_ports ""] ;# Bank  65 VCCO - VCC1V8_FPGA - IO_L15N_T2L_N5_AD11N_A03_D19_65
# #set_property IOSTANDARD  LVCMOSxx [get_ports ""] ;# Bank  65 VCCO - VCC1V8_FPGA - IO_L15N_T2L_N5_AD11N_A03_D19_65
# #set_property PACKAGE_PIN AV20     [get_ports ""] ;# Bank  65 VCCO - VCC1V8_FPGA - IO_L15P_T2L_N4_AD11P_A02_D18_65
# #set_property IOSTANDARD  LVCMOSxx [get_ports ""] ;# Bank  65 VCCO - VCC1V8_FPGA - IO_L15P_T2L_N4_AD11P_A02_D18_65
# #set_property PACKAGE_PIN AU18     [get_ports ""] ;# Bank  65 VCCO - VCC1V8_FPGA - IO_L14N_T2L_N3_GC_A05_D21_65
# #set_property IOSTANDARD  LVCMOSxx [get_ports ""] ;# Bank  65 VCCO - VCC1V8_FPGA - IO_L14N_T2L_N3_GC_A05_D21_65
# #set_property PACKAGE_PIN AU19     [get_ports ""] ;# Bank  65 VCCO - VCC1V8_FPGA - IO_L14P_T2L_N2_GC_A04_D20_65
# #set_property IOSTANDARD  LVCMOSxx [get_ports ""] ;# Bank  65 VCCO - VCC1V8_FPGA - IO_L14P_T2L_N2_GC_A04_D20_65
# #set_property PACKAGE_PIN AV18     [get_ports ""] ;# Bank  65 VCCO - VCC1V8_FPGA - IO_L13N_T2L_N1_GC_QBC_A07_D23_65
# #set_property IOSTANDARD  LVCMOSxx [get_ports ""] ;# Bank  65 VCCO - VCC1V8_FPGA - IO_L13N_T2L_N1_GC_QBC_A07_D23_65
# #set_property PACKAGE_PIN AV19     [get_ports ""] ;# Bank  65 VCCO - VCC1V8_FPGA - IO_L13P_T2L_N0_GC_QBC_A06_D22_65
# #set_property IOSTANDARD  LVCMOSxx [get_ports ""] ;# Bank  65 VCCO - VCC1V8_FPGA - IO_L13P_T2L_N0_GC_QBC_A06_D22_65
# #set_property PACKAGE_PIN AY18     [get_ports ""] ;# Bank  65 VCCO - VCC1V8_FPGA - IO_L12N_T1U_N11_GC_A09_D25_65
# #set_property IOSTANDARD  LVCMOSxx [get_ports ""] ;# Bank  65 VCCO - VCC1V8_FPGA - IO_L12N_T1U_N11_GC_A09_D25_65
# #set_property PACKAGE_PIN AW18     [get_ports ""] ;# Bank  65 VCCO - VCC1V8_FPGA - IO_L12P_T1U_N10_GC_A08_D24_65
# #set_property IOSTANDARD  LVCMOSxx [get_ports ""] ;# Bank  65 VCCO - VCC1V8_FPGA - IO_L12P_T1U_N10_GC_A08_D24_65
# #set_property PACKAGE_PIN BA19     [get_ports ""] ;# Bank  65 VCCO - VCC1V8_FPGA - IO_L11N_T1U_N9_GC_A11_D27_65
# #set_property IOSTANDARD  LVCMOSxx [get_ports ""] ;# Bank  65 VCCO - VCC1V8_FPGA - IO_L11N_T1U_N9_GC_A11_D27_65
# #set_property PACKAGE_PIN AY19     [get_ports ""] ;# Bank  65 VCCO - VCC1V8_FPGA - IO_L11P_T1U_N8_GC_A10_D26_65
# #set_property IOSTANDARD  LVCMOSxx [get_ports ""] ;# Bank  65 VCCO - VCC1V8_FPGA - IO_L11P_T1U_N8_GC_A10_D26_65
# #set_property PACKAGE_PIN BB17     [get_ports ""] ;# Bank  65 VCCO - VCC1V8_FPGA - IO_L10N_T1U_N7_QBC_AD4N_A13_D29_65
# #set_property IOSTANDARD  LVCMOSxx [get_ports ""] ;# Bank  65 VCCO - VCC1V8_FPGA - IO_L10N_T1U_N7_QBC_AD4N_A13_D29_65
# #set_property PACKAGE_PIN BA17     [get_ports ""] ;# Bank  65 VCCO - VCC1V8_FPGA - IO_L10P_T1U_N6_QBC_AD4P_A12_D28_65
# #set_property IOSTANDARD  LVCMOSxx [get_ports ""] ;# Bank  65 VCCO - VCC1V8_FPGA - IO_L10P_T1U_N6_QBC_AD4P_A12_D28_65
# #set_property PACKAGE_PIN BC19     [get_ports ""] ;# Bank  65 VCCO - VCC1V8_FPGA - IO_L9N_T1L_N5_AD12N_A15_D31_65
# #set_property IOSTANDARD  LVCMOSxx [get_ports ""] ;# Bank  65 VCCO - VCC1V8_FPGA - IO_L9N_T1L_N5_AD12N_A15_D31_65
# #set_property PACKAGE_PIN BB19     [get_ports ""] ;# Bank  65 VCCO - VCC1V8_FPGA - IO_L9P_T1L_N4_AD12P_A14_D30_65
# #set_property IOSTANDARD  LVCMOSxx [get_ports ""] ;# Bank  65 VCCO - VCC1V8_FPGA - IO_L9P_T1L_N4_AD12P_A14_D30_65
# #set_property PACKAGE_PIN BC18     [get_ports ""] ;# Bank  65 VCCO - VCC1V8_FPGA - IO_L8N_T1L_N3_AD5N_A17_65
# #set_property IOSTANDARD  LVCMOSxx [get_ports ""] ;# Bank  65 VCCO - VCC1V8_FPGA - IO_L8N_T1L_N3_AD5N_A17_65
# #set_property PACKAGE_PIN BB18     [get_ports ""] ;# Bank  65 VCCO - VCC1V8_FPGA - IO_L8P_T1L_N2_AD5P_A16_65
# #set_property IOSTANDARD  LVCMOSxx [get_ports ""] ;# Bank  65 VCCO - VCC1V8_FPGA - IO_L8P_T1L_N2_AD5P_A16_65
# #set_property PACKAGE_PIN BA20     [get_ports ""] ;# Bank  65 VCCO - VCC1V8_FPGA - IO_L7N_T1L_N1_QBC_AD13N_A19_65
# #set_property IOSTANDARD  LVCMOSxx [get_ports ""] ;# Bank  65 VCCO - VCC1V8_FPGA - IO_L7N_T1L_N1_QBC_AD13N_A19_65
# #set_property PACKAGE_PIN AY20     [get_ports ""] ;# Bank  65 VCCO - VCC1V8_FPGA - IO_L7P_T1L_N0_QBC_AD13P_A18_65
# #set_property IOSTANDARD  LVCMOSxx [get_ports ""] ;# Bank  65 VCCO - VCC1V8_FPGA - IO_L7P_T1L_N0_QBC_AD13P_A18_65
# #set_property PACKAGE_PIN AY17     [get_ports ""] ;# Bank  65 VCCO - VCC1V8_FPGA - IO_T1U_N12_SMBALERT_65
# #set_property IOSTANDARD  LVCMOSxx [get_ports ""] ;# Bank  65 VCCO - VCC1V8_FPGA - IO_T1U_N12_SMBALERT_65
# #set_property PACKAGE_PIN BF21     [get_ports "VRP_65"] ;# Bank  65 VCCO - VCC1V8_FPGA - IO_T0U_N12_VRP_A28_65
# #set_property IOSTANDARD  LVCMOSxx [get_ports "VRP_65"] ;# Bank  65 VCCO - VCC1V8_FPGA - IO_T0U_N12_VRP_A28_65
# #set_property PACKAGE_PIN BD17     [get_ports ""] ;# Bank  65 VCCO - VCC1V8_FPGA - IO_L6N_T0U_N11_AD6N_A21_65
# #set_property IOSTANDARD  LVCMOSxx [get_ports ""] ;# Bank  65 VCCO - VCC1V8_FPGA - IO_L6N_T0U_N11_AD6N_A21_65
# #set_property PACKAGE_PIN BD18     [get_ports ""] ;# Bank  65 VCCO - VCC1V8_FPGA - IO_L6P_T0U_N10_AD6P_A20_65
# #set_property IOSTANDARD  LVCMOSxx [get_ports ""] ;# Bank  65 VCCO - VCC1V8_FPGA - IO_L6P_T0U_N10_AD6P_A20_65
# #set_property PACKAGE_PIN BD20     [get_ports ""] ;# Bank  65 VCCO - VCC1V8_FPGA - IO_L5N_T0U_N9_AD14N_A23_65
# #set_property IOSTANDARD  LVCMOSxx [get_ports ""] ;# Bank  65 VCCO - VCC1V8_FPGA - IO_L5N_T0U_N9_AD14N_A23_65
# #set_property PACKAGE_PIN BC20     [get_ports ""] ;# Bank  65 VCCO - VCC1V8_FPGA - IO_L5P_T0U_N8_AD14P_A22_65
# #set_property IOSTANDARD  LVCMOSxx [get_ports ""] ;# Bank  65 VCCO - VCC1V8_FPGA - IO_L5P_T0U_N8_AD14P_A22_65
# #set_property PACKAGE_PIN BE17     [get_ports ""] ;# Bank  65 VCCO - VCC1V8_FPGA - IO_L4N_T0U_N7_DBC_AD7N_A25_65
# #set_property IOSTANDARD  LVCMOSxx [get_ports ""] ;# Bank  65 VCCO - VCC1V8_FPGA - IO_L4N_T0U_N7_DBC_AD7N_A25_65
# #set_property PACKAGE_PIN BE18     [get_ports ""] ;# Bank  65 VCCO - VCC1V8_FPGA - IO_L4P_T0U_N6_DBC_AD7P_A24_65
# #set_property IOSTANDARD  LVCMOSxx [get_ports ""] ;# Bank  65 VCCO - VCC1V8_FPGA - IO_L4P_T0U_N6_DBC_AD7P_A24_65
# #set_property PACKAGE_PIN BF19     [get_ports ""] ;# Bank  65 VCCO - VCC1V8_FPGA - IO_L3N_T0L_N5_AD15N_A27_65
# #set_property IOSTANDARD  LVCMOSxx [get_ports ""] ;# Bank  65 VCCO - VCC1V8_FPGA - IO_L3N_T0L_N5_AD15N_A27_65
# #set_property PACKAGE_PIN BE19     [get_ports ""] ;# Bank  65 VCCO - VCC1V8_FPGA - IO_L3P_T0L_N4_AD15P_A26_65
# #set_property IOSTANDARD  LVCMOSxx [get_ports ""] ;# Bank  65 VCCO - VCC1V8_FPGA - IO_L3P_T0L_N4_AD15P_A26_65
# set_property PACKAGE_PIN BF16     [get_ports "QSPI1_CS_B"] ;# Bank  65 VCCO - VCC1V8_FPGA - IO_L2N_T0L_N3_FWE_FCS2_B_65
# set_property IOSTANDARD  LVCMOS18 [get_ports "QSPI1_CS_B"] ;# Bank  65 VCCO - VCC1V8_FPGA - IO_L2N_T0L_N3_FWE_FCS2_B_65
# set_property PACKAGE_PIN BF17     [get_ports "BPI_FLASH_OE_B"] ;# Bank  65 VCCO - VCC1V8_FPGA - IO_L2P_T0L_N2_FOE_B_65
# set_property IOSTANDARD  LVCMOS18 [get_ports "BPI_FLASH_OE_B"] ;# Bank  65 VCCO - VCC1V8_FPGA - IO_L2P_T0L_N2_FOE_B_65
# #set_property PACKAGE_PIN BF20     [get_ports ""] ;# Bank  65 VCCO - VCC1V8_FPGA - IO_L1N_T0L_N1_DBC_RS1_65
# #set_property IOSTANDARD  LVCMOSxx [get_ports ""] ;# Bank  65 VCCO - VCC1V8_FPGA - IO_L1N_T0L_N1_DBC_RS1_65
# #set_property PACKAGE_PIN BE20     [get_ports ""] ;# Bank  65 VCCO - VCC1V8_FPGA - IO_L1P_T0L_N0_DBC_RS0_65
# #set_property IOSTANDARD  LVCMOSxx [get_ports ""] ;# Bank  65 VCCO - VCC1V8_FPGA - IO_L1P_T0L_N0_DBC_RS0_65
# #Other net   PACKAGE_PIN AL17     - 8N8196                    Bank  65 - VREF_65
# set_property PACKAGE_PIN AM24     [get_ports "IIC_MAIN_SCL"] ;# Bank  64 VCCO - VCC1V8_FPGA - IO_L24N_T3U_N11_64
# set_property IOSTANDARD  LVCMOS18 [get_ports "IIC_MAIN_SCL"] ;# Bank  64 VCCO - VCC1V8_FPGA - IO_L24N_T3U_N11_64
# set_property PACKAGE_PIN AL24     [get_ports "IIC_MAIN_SDA"] ;# Bank  64 VCCO - VCC1V8_FPGA - IO_L24P_T3U_N10_64
# set_property IOSTANDARD  LVCMOS18 [get_ports "IIC_MAIN_SDA"] ;# Bank  64 VCCO - VCC1V8_FPGA - IO_L24P_T3U_N10_64
# set_property PACKAGE_PIN AM21     [get_ports "QSFP1_MODSELL_LS"] ;# Bank  64 VCCO - VCC1V8_FPGA - IO_L23N_T3U_N9_64
# set_property IOSTANDARD  LVCMOS18 [get_ports "QSFP1_MODSELL_LS"] ;# Bank  64 VCCO - VCC1V8_FPGA - IO_L23N_T3U_N9_64
# set_property PACKAGE_PIN AL21     [get_ports "QSFP1_MODPRSL_LS"] ;# Bank  64 VCCO - VCC1V8_FPGA - IO_L23P_T3U_N8_64
# set_property IOSTANDARD  LVCMOS18 [get_ports "QSFP1_MODPRSL_LS"] ;# Bank  64 VCCO - VCC1V8_FPGA - IO_L23P_T3U_N8_64
# set_property PACKAGE_PIN AM22     [get_ports "QSFP1_RECCLK_N"] ;# Bank  64 VCCO - VCC1V8_FPGA - IO_L22N_T3U_N7_DBC_AD0N_64
# set_property IOSTANDARD  LVDS [get_ports "QSFP1_RECCLK_N"] ;# Bank  64 VCCO - VCC1V8_FPGA - IO_L22N_T3U_N7_DBC_AD0N_64
# set_property PACKAGE_PIN AM23     [get_ports "QSFP1_RECCLK_P"] ;# Bank  64 VCCO - VCC1V8_FPGA - IO_L22P_T3U_N6_DBC_AD0P_64
# set_property IOSTANDARD  LVDS [get_ports "QSFP1_RECCLK_P"] ;# Bank  64 VCCO - VCC1V8_FPGA - IO_L22P_T3U_N6_DBC_AD0P_64
# set_property PACKAGE_PIN AP21     [get_ports "QSFP1_INTL_LS"] ;# Bank  64 VCCO - VCC1V8_FPGA - IO_L21N_T3L_N5_AD8N_64
# set_property IOSTANDARD  LVCMOS18 [get_ports "QSFP1_INTL_LS"] ;# Bank  64 VCCO - VCC1V8_FPGA - IO_L21N_T3L_N5_AD8N_64
# set_property PACKAGE_PIN AN21     [get_ports "QSFP1_LPMODE_LS"] ;# Bank  64 VCCO - VCC1V8_FPGA - IO_L21P_T3L_N4_AD8P_64
# set_property IOSTANDARD  LVCMOS18 [get_ports "QSFP1_LPMODE_LS"] ;# Bank  64 VCCO - VCC1V8_FPGA - IO_L21P_T3L_N4_AD8P_64
# set_property PACKAGE_PIN AN23     [get_ports "QSFP2_MODSELL_LS"] ;# Bank  64 VCCO - VCC1V8_FPGA - IO_L20N_T3L_N3_AD1N_64
# set_property IOSTANDARD  LVCMOS18 [get_ports "QSFP2_MODSELL_LS"] ;# Bank  64 VCCO - VCC1V8_FPGA - IO_L20N_T3L_N3_AD1N_64
# set_property PACKAGE_PIN AN24     [get_ports "QSFP2_MODPRSL_LS"] ;# Bank  64 VCCO - VCC1V8_FPGA - IO_L20P_T3L_N2_AD1P_64
# set_property IOSTANDARD  LVCMOS18 [get_ports "QSFP2_MODPRSL_LS"] ;# Bank  64 VCCO - VCC1V8_FPGA - IO_L20P_T3L_N2_AD1P_64
# set_property PACKAGE_PIN AP22     [get_ports "QSFP2_RECCLK_N"] ;# Bank  64 VCCO - VCC1V8_FPGA - IO_L19N_T3L_N1_DBC_AD9N_64
# set_property IOSTANDARD  LVDS [get_ports "QSFP2_RECCLK_N"] ;# Bank  64 VCCO - VCC1V8_FPGA - IO_L19N_T3L_N1_DBC_AD9N_64
# set_property PACKAGE_PIN AP23     [get_ports "QSFP2_RECCLK_P"] ;# Bank  64 VCCO - VCC1V8_FPGA - IO_L19P_T3L_N0_DBC_AD9P_64
# set_property IOSTANDARD  LVDS [get_ports "QSFP2_RECCLK_P"] ;# Bank  64 VCCO - VCC1V8_FPGA - IO_L19P_T3L_N0_DBC_AD9P_64
# set_property PACKAGE_PIN AL25     [get_ports "IIC_MUX_RESET_B"] ;# Bank  64 VCCO - VCC1V8_FPGA - IO_T3U_N12_64
# set_property IOSTANDARD  LVCMOS18 [get_ports "IIC_MUX_RESET_B"] ;# Bank  64 VCCO - VCC1V8_FPGA - IO_T3U_N12_64
# set_property PACKAGE_PIN AT21     [get_ports "QSFP2_INTL_LS"] ;# Bank  64 VCCO - VCC1V8_FPGA - IO_T2U_N12_64
# set_property IOSTANDARD  LVCMOS18 [get_ports "QSFP2_INTL_LS"] ;# Bank  64 VCCO - VCC1V8_FPGA - IO_T2U_N12_64
# set_property PACKAGE_PIN AT24     [get_ports "QSFP2_LPMODE_LS"] ;# Bank  64 VCCO - VCC1V8_FPGA - IO_L18N_T2U_N11_AD2N_64
# set_property IOSTANDARD  LVCMOS18 [get_ports "QSFP2_LPMODE_LS"] ;# Bank  64 VCCO - VCC1V8_FPGA - IO_L18N_T2U_N11_AD2N_64
# set_property PACKAGE_PIN AR24     [get_ports "PHY1_PDWN_B_I_INT_B_O"] ;# Bank  64 VCCO - VCC1V8_FPGA - IO_L18P_T2U_N10_AD2P_64
# set_property IOSTANDARD  LVCMOS18 [get_ports "PHY1_PDWN_B_I_INT_B_O"] ;# Bank  64 VCCO - VCC1V8_FPGA - IO_L18P_T2U_N10_AD2P_64
# set_property PACKAGE_PIN AR22     [get_ports "PHY1_GPIO_0"] ;# Bank  64 VCCO - VCC1V8_FPGA - IO_L17N_T2U_N9_AD10N_64
# set_property IOSTANDARD  LVCMOS18 [get_ports "PHY1_GPIO_0"] ;# Bank  64 VCCO - VCC1V8_FPGA - IO_L17N_T2U_N9_AD10N_64
# set_property PACKAGE_PIN AR23     [get_ports "PHY1_MDIO"] ;# Bank  64 VCCO - VCC1V8_FPGA - IO_L17P_T2U_N8_AD10P_64
# set_property IOSTANDARD  LVCMOS18 [get_ports "PHY1_MDIO"] ;# Bank  64 VCCO - VCC1V8_FPGA - IO_L17P_T2U_N8_AD10P_64
# set_property PACKAGE_PIN AV24     [get_ports "PHY1_SGMII_OUT_N"] ;# Bank  64 VCCO - VCC1V8_FPGA - IO_L16N_T2U_N7_QBC_AD3N_64
# set_property IOSTANDARD  LVDS [get_ports "PHY1_SGMII_OUT_N"] ;# Bank  64 VCCO - VCC1V8_FPGA - IO_L16N_T2U_N7_QBC_AD3N_64
# set_property PACKAGE_PIN AU24     [get_ports "PHY1_SGMII_OUT_P"] ;# Bank  64 VCCO - VCC1V8_FPGA - IO_L16P_T2U_N6_QBC_AD3P_64
# set_property IOSTANDARD  LVDS [get_ports "PHY1_SGMII_OUT_P"] ;# Bank  64 VCCO - VCC1V8_FPGA - IO_L16P_T2U_N6_QBC_AD3P_64
# set_property PACKAGE_PIN AV21     [get_ports "PHY1_SGMII_IN_N"] ;# Bank  64 VCCO - VCC1V8_FPGA - IO_L15N_T2L_N5_AD11N_64
# set_property IOSTANDARD  LVDS [get_ports "PHY1_SGMII_IN_N"] ;# Bank  64 VCCO - VCC1V8_FPGA - IO_L15N_T2L_N5_AD11N_64
# set_property PACKAGE_PIN AU21     [get_ports "PHY1_SGMII_IN_P"] ;# Bank  64 VCCO - VCC1V8_FPGA - IO_L15P_T2L_N4_AD11P_64
# set_property IOSTANDARD  LVDS [get_ports "PHY1_SGMII_IN_P"] ;# Bank  64 VCCO - VCC1V8_FPGA - IO_L15P_T2L_N4_AD11P_64
# set_property PACKAGE_PIN AV23     [get_ports "PHY1_MDC"] ;# Bank  64 VCCO - VCC1V8_FPGA - IO_L14N_T2L_N3_GC_64
# set_property IOSTANDARD  LVCMOS18 [get_ports "PHY1_MDC"] ;# Bank  64 VCCO - VCC1V8_FPGA - IO_L14N_T2L_N3_GC_64
# set_property PACKAGE_PIN AU23     [get_ports "PHY1_CLKOUT"] ;# Bank  64 VCCO - VCC1V8_FPGA - IO_L14P_T2L_N2_GC_64
# set_property IOSTANDARD  LVCMOS18 [get_ports "PHY1_CLKOUT"] ;# Bank  64 VCCO - VCC1V8_FPGA - IO_L14P_T2L_N2_GC_64
# set_property PACKAGE_PIN AU22     [get_ports "PHY1_SGMII_CLK_N"] ;# Bank  64 VCCO - VCC1V8_FPGA - IO_L13N_T2L_N1_GC_QBC_64
# set_property IOSTANDARD  LVDS [get_ports "PHY1_SGMII_CLK_N"] ;# Bank  64 VCCO - VCC1V8_FPGA - IO_L13N_T2L_N1_GC_QBC_64
# set_property PACKAGE_PIN AT22     [get_ports "PHY1_SGMII_CLK_P"] ;# Bank  64 VCCO - VCC1V8_FPGA - IO_L13P_T2L_N0_GC_QBC_64
# set_property IOSTANDARD  LVDS [get_ports "PHY1_SGMII_CLK_P"] ;# Bank  64 VCCO - VCC1V8_FPGA - IO_L13P_T2L_N0_GC_QBC_64
# set_property PACKAGE_PIN AW22     [get_ports "USER_SI570_CLOCK1_N"] ;# Bank  64 VCCO - VCC1V8_FPGA - IO_L12N_T1U_N11_GC_64
# set_property IOSTANDARD  LVDS [get_ports "USER_SI570_CLOCK1_N"] ;# Bank  64 VCCO - VCC1V8_FPGA - IO_L12N_T1U_N11_GC_64
# set_property PACKAGE_PIN AW23     [get_ports "USER_SI570_CLOCK1_P"] ;# Bank  64 VCCO - VCC1V8_FPGA - IO_L12P_T1U_N10_GC_64
# set_property IOSTANDARD  LVDS [get_ports "USER_SI570_CLOCK1_P"] ;# Bank  64 VCCO - VCC1V8_FPGA - IO_L12P_T1U_N10_GC_64
# set_property PACKAGE_PIN BA22     [get_ports "QSFP1_RESETL_LS"] ;# Bank  64 VCCO - VCC1V8_FPGA - IO_L10N_T1U_N7_QBC_AD4N_64
# set_property IOSTANDARD  LVCMOS18 [get_ports "QSFP1_RESETL_LS"] ;# Bank  64 VCCO - VCC1V8_FPGA - IO_L10N_T1U_N7_QBC_AD4N_64
# set_property PACKAGE_PIN AY22     [get_ports "QSFP2_RESETL_LS"] ;# Bank  64 VCCO - VCC1V8_FPGA - IO_L10P_T1U_N6_QBC_AD4P_64
# set_property IOSTANDARD  LVCMOS18 [get_ports "QSFP2_RESETL_LS"] ;# Bank  64 VCCO - VCC1V8_FPGA - IO_L10P_T1U_N6_QBC_AD4P_64
# set_property PACKAGE_PIN AY25     [get_ports "USB_UART_RTS"] ;# Bank  64 VCCO - VCC1V8_FPGA - IO_L9N_T1L_N5_AD12N_64
# set_property IOSTANDARD  LVCMOS18 [get_ports "USB_UART_RTS"] ;# Bank  64 VCCO - VCC1V8_FPGA - IO_L9N_T1L_N5_AD12N_64

# set_property PACKAGE_PIN BB22     [get_ports "USB_UART_CTS"] ;# Bank  64 VCCO - VCC1V8_FPGA - IO_L8P_T1L_N2_AD5P_64
# set_property IOSTANDARD  LVCMOS18 [get_ports "USB_UART_CTS"] ;# Bank  64 VCCO - VCC1V8_FPGA - IO_L8P_T1L_N2_AD5P_64
# set_property PACKAGE_PIN BA24     [get_ports "SYSCTLR_GPIO_7"] ;# Bank  64 VCCO - VCC1V8_FPGA - IO_L7N_T1L_N1_QBC_AD13N_64
# set_property IOSTANDARD  LVCMOS18 [get_ports "SYSCTLR_GPIO_7"] ;# Bank  64 VCCO - VCC1V8_FPGA - IO_L7N_T1L_N1_QBC_AD13N_64
# set_property PACKAGE_PIN BA25     [get_ports "SYSCTLR_GPIO_6"] ;# Bank  64 VCCO - VCC1V8_FPGA - IO_L7P_T1L_N0_QBC_AD13P_64
# set_property IOSTANDARD  LVCMOS18 [get_ports "SYSCTLR_GPIO_6"] ;# Bank  64 VCCO - VCC1V8_FPGA - IO_L7P_T1L_N0_QBC_AD13P_64
# set_property PACKAGE_PIN BA21     [get_ports "PHY1_RESET_B"] ;# Bank  64 VCCO - VCC1V8_FPGA - IO_T1U_N12_64
# set_property IOSTANDARD  LVCMOS18 [get_ports "PHY1_RESET_B"] ;# Bank  64 VCCO - VCC1V8_FPGA - IO_T1U_N12_64
# #set_property PACKAGE_PIN BC24     [get_ports "PCIE_WAKE_B_LS"] ;# Bank  64 VCCO - VCC1V8_FPGA - IO_T0U_N12_VRP_64
# #set_property IOSTANDARD  LVCMOS18 [get_ports "PCIE_WAKE_B_LS"] ;# Bank  64 VCCO - VCC1V8_FPGA - IO_T0U_N12_VRP_64
# set_property PACKAGE_PIN BD21     [get_ports "SYSCTLR_GPIO_5"] ;# Bank  64 VCCO - VCC1V8_FPGA - IO_L6N_T0U_N11_AD6N_64
# set_property IOSTANDARD  LVCMOS18 [get_ports "SYSCTLR_GPIO_5"] ;# Bank  64 VCCO - VCC1V8_FPGA - IO_L6N_T0U_N11_AD6N_64
# set_property PACKAGE_PIN BC21     [get_ports "SI5328_RST_LS_B"] ;# Bank  64 VCCO - VCC1V8_FPGA - IO_L6P_T0U_N10_AD6P_64
# set_property IOSTANDARD  LVCMOS18 [get_ports "SI5328_RST_LS_B"] ;# Bank  64 VCCO - VCC1V8_FPGA - IO_L6P_T0U_N10_AD6P_64
# set_property PACKAGE_PIN BB23     [get_ports "PMBUS_ALERT_FPGA"] ;# Bank  64 VCCO - VCC1V8_FPGA - IO_L5N_T0U_N9_AD14N_64
# set_property IOSTANDARD  LVCMOS18 [get_ports "PMBUS_ALERT_FPGA"] ;# Bank  64 VCCO - VCC1V8_FPGA - IO_L5N_T0U_N9_AD14N_64
# set_property PACKAGE_PIN BB24     [get_ports "GPIO_SW_N"] ;# Bank  64 VCCO - VCC1V8_FPGA - IO_L5P_T0U_N8_AD14P_64
# set_property IOSTANDARD  LVCMOS18 [get_ports "GPIO_SW_N"] ;# Bank  64 VCCO - VCC1V8_FPGA - IO_L5P_T0U_N8_AD14P_64
# set_property PACKAGE_PIN BF22     [get_ports "GPIO_SW_W"] ;# Bank  64 VCCO - VCC1V8_FPGA - IO_L4N_T0U_N7_DBC_AD7N_64
# set_property IOSTANDARD  LVCMOS18 [get_ports "GPIO_SW_W"] ;# Bank  64 VCCO - VCC1V8_FPGA - IO_L4N_T0U_N7_DBC_AD7N_64
# set_property PACKAGE_PIN BE22     [get_ports "GPIO_SW_S"] ;# Bank  64 VCCO - VCC1V8_FPGA - IO_L4P_T0U_N6_DBC_AD7P_64
# set_property IOSTANDARD  LVCMOS18 [get_ports "GPIO_SW_S"] ;# Bank  64 VCCO - VCC1V8_FPGA - IO_L4P_T0U_N6_DBC_AD7P_64
# set_property PACKAGE_PIN BE23     [get_ports "GPIO_SW_E"] ;# Bank  64 VCCO - VCC1V8_FPGA - IO_L3N_T0L_N5_AD15N_64
# set_property IOSTANDARD  LVCMOS18 [get_ports "GPIO_SW_E"] ;# Bank  64 VCCO - VCC1V8_FPGA - IO_L3N_T0L_N5_AD15N_64
# set_property PACKAGE_PIN BD23     [get_ports "GPIO_SW_C"] ;# Bank  64 VCCO - VCC1V8_FPGA - IO_L3P_T0L_N4_AD15P_64
# set_property IOSTANDARD  LVCMOS18 [get_ports "GPIO_SW_C"] ;# Bank  64 VCCO - VCC1V8_FPGA - IO_L3P_T0L_N4_AD15P_64
# set_property PACKAGE_PIN BD22     [get_ports "FIREFLY_MODPRS_LS_B"] ;# Bank  64 VCCO - VCC1V8_FPGA - IO_L2N_T0L_N3_64
# set_property IOSTANDARD  LVCMOS18 [get_ports "FIREFLY_MODPRS_LS_B"] ;# Bank  64 VCCO - VCC1V8_FPGA - IO_L2N_T0L_N3_64
# set_property PACKAGE_PIN BC23     [get_ports "FIREFLY_MODSEL_LS_B"] ;# Bank  64 VCCO - VCC1V8_FPGA - IO_L2P_T0L_N2_64
# set_property IOSTANDARD  LVCMOS18 [get_ports "FIREFLY_MODSEL_LS_B"] ;# Bank  64 VCCO - VCC1V8_FPGA - IO_L2P_T0L_N2_64
# set_property PACKAGE_PIN BF24     [get_ports "FIREFLY_INT_LS_B"] ;# Bank  64 VCCO - VCC1V8_FPGA - IO_L1N_T0L_N1_DBC_64
# set_property IOSTANDARD  LVCMOS18 [get_ports "FIREFLY_INT_LS_B"] ;# Bank  64 VCCO - VCC1V8_FPGA - IO_L1N_T0L_N1_DBC_64
# set_property PACKAGE_PIN BE24     [get_ports "FIREFLY_RESET_LS_B"] ;# Bank  64 VCCO - VCC1V8_FPGA - IO_L1P_T0L_N0_DBC_64
# set_property IOSTANDARD  LVCMOS18 [get_ports "FIREFLY_RESET_LS_B"] ;# Bank  64 VCCO - VCC1V8_FPGA - IO_L1P_T0L_N0_DBC_64
# #Other net   PACKAGE_PIN AL22     - 30N4994                   Bank  64 - VREF_64
# set_property PACKAGE_PIN AG33     [get_ports "FMCP_HSPC_LA15_N"] ;# Bank  43 VCCO - VADJ_1V8_FPGA - IO_L24N_T3U_N11_43
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_LA15_N"] ;# Bank  43 VCCO - VADJ_1V8_FPGA - IO_L24N_T3U_N11_43
# set_property PACKAGE_PIN AG32     [get_ports "FMCP_HSPC_LA15_P"] ;# Bank  43 VCCO - VADJ_1V8_FPGA - IO_L24P_T3U_N10_43
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_LA15_P"] ;# Bank  43 VCCO - VADJ_1V8_FPGA - IO_L24P_T3U_N10_43
# set_property PACKAGE_PIN AH31     [get_ports "FMCP_HSPC_LA14_N"] ;# Bank  43 VCCO - VADJ_1V8_FPGA - IO_L23N_T3U_N9_43
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_LA14_N"] ;# Bank  43 VCCO - VADJ_1V8_FPGA - IO_L23N_T3U_N9_43
# set_property PACKAGE_PIN AG31     [get_ports "FMCP_HSPC_LA14_P"] ;# Bank  43 VCCO - VADJ_1V8_FPGA - IO_L23P_T3U_N8_43
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_LA14_P"] ;# Bank  43 VCCO - VADJ_1V8_FPGA - IO_L23P_T3U_N8_43
# set_property PACKAGE_PIN AH35     [get_ports "FMCP_HSPC_LA16_N"] ;# Bank  43 VCCO - VADJ_1V8_FPGA - IO_L22N_T3U_N7_DBC_AD0N_43
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_LA16_N"] ;# Bank  43 VCCO - VADJ_1V8_FPGA - IO_L22N_T3U_N7_DBC_AD0N_43
# set_property PACKAGE_PIN AG34     [get_ports "FMCP_HSPC_LA16_P"] ;# Bank  43 VCCO - VADJ_1V8_FPGA - IO_L22P_T3U_N6_DBC_AD0P_43
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_LA16_P"] ;# Bank  43 VCCO - VADJ_1V8_FPGA - IO_L22P_T3U_N6_DBC_AD0P_43
# set_property PACKAGE_PIN AH34     [get_ports "FMCP_HSPC_LA12_N"] ;# Bank  43 VCCO - VADJ_1V8_FPGA - IO_L21N_T3L_N5_AD8N_43
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_LA12_N"] ;# Bank  43 VCCO - VADJ_1V8_FPGA - IO_L21N_T3L_N5_AD8N_43
# set_property PACKAGE_PIN AH33     [get_ports "FMCP_HSPC_LA12_P"] ;# Bank  43 VCCO - VADJ_1V8_FPGA - IO_L21P_T3L_N4_AD8P_43
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_LA12_P"] ;# Bank  43 VCCO - VADJ_1V8_FPGA - IO_L21P_T3L_N4_AD8P_43
# set_property PACKAGE_PIN AJ36     [get_ports "FMCP_HSPC_LA13_N"] ;# Bank  43 VCCO - VADJ_1V8_FPGA - IO_L20N_T3L_N3_AD1N_43
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_LA13_N"] ;# Bank  43 VCCO - VADJ_1V8_FPGA - IO_L20N_T3L_N3_AD1N_43
# set_property PACKAGE_PIN AJ35     [get_ports "FMCP_HSPC_LA13_P"] ;# Bank  43 VCCO - VADJ_1V8_FPGA - IO_L20P_T3L_N2_AD1P_43
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_LA13_P"] ;# Bank  43 VCCO - VADJ_1V8_FPGA - IO_L20P_T3L_N2_AD1P_43
# set_property PACKAGE_PIN AK33     [get_ports "FMCP_HSPC_LA09_N"] ;# Bank  43 VCCO - VADJ_1V8_FPGA - IO_L19N_T3L_N1_DBC_AD9N_43
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_LA09_N"] ;# Bank  43 VCCO - VADJ_1V8_FPGA - IO_L19N_T3L_N1_DBC_AD9N_43
# set_property PACKAGE_PIN AJ33     [get_ports "FMCP_HSPC_LA09_P"] ;# Bank  43 VCCO - VADJ_1V8_FPGA - IO_L19P_T3L_N0_DBC_AD9P_43
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_LA09_P"] ;# Bank  43 VCCO - VADJ_1V8_FPGA - IO_L19P_T3L_N0_DBC_AD9P_43
# set_property PACKAGE_PIN AH30     [get_ports "9N9738"] ;# Bank  43 VCCO - VADJ_1V8_FPGA - IO_T3U_N12_43
# set_property IOSTANDARD  LVCMOSxx [get_ports "9N9738"] ;# Bank  43 VCCO - VADJ_1V8_FPGA - IO_T3U_N12_43
# set_property PACKAGE_PIN AM31     [get_ports "9N9739"] ;# Bank  43 VCCO - VADJ_1V8_FPGA - IO_T2U_N12_43
# set_property IOSTANDARD  LVCMOSxx [get_ports "9N9739"] ;# Bank  43 VCCO - VADJ_1V8_FPGA - IO_T2U_N12_43
# set_property PACKAGE_PIN AK30     [get_ports "FMCP_HSPC_LA08_N"] ;# Bank  43 VCCO - VADJ_1V8_FPGA - IO_L18N_T2U_N11_AD2N_43
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_LA08_N"] ;# Bank  43 VCCO - VADJ_1V8_FPGA - IO_L18N_T2U_N11_AD2N_43
# set_property PACKAGE_PIN AK29     [get_ports "FMCP_HSPC_LA08_P"] ;# Bank  43 VCCO - VADJ_1V8_FPGA - IO_L18P_T2U_N10_AD2P_43
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_LA08_P"] ;# Bank  43 VCCO - VADJ_1V8_FPGA - IO_L18P_T2U_N10_AD2P_43
# set_property PACKAGE_PIN AJ31     [get_ports "FMCP_HSPC_LA11_N"] ;# Bank  43 VCCO - VADJ_1V8_FPGA - IO_L17N_T2U_N9_AD10N_43
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_LA11_N"] ;# Bank  43 VCCO - VADJ_1V8_FPGA - IO_L17N_T2U_N9_AD10N_43
# set_property PACKAGE_PIN AJ30     [get_ports "FMCP_HSPC_LA11_P"] ;# Bank  43 VCCO - VADJ_1V8_FPGA - IO_L17P_T2U_N8_AD10P_43
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_LA11_P"] ;# Bank  43 VCCO - VADJ_1V8_FPGA - IO_L17P_T2U_N8_AD10P_43
# set_property PACKAGE_PIN AL31     [get_ports "FMCP_HSPC_LA01_CC_N"] ;# Bank  43 VCCO - VADJ_1V8_FPGA - IO_L16N_T2U_N7_QBC_AD3N_43
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_LA01_CC_N"] ;# Bank  43 VCCO - VADJ_1V8_FPGA - IO_L16N_T2U_N7_QBC_AD3N_43
# set_property PACKAGE_PIN AL30     [get_ports "FMCP_HSPC_LA01_CC_P"] ;# Bank  43 VCCO - VADJ_1V8_FPGA - IO_L16P_T2U_N6_QBC_AD3P_43
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_LA01_CC_P"] ;# Bank  43 VCCO - VADJ_1V8_FPGA - IO_L16P_T2U_N6_QBC_AD3P_43
# set_property PACKAGE_PIN AM29     [get_ports "FMCP_HSPC_Z_PRSNT_M2C_B_LS"] ;# Bank  43 VCCO - VADJ_1V8_FPGA - IO_L15N_T2L_N5_AD11N_43
# set_property IOSTANDARD  LVCMOS18 [get_ports "FMCP_HSPC_Z_PRSNT_M2C_B_LS"] ;# Bank  43 VCCO - VADJ_1V8_FPGA - IO_L15N_T2L_N5_AD11N_43
# set_property PACKAGE_PIN AL29     [get_ports "FMC_VADJ_ON_LS"] ;# Bank  43 VCCO - VADJ_1V8_FPGA - IO_L15P_T2L_N4_AD11P_43
# set_property IOSTANDARD  LVCMOS18 [get_ports "FMC_VADJ_ON_LS"] ;# Bank  43 VCCO - VADJ_1V8_FPGA - IO_L15P_T2L_N4_AD11P_43
# set_property PACKAGE_PIN AK32     [get_ports "FMCP_HSPC_LA02_N"] ;# Bank  43 VCCO - VADJ_1V8_FPGA - IO_L14N_T2L_N3_GC_43
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_LA02_N"] ;# Bank  43 VCCO - VADJ_1V8_FPGA - IO_L14N_T2L_N3_GC_43
# set_property PACKAGE_PIN AJ32     [get_ports "FMCP_HSPC_LA02_P"] ;# Bank  43 VCCO - VADJ_1V8_FPGA - IO_L14P_T2L_N2_GC_43
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_LA02_P"] ;# Bank  43 VCCO - VADJ_1V8_FPGA - IO_L14P_T2L_N2_GC_43
# set_property PACKAGE_PIN AM32     [get_ports "FMCP_HSPC_CLK0_M2C_N"] ;# Bank  43 VCCO - VADJ_1V8_FPGA - IO_L13N_T2L_N1_GC_QBC_43
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_CLK0_M2C_N"] ;# Bank  43 VCCO - VADJ_1V8_FPGA - IO_L13N_T2L_N1_GC_QBC_43
# set_property PACKAGE_PIN AL32     [get_ports "FMCP_HSPC_CLK0_M2C_P"] ;# Bank  43 VCCO - VADJ_1V8_FPGA - IO_L13P_T2L_N0_GC_QBC_43
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_CLK0_M2C_P"] ;# Bank  43 VCCO - VADJ_1V8_FPGA - IO_L13P_T2L_N0_GC_QBC_43
# set_property PACKAGE_PIN AM34     [get_ports "FMCP_HSPC_PG_M2C_LS"] ;# Bank  43 VCCO - VADJ_1V8_FPGA - IO_L12N_T1U_N11_GC_43
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_PG_M2C_LS"] ;# Bank  43 VCCO - VADJ_1V8_FPGA - IO_L12N_T1U_N11_GC_43
# set_property PACKAGE_PIN AM33     [get_ports "FMCP_HSPC_H_PRSNT_M2C_B_LS"] ;# Bank  43 VCCO - VADJ_1V8_FPGA - IO_L12P_T1U_N10_GC_43
# set_property IOSTANDARD  LVCMOS18 [get_ports "FMCP_HSPC_H_PRSNT_M2C_B_LS"] ;# Bank  43 VCCO - VADJ_1V8_FPGA - IO_L12P_T1U_N10_GC_43
# set_property PACKAGE_PIN AL34     [get_ports "FMCP_HSPC_REFCLK_M2C_N"] ;# Bank  43 VCCO - VADJ_1V8_FPGA - IO_L11N_T1U_N9_GC_43
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_REFCLK_M2C_N"] ;# Bank  43 VCCO - VADJ_1V8_FPGA - IO_L11N_T1U_N9_GC_43
# set_property PACKAGE_PIN AK34     [get_ports "FMCP_HSPC_REFCLK_M2C_P"] ;# Bank  43 VCCO - VADJ_1V8_FPGA - IO_L11P_T1U_N8_GC_43
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_REFCLK_M2C_P"] ;# Bank  43 VCCO - VADJ_1V8_FPGA - IO_L11P_T1U_N8_GC_43
# set_property PACKAGE_PIN AP33     [get_ports "FMCP_HSPC_REFCLK_C2M_N"] ;# Bank  43 VCCO - VADJ_1V8_FPGA - IO_L10N_T1U_N7_QBC_AD4N_43
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_REFCLK_C2M_N"] ;# Bank  43 VCCO - VADJ_1V8_FPGA - IO_L10N_T1U_N7_QBC_AD4N_43
# set_property PACKAGE_PIN AN33     [get_ports "FMCP_HSPC_REFCLK_C2M_P"] ;# Bank  43 VCCO - VADJ_1V8_FPGA - IO_L10P_T1U_N6_QBC_AD4P_43
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_REFCLK_C2M_P"] ;# Bank  43 VCCO - VADJ_1V8_FPGA - IO_L10P_T1U_N6_QBC_AD4P_43
# set_property PACKAGE_PIN AN36     [get_ports "FMCP_HSPC_SYNC_M2C_N"] ;# Bank  43 VCCO - VADJ_1V8_FPGA - IO_L9N_T1L_N5_AD12N_43
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_SYNC_M2C_N"] ;# Bank  43 VCCO - VADJ_1V8_FPGA - IO_L9N_T1L_N5_AD12N_43
# set_property PACKAGE_PIN AM36     [get_ports "FMCP_HSPC_SYNC_M2C_P"] ;# Bank  43 VCCO - VADJ_1V8_FPGA - IO_L9P_T1L_N4_AD12P_43
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_SYNC_M2C_P"] ;# Bank  43 VCCO - VADJ_1V8_FPGA - IO_L9P_T1L_N4_AD12P_43
# set_property PACKAGE_PIN AN35     [get_ports "FMCP_HSPC_SYNC_C2M_N"] ;# Bank  43 VCCO - VADJ_1V8_FPGA - IO_L8N_T1L_N3_AD5N_43
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_SYNC_C2M_N"] ;# Bank  43 VCCO - VADJ_1V8_FPGA - IO_L8N_T1L_N3_AD5N_43
# set_property PACKAGE_PIN AN34     [get_ports "FMCP_HSPC_SYNC_C2M_P"] ;# Bank  43 VCCO - VADJ_1V8_FPGA - IO_L8P_T1L_N2_AD5P_43
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_SYNC_C2M_P"] ;# Bank  43 VCCO - VADJ_1V8_FPGA - IO_L8P_T1L_N2_AD5P_43
# set_property PACKAGE_PIN AL36     [get_ports "FMCP_HSPC_LA00_CC_N"] ;# Bank  43 VCCO - VADJ_1V8_FPGA - IO_L7N_T1L_N1_QBC_AD13N_43
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_LA00_CC_N"] ;# Bank  43 VCCO - VADJ_1V8_FPGA - IO_L7N_T1L_N1_QBC_AD13N_43
# set_property PACKAGE_PIN AL35     [get_ports "FMCP_HSPC_LA00_CC_P"] ;# Bank  43 VCCO - VADJ_1V8_FPGA - IO_L7P_T1L_N0_QBC_AD13P_43
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_LA00_CC_P"] ;# Bank  43 VCCO - VADJ_1V8_FPGA - IO_L7P_T1L_N0_QBC_AD13P_43
# set_property PACKAGE_PIN AK35     [get_ports "VADJ_1V8_PGOOD_LS"] ;# Bank  43 VCCO - VADJ_1V8_FPGA - IO_T1U_N12_43
# set_property IOSTANDARD  LVCMOS18 [get_ports "VADJ_1V8_PGOOD_LS"] ;# Bank  43 VCCO - VADJ_1V8_FPGA - IO_T1U_N12_43
# #set_property PACKAGE_PIN AR34     [get_ports "VRP_43"] ;# Bank  43 VCCO - VADJ_1V8_FPGA - IO_T0U_N12_VRP_43
# #set_property IOSTANDARD  LVCMOSxx [get_ports "VRP_43"] ;# Bank  43 VCCO - VADJ_1V8_FPGA - IO_T0U_N12_VRP_43
# set_property PACKAGE_PIN AT37     [get_ports "FMCP_HSPC_LA04_N"] ;# Bank  43 VCCO - VADJ_1V8_FPGA - IO_L6N_T0U_N11_AD6N_43
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_LA04_N"] ;# Bank  43 VCCO - VADJ_1V8_FPGA - IO_L6N_T0U_N11_AD6N_43
# set_property PACKAGE_PIN AR37     [get_ports "FMCP_HSPC_LA04_P"] ;# Bank  43 VCCO - VADJ_1V8_FPGA - IO_L6P_T0U_N10_AD6P_43
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_LA04_P"] ;# Bank  43 VCCO - VADJ_1V8_FPGA - IO_L6P_T0U_N10_AD6P_43
# set_property PACKAGE_PIN AP37     [get_ports "FMCP_HSPC_LA07_N"] ;# Bank  43 VCCO - VADJ_1V8_FPGA - IO_L5N_T0U_N9_AD14N_43
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_LA07_N"] ;# Bank  43 VCCO - VADJ_1V8_FPGA - IO_L5N_T0U_N9_AD14N_43
# set_property PACKAGE_PIN AP36     [get_ports "FMCP_HSPC_LA07_P"] ;# Bank  43 VCCO - VADJ_1V8_FPGA - IO_L5P_T0U_N8_AD14P_43
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_LA07_P"] ;# Bank  43 VCCO - VADJ_1V8_FPGA - IO_L5P_T0U_N8_AD14P_43
# set_property PACKAGE_PIN AT40     [get_ports "FMCP_HSPC_LA03_N"] ;# Bank  43 VCCO - VADJ_1V8_FPGA - IO_L4N_T0U_N7_DBC_AD7N_43
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_LA03_N"] ;# Bank  43 VCCO - VADJ_1V8_FPGA - IO_L4N_T0U_N7_DBC_AD7N_43
# set_property PACKAGE_PIN AT39     [get_ports "FMCP_HSPC_LA03_P"] ;# Bank  43 VCCO - VADJ_1V8_FPGA - IO_L4P_T0U_N6_DBC_AD7P_43
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_LA03_P"] ;# Bank  43 VCCO - VADJ_1V8_FPGA - IO_L4P_T0U_N6_DBC_AD7P_43
# set_property PACKAGE_PIN AR35     [get_ports "FMCP_HSPC_LA10_N"] ;# Bank  43 VCCO - VADJ_1V8_FPGA - IO_L3N_T0L_N5_AD15N_43
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_LA10_N"] ;# Bank  43 VCCO - VADJ_1V8_FPGA - IO_L3N_T0L_N5_AD15N_43
# set_property PACKAGE_PIN AP35     [get_ports "FMCP_HSPC_LA10_P"] ;# Bank  43 VCCO - VADJ_1V8_FPGA - IO_L3P_T0L_N4_AD15P_43
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_LA10_P"] ;# Bank  43 VCCO - VADJ_1V8_FPGA - IO_L3P_T0L_N4_AD15P_43
# set_property PACKAGE_PIN AT36     [get_ports "FMCP_HSPC_LA06_N"] ;# Bank  43 VCCO - VADJ_1V8_FPGA - IO_L2N_T0L_N3_43
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_LA06_N"] ;# Bank  43 VCCO - VADJ_1V8_FPGA - IO_L2N_T0L_N3_43
# set_property PACKAGE_PIN AT35     [get_ports "FMCP_HSPC_LA06_P"] ;# Bank  43 VCCO - VADJ_1V8_FPGA - IO_L2P_T0L_N2_43
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_LA06_P"] ;# Bank  43 VCCO - VADJ_1V8_FPGA - IO_L2P_T0L_N2_43
# set_property PACKAGE_PIN AR38     [get_ports "FMCP_HSPC_LA05_N"] ;# Bank  43 VCCO - VADJ_1V8_FPGA - IO_L1N_T0L_N1_DBC_43
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_LA05_N"] ;# Bank  43 VCCO - VADJ_1V8_FPGA - IO_L1N_T0L_N1_DBC_43
# set_property PACKAGE_PIN AP38     [get_ports "FMCP_HSPC_LA05_P"] ;# Bank  43 VCCO - VADJ_1V8_FPGA - IO_L1P_T0L_N0_DBC_43
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_LA05_P"] ;# Bank  43 VCCO - VADJ_1V8_FPGA - IO_L1P_T0L_N0_DBC_43
# #Other net   PACKAGE_PIN AJ29     - VREF_43                   Bank  43 - VREF_43
# set_property PACKAGE_PIN AV39     [get_ports "DDR4_C2_DQ63"] ;# Bank  42 VCCO - VCC1V2_FPGA - IO_L24N_T3U_N11_42
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C2_DQ63"] ;# Bank  42 VCCO - VCC1V2_FPGA - IO_L24N_T3U_N11_42
# set_property PACKAGE_PIN AV38     [get_ports "DDR4_C2_DQ62"] ;# Bank  42 VCCO - VCC1V2_FPGA - IO_L24P_T3U_N10_42
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C2_DQ62"] ;# Bank  42 VCCO - VCC1V2_FPGA - IO_L24P_T3U_N10_42
# set_property PACKAGE_PIN AU39     [get_ports "DDR4_C2_DQ61"] ;# Bank  42 VCCO - VCC1V2_FPGA - IO_L23N_T3U_N9_42
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C2_DQ61"] ;# Bank  42 VCCO - VCC1V2_FPGA - IO_L23N_T3U_N9_42
# set_property PACKAGE_PIN AU38     [get_ports "DDR4_C2_DQ60"] ;# Bank  42 VCCO - VCC1V2_FPGA - IO_L23P_T3U_N8_42
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C2_DQ60"] ;# Bank  42 VCCO - VCC1V2_FPGA - IO_L23P_T3U_N8_42
# set_property PACKAGE_PIN AW38     [get_ports "DDR4_C2_DQS7_C"] ;# Bank  42 VCCO - VCC1V2_FPGA - IO_L22N_T3U_N7_DBC_AD0N_42
# set_property IOSTANDARD  DIFF_POD12 [get_ports "DDR4_C2_DQS7_C"] ;# Bank  42 VCCO - VCC1V2_FPGA - IO_L22N_T3U_N7_DBC_AD0N_42
# set_property PACKAGE_PIN AW37     [get_ports "DDR4_C2_DQS7_T"] ;# Bank  42 VCCO - VCC1V2_FPGA - IO_L22P_T3U_N6_DBC_AD0P_42
# set_property IOSTANDARD  DIFF_POD12 [get_ports "DDR4_C2_DQS7_T"] ;# Bank  42 VCCO - VCC1V2_FPGA - IO_L22P_T3U_N6_DBC_AD0P_42
# set_property PACKAGE_PIN AV40     [get_ports "DDR4_C2_DQ59"] ;# Bank  42 VCCO - VCC1V2_FPGA - IO_L21N_T3L_N5_AD8N_42
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C2_DQ59"] ;# Bank  42 VCCO - VCC1V2_FPGA - IO_L21N_T3L_N5_AD8N_42
# set_property PACKAGE_PIN AU40     [get_ports "DDR4_C2_DQ58"] ;# Bank  42 VCCO - VCC1V2_FPGA - IO_L21P_T3L_N4_AD8P_42
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C2_DQ58"] ;# Bank  42 VCCO - VCC1V2_FPGA - IO_L21P_T3L_N4_AD8P_42
# set_property PACKAGE_PIN AW36     [get_ports "DDR4_C2_DQ57"] ;# Bank  42 VCCO - VCC1V2_FPGA - IO_L20N_T3L_N3_AD1N_42
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C2_DQ57"] ;# Bank  42 VCCO - VCC1V2_FPGA - IO_L20N_T3L_N3_AD1N_42
# set_property PACKAGE_PIN AW35     [get_ports "DDR4_C2_DQ56"] ;# Bank  42 VCCO - VCC1V2_FPGA - IO_L20P_T3L_N2_AD1P_42
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C2_DQ56"] ;# Bank  42 VCCO - VCC1V2_FPGA - IO_L20P_T3L_N2_AD1P_42
# set_property PACKAGE_PIN AV36     [get_ports "GPIO_LED6"] ;# Bank  42 VCCO - VCC1V2_FPGA - IO_L19N_T3L_N1_DBC_AD9N_42
# set_property IOSTANDARD  LVCMOS12 [get_ports "GPIO_LED6"] ;# Bank  42 VCCO - VCC1V2_FPGA - IO_L19N_T3L_N1_DBC_AD9N_42
# set_property PACKAGE_PIN AV35     [get_ports "DDR4_C2_DM7"] ;# Bank  42 VCCO - VCC1V2_FPGA - IO_L19P_T3L_N0_DBC_AD9P_42
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C2_DM7"] ;# Bank  42 VCCO - VCC1V2_FPGA - IO_L19P_T3L_N0_DBC_AD9P_42
# set_property PACKAGE_PIN AU37     [get_ports "GPIO_LED5"] ;# Bank  42 VCCO - VCC1V2_FPGA - IO_T3U_N12_42
# set_property IOSTANDARD  LVCMOS12 [get_ports "GPIO_LED5"] ;# Bank  42 VCCO - VCC1V2_FPGA - IO_T3U_N12_42
# set_property PACKAGE_PIN AY35     [get_ports "DDR4_C2_TEN"] ;# Bank  42 VCCO - VCC1V2_FPGA - IO_T2U_N12_42
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C2_TEN"] ;# Bank  42 VCCO - VCC1V2_FPGA - IO_T2U_N12_42
# set_property PACKAGE_PIN AY39     [get_ports "DDR4_C2_DQ55"] ;# Bank  42 VCCO - VCC1V2_FPGA - IO_L18N_T2U_N11_AD2N_42
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C2_DQ55"] ;# Bank  42 VCCO - VCC1V2_FPGA - IO_L18N_T2U_N11_AD2N_42
# set_property PACKAGE_PIN AY38     [get_ports "DDR4_C2_DQ54"] ;# Bank  42 VCCO - VCC1V2_FPGA - IO_L18P_T2U_N10_AD2P_42
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C2_DQ54"] ;# Bank  42 VCCO - VCC1V2_FPGA - IO_L18P_T2U_N10_AD2P_42
# set_property PACKAGE_PIN AY40     [get_ports "DDR4_C2_DQ53"] ;# Bank  42 VCCO - VCC1V2_FPGA - IO_L17N_T2U_N9_AD10N_42
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C2_DQ53"] ;# Bank  42 VCCO - VCC1V2_FPGA - IO_L17N_T2U_N9_AD10N_42
# set_property PACKAGE_PIN AW40     [get_ports "DDR4_C2_DQ52"] ;# Bank  42 VCCO - VCC1V2_FPGA - IO_L17P_T2U_N8_AD10P_42
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C2_DQ52"] ;# Bank  42 VCCO - VCC1V2_FPGA - IO_L17P_T2U_N8_AD10P_42
# set_property PACKAGE_PIN BA36     [get_ports "DDR4_C2_DQS6_C"] ;# Bank  42 VCCO - VCC1V2_FPGA - IO_L16N_T2U_N7_QBC_AD3N_42
# set_property IOSTANDARD  DIFF_POD12 [get_ports "DDR4_C2_DQS6_C"] ;# Bank  42 VCCO - VCC1V2_FPGA - IO_L16N_T2U_N7_QBC_AD3N_42
# set_property PACKAGE_PIN BA35     [get_ports "DDR4_C2_DQS6_T"] ;# Bank  42 VCCO - VCC1V2_FPGA - IO_L16P_T2U_N6_QBC_AD3P_42
# set_property IOSTANDARD  DIFF_POD12 [get_ports "DDR4_C2_DQS6_T"] ;# Bank  42 VCCO - VCC1V2_FPGA - IO_L16P_T2U_N6_QBC_AD3P_42
# set_property PACKAGE_PIN BA40     [get_ports "DDR4_C2_DQ51"] ;# Bank  42 VCCO - VCC1V2_FPGA - IO_L15N_T2L_N5_AD11N_42
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C2_DQ51"] ;# Bank  42 VCCO - VCC1V2_FPGA - IO_L15N_T2L_N5_AD11N_42
# set_property PACKAGE_PIN BA39     [get_ports "DDR4_C2_DQ50"] ;# Bank  42 VCCO - VCC1V2_FPGA - IO_L15P_T2L_N4_AD11P_42
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C2_DQ50"] ;# Bank  42 VCCO - VCC1V2_FPGA - IO_L15P_T2L_N4_AD11P_42
# set_property PACKAGE_PIN BB37     [get_ports "DDR4_C2_DQ49"] ;# Bank  42 VCCO - VCC1V2_FPGA - IO_L14N_T2L_N3_GC_42
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C2_DQ49"] ;# Bank  42 VCCO - VCC1V2_FPGA - IO_L14N_T2L_N3_GC_42
# set_property PACKAGE_PIN BB36     [get_ports "DDR4_C2_DQ48"] ;# Bank  42 VCCO - VCC1V2_FPGA - IO_L14P_T2L_N2_GC_42
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C2_DQ48"] ;# Bank  42 VCCO - VCC1V2_FPGA - IO_L14P_T2L_N2_GC_42
# set_property PACKAGE_PIN BA37     [get_ports "GPIO_LED7"] ;# Bank  42 VCCO - VCC1V2_FPGA - IO_L13N_T2L_N1_GC_QBC_42
# set_property IOSTANDARD  LVCMOS12 [get_ports "GPIO_LED7"] ;# Bank  42 VCCO - VCC1V2_FPGA - IO_L13N_T2L_N1_GC_QBC_42
# set_property PACKAGE_PIN AY37     [get_ports "DDR4_C2_DM6"] ;# Bank  42 VCCO - VCC1V2_FPGA - IO_L13P_T2L_N0_GC_QBC_42
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C2_DM6"] ;# Bank  42 VCCO - VCC1V2_FPGA - IO_L13P_T2L_N0_GC_QBC_42
# set_property PACKAGE_PIN BD38     [get_ports "DDR4_C2_DQ47"] ;# Bank  42 VCCO - VCC1V2_FPGA - IO_L12N_T1U_N11_GC_42
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C2_DQ47"] ;# Bank  42 VCCO - VCC1V2_FPGA - IO_L12N_T1U_N11_GC_42
# set_property PACKAGE_PIN BC38     [get_ports "DDR4_C2_DQ46"] ;# Bank  42 VCCO - VCC1V2_FPGA - IO_L12P_T1U_N10_GC_42
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C2_DQ46"] ;# Bank  42 VCCO - VCC1V2_FPGA - IO_L12P_T1U_N10_GC_42
# set_property PACKAGE_PIN BB39     [get_ports "DDR4_C2_DQ45"] ;# Bank  42 VCCO - VCC1V2_FPGA - IO_L11N_T1U_N9_GC_42
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C2_DQ45"] ;# Bank  42 VCCO - VCC1V2_FPGA - IO_L11N_T1U_N9_GC_42
# set_property PACKAGE_PIN BB38     [get_ports "DDR4_C2_DQ44"] ;# Bank  42 VCCO - VCC1V2_FPGA - IO_L11P_T1U_N8_GC_42
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C2_DQ44"] ;# Bank  42 VCCO - VCC1V2_FPGA - IO_L11P_T1U_N8_GC_42
# set_property PACKAGE_PIN BF39     [get_ports "DDR4_C2_DQS5_C"] ;# Bank  42 VCCO - VCC1V2_FPGA - IO_L10N_T1U_N7_QBC_AD4N_42
# set_property IOSTANDARD  DIFF_POD12 [get_ports "DDR4_C2_DQS5_C"] ;# Bank  42 VCCO - VCC1V2_FPGA - IO_L10N_T1U_N7_QBC_AD4N_42
# set_property PACKAGE_PIN BE39     [get_ports "DDR4_C2_DQS5_T"] ;# Bank  42 VCCO - VCC1V2_FPGA - IO_L10P_T1U_N6_QBC_AD4P_42
# set_property IOSTANDARD  DIFF_POD12 [get_ports "DDR4_C2_DQS5_T"] ;# Bank  42 VCCO - VCC1V2_FPGA - IO_L10P_T1U_N6_QBC_AD4P_42
# set_property PACKAGE_PIN BD40     [get_ports "DDR4_C2_DQ43"] ;# Bank  42 VCCO - VCC1V2_FPGA - IO_L9N_T1L_N5_AD12N_42
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C2_DQ43"] ;# Bank  42 VCCO - VCC1V2_FPGA - IO_L9N_T1L_N5_AD12N_42
# set_property PACKAGE_PIN BC39     [get_ports "DDR4_C2_DQ42"] ;# Bank  42 VCCO - VCC1V2_FPGA - IO_L9P_T1L_N4_AD12P_42
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C2_DQ42"] ;# Bank  42 VCCO - VCC1V2_FPGA - IO_L9P_T1L_N4_AD12P_42
# set_property PACKAGE_PIN BE38     [get_ports "DDR4_C2_DQ41"] ;# Bank  42 VCCO - VCC1V2_FPGA - IO_L8N_T1L_N3_AD5N_42
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C2_DQ41"] ;# Bank  42 VCCO - VCC1V2_FPGA - IO_L8N_T1L_N3_AD5N_42
# set_property PACKAGE_PIN BD37     [get_ports "DDR4_C2_DQ40"] ;# Bank  42 VCCO - VCC1V2_FPGA - IO_L8P_T1L_N2_AD5P_42
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C2_DQ40"] ;# Bank  42 VCCO - VCC1V2_FPGA - IO_L8P_T1L_N2_AD5P_42
# set_property PACKAGE_PIN BF40     [get_ports "MAXIM_CABLE_LS_B"] ;# Bank  42 VCCO - VCC1V2_FPGA - IO_L7N_T1L_N1_QBC_AD13N_42
# set_property IOSTANDARD  LVCMOS12 [get_ports "MAXIM_CABLE_LS_B"] ;# Bank  42 VCCO - VCC1V2_FPGA - IO_L7N_T1L_N1_QBC_AD13N_42
# set_property PACKAGE_PIN BE40     [get_ports "DDR4_C2_DM5"] ;# Bank  42 VCCO - VCC1V2_FPGA - IO_L7P_T1L_N0_QBC_AD13P_42
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C2_DM5"] ;# Bank  42 VCCO - VCC1V2_FPGA - IO_L7P_T1L_N0_QBC_AD13P_42
# set_property PACKAGE_PIN BC40     [get_ports "FAN_OT_LS_B"] ;# Bank  42 VCCO - VCC1V2_FPGA - IO_T1U_N12_42
# set_property IOSTANDARD  LVCMOS12 [get_ports "FAN_OT_LS_B"] ;# Bank  42 VCCO - VCC1V2_FPGA - IO_T1U_N12_42
# #set_property PACKAGE_PIN BB34     [get_ports "VRP_42"] ;# Bank  42 VCCO - VCC1V2_FPGA - IO_T0U_N12_VRP_42
# #set_property IOSTANDARD  LVCMOSxx [get_ports "VRP_42"] ;# Bank  42 VCCO - VCC1V2_FPGA - IO_T0U_N12_VRP_42
# set_property PACKAGE_PIN BF37     [get_ports "DDR4_C2_DQ39"] ;# Bank  42 VCCO - VCC1V2_FPGA - IO_L6N_T0U_N11_AD6N_42
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C2_DQ39"] ;# Bank  42 VCCO - VCC1V2_FPGA - IO_L6N_T0U_N11_AD6N_42
# set_property PACKAGE_PIN BF36     [get_ports "DDR4_C2_DQ38"] ;# Bank  42 VCCO - VCC1V2_FPGA - IO_L6P_T0U_N10_AD6P_42
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C2_DQ38"] ;# Bank  42 VCCO - VCC1V2_FPGA - IO_L6P_T0U_N10_AD6P_42
# set_property PACKAGE_PIN BE37     [get_ports "DDR4_C2_DQ37"] ;# Bank  42 VCCO - VCC1V2_FPGA - IO_L5N_T0U_N9_AD14N_42
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C2_DQ37"] ;# Bank  42 VCCO - VCC1V2_FPGA - IO_L5N_T0U_N9_AD14N_42
# set_property PACKAGE_PIN BD36     [get_ports "DDR4_C2_DQ36"] ;# Bank  42 VCCO - VCC1V2_FPGA - IO_L5P_T0U_N8_AD14P_42
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C2_DQ36"] ;# Bank  42 VCCO - VCC1V2_FPGA - IO_L5P_T0U_N8_AD14P_42
# set_property PACKAGE_PIN BF35     [get_ports "DDR4_C2_DQS4_C"] ;# Bank  42 VCCO - VCC1V2_FPGA - IO_L4N_T0U_N7_DBC_AD7N_42
# set_property IOSTANDARD  DIFF_POD12 [get_ports "DDR4_C2_DQS4_C"] ;# Bank  42 VCCO - VCC1V2_FPGA - IO_L4N_T0U_N7_DBC_AD7N_42
# set_property PACKAGE_PIN BE35     [get_ports "DDR4_C2_DQS4_T"] ;# Bank  42 VCCO - VCC1V2_FPGA - IO_L4P_T0U_N6_DBC_AD7P_42
# set_property IOSTANDARD  DIFF_POD12 [get_ports "DDR4_C2_DQS4_T"] ;# Bank  42 VCCO - VCC1V2_FPGA - IO_L4P_T0U_N6_DBC_AD7P_42
# set_property PACKAGE_PIN BC36     [get_ports "DDR4_C2_DQ35"] ;# Bank  42 VCCO - VCC1V2_FPGA - IO_L3N_T0L_N5_AD15N_42
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C2_DQ35"] ;# Bank  42 VCCO - VCC1V2_FPGA - IO_L3N_T0L_N5_AD15N_42
# set_property PACKAGE_PIN BC35     [get_ports "DDR4_C2_DQ34"] ;# Bank  42 VCCO - VCC1V2_FPGA - IO_L3P_T0L_N4_AD15P_42
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C2_DQ34"] ;# Bank  42 VCCO - VCC1V2_FPGA - IO_L3P_T0L_N4_AD15P_42
# set_property PACKAGE_PIN BF34     [get_ports "DDR4_C2_DQ33"] ;# Bank  42 VCCO - VCC1V2_FPGA - IO_L2N_T0L_N3_42
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C2_DQ33"] ;# Bank  42 VCCO - VCC1V2_FPGA - IO_L2N_T0L_N3_42
# set_property PACKAGE_PIN BE34     [get_ports "DDR4_C2_DQ32"] ;# Bank  42 VCCO - VCC1V2_FPGA - IO_L2P_T0L_N2_42
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C2_DQ32"] ;# Bank  42 VCCO - VCC1V2_FPGA - IO_L2P_T0L_N2_42
# set_property PACKAGE_PIN BD35     [get_ports "DDR4_C2_RESET_B"] ;# Bank  42 VCCO - VCC1V2_FPGA - IO_L1N_T0L_N1_DBC_42
# set_property IOSTANDARD  LVCMOS12 [get_ports "DDR4_C2_RESET_B"] ;# Bank  42 VCCO - VCC1V2_FPGA - IO_L1N_T0L_N1_DBC_42
# set_property PACKAGE_PIN BC34     [get_ports "DDR4_C2_DM4"] ;# Bank  42 VCCO - VCC1V2_FPGA - IO_L1P_T0L_N0_DBC_42
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C2_DM4"] ;# Bank  42 VCCO - VCC1V2_FPGA - IO_L1P_T0L_N0_DBC_42
# #Other net   PACKAGE_PIN AU36     - 5N11683                   Bank  42 - VREF_42
# set_property PACKAGE_PIN AM27     [get_ports "DDR4_C2_A0"] ;# Bank  41 VCCO - VCC1V2_FPGA - IO_L24N_T3U_N11_41
# set_property IOSTANDARD  SSTL12 [get_ports "DDR4_C2_A0"] ;# Bank  41 VCCO - VCC1V2_FPGA - IO_L24N_T3U_N11_41
# set_property PACKAGE_PIN AL27     [get_ports "DDR4_C2_A1"] ;# Bank  41 VCCO - VCC1V2_FPGA - IO_L24P_T3U_N10_41
# set_property IOSTANDARD  SSTL12 [get_ports "DDR4_C2_A1"] ;# Bank  41 VCCO - VCC1V2_FPGA - IO_L24P_T3U_N10_41
# set_property PACKAGE_PIN AP26     [get_ports "DDR4_C2_A2"] ;# Bank  41 VCCO - VCC1V2_FPGA - IO_L23N_T3U_N9_41
# set_property IOSTANDARD  SSTL12 [get_ports "DDR4_C2_A2"] ;# Bank  41 VCCO - VCC1V2_FPGA - IO_L23N_T3U_N9_41
# set_property PACKAGE_PIN AP25     [get_ports "DDR4_C2_A3"] ;# Bank  41 VCCO - VCC1V2_FPGA - IO_L23P_T3U_N8_41
# set_property IOSTANDARD  SSTL12 [get_ports "DDR4_C2_A3"] ;# Bank  41 VCCO - VCC1V2_FPGA - IO_L23P_T3U_N8_41
# set_property PACKAGE_PIN AN28     [get_ports "DDR4_C2_A4"] ;# Bank  41 VCCO - VCC1V2_FPGA - IO_L22N_T3U_N7_DBC_AD0N_41
# set_property IOSTANDARD  SSTL12 [get_ports "DDR4_C2_A4"] ;# Bank  41 VCCO - VCC1V2_FPGA - IO_L22N_T3U_N7_DBC_AD0N_41
# set_property PACKAGE_PIN AM28     [get_ports "DDR4_C2_A5"] ;# Bank  41 VCCO - VCC1V2_FPGA - IO_L22P_T3U_N6_DBC_AD0P_41
# set_property IOSTANDARD  SSTL12 [get_ports "DDR4_C2_A5"] ;# Bank  41 VCCO - VCC1V2_FPGA - IO_L22P_T3U_N6_DBC_AD0P_41
# set_property PACKAGE_PIN AP28     [get_ports "DDR4_C2_A6"] ;# Bank  41 VCCO - VCC1V2_FPGA - IO_L21N_T3L_N5_AD8N_41
# set_property IOSTANDARD  SSTL12 [get_ports "DDR4_C2_A6"] ;# Bank  41 VCCO - VCC1V2_FPGA - IO_L21N_T3L_N5_AD8N_41
# set_property PACKAGE_PIN AP27     [get_ports "DDR4_C2_A7"] ;# Bank  41 VCCO - VCC1V2_FPGA - IO_L21P_T3L_N4_AD8P_41
# set_property IOSTANDARD  SSTL12 [get_ports "DDR4_C2_A7"] ;# Bank  41 VCCO - VCC1V2_FPGA - IO_L21P_T3L_N4_AD8P_41
# set_property PACKAGE_PIN AN26     [get_ports "DDR4_C2_A8"] ;# Bank  41 VCCO - VCC1V2_FPGA - IO_L20N_T3L_N3_AD1N_41
# set_property IOSTANDARD  SSTL12 [get_ports "DDR4_C2_A8"] ;# Bank  41 VCCO - VCC1V2_FPGA - IO_L20N_T3L_N3_AD1N_41
# set_property PACKAGE_PIN AM26     [get_ports "DDR4_C2_A9"] ;# Bank  41 VCCO - VCC1V2_FPGA - IO_L20P_T3L_N2_AD1P_41
# set_property IOSTANDARD  SSTL12 [get_ports "DDR4_C2_A9"] ;# Bank  41 VCCO - VCC1V2_FPGA - IO_L20P_T3L_N2_AD1P_41
# set_property PACKAGE_PIN AR28     [get_ports "DDR4_C2_A10"] ;# Bank  41 VCCO - VCC1V2_FPGA - IO_L19N_T3L_N1_DBC_AD9N_41
# set_property IOSTANDARD  SSTL12 [get_ports "DDR4_C2_A10"] ;# Bank  41 VCCO - VCC1V2_FPGA - IO_L19N_T3L_N1_DBC_AD9N_41
# set_property PACKAGE_PIN AR27     [get_ports "DDR4_C2_A11"] ;# Bank  41 VCCO - VCC1V2_FPGA - IO_L19P_T3L_N0_DBC_AD9P_41
# set_property IOSTANDARD  SSTL12 [get_ports "DDR4_C2_A11"] ;# Bank  41 VCCO - VCC1V2_FPGA - IO_L19P_T3L_N0_DBC_AD9P_41
# set_property PACKAGE_PIN AN25     [get_ports "DDR4_C2_ACT_B"] ;# Bank  41 VCCO - VCC1V2_FPGA - IO_T3U_N12_41
# set_property IOSTANDARD  SSTL12 [get_ports "DDR4_C2_ACT_B"] ;# Bank  41 VCCO - VCC1V2_FPGA - IO_T3U_N12_41
# set_property PACKAGE_PIN AV25     [get_ports "DDR4_C2_A12"] ;# Bank  41 VCCO - VCC1V2_FPGA - IO_T2U_N12_41
# set_property IOSTANDARD  SSTL12 [get_ports "DDR4_C2_A12"] ;# Bank  41 VCCO - VCC1V2_FPGA - IO_T2U_N12_41
# set_property PACKAGE_PIN AT25     [get_ports "DDR4_C2_A13"] ;# Bank  41 VCCO - VCC1V2_FPGA - IO_L18N_T2U_N11_AD2N_41
# set_property IOSTANDARD  SSTL12 [get_ports "DDR4_C2_A13"] ;# Bank  41 VCCO - VCC1V2_FPGA - IO_L18N_T2U_N11_AD2N_41
# set_property PACKAGE_PIN AR25     [get_ports "DDR4_C2_BA0"] ;# Bank  41 VCCO - VCC1V2_FPGA - IO_L18P_T2U_N10_AD2P_41
# set_property IOSTANDARD  SSTL12 [get_ports "DDR4_C2_BA0"] ;# Bank  41 VCCO - VCC1V2_FPGA - IO_L18P_T2U_N10_AD2P_41
# set_property PACKAGE_PIN AU28     [get_ports "DDR4_C2_BA1"] ;# Bank  41 VCCO - VCC1V2_FPGA - IO_L17N_T2U_N9_AD10N_41
# set_property IOSTANDARD  SSTL12 [get_ports "DDR4_C2_BA1"] ;# Bank  41 VCCO - VCC1V2_FPGA - IO_L17N_T2U_N9_AD10N_41
# set_property PACKAGE_PIN AU27     [get_ports "DDR4_C2_BG0"] ;# Bank  41 VCCO - VCC1V2_FPGA - IO_L17P_T2U_N8_AD10P_41
# set_property IOSTANDARD  SSTL12 [get_ports "DDR4_C2_BG0"] ;# Bank  41 VCCO - VCC1V2_FPGA - IO_L17P_T2U_N8_AD10P_41
# set_property PACKAGE_PIN AT27     [get_ports "DDR4_C2_CK_C"] ;# Bank  41 VCCO - VCC1V2_FPGA - IO_L16N_T2U_N7_QBC_AD3N_41
# set_property IOSTANDARD  DIFF_POD12 [get_ports "DDR4_C2_CK_C"] ;# Bank  41 VCCO - VCC1V2_FPGA - IO_L16N_T2U_N7_QBC_AD3N_41
# set_property PACKAGE_PIN AT26     [get_ports "DDR4_C2_CK_T"] ;# Bank  41 VCCO - VCC1V2_FPGA - IO_L16P_T2U_N6_QBC_AD3P_41
# set_property IOSTANDARD  DIFF_POD12 [get_ports "DDR4_C2_CK_T"] ;# Bank  41 VCCO - VCC1V2_FPGA - IO_L16P_T2U_N6_QBC_AD3P_41
# set_property PACKAGE_PIN AW28     [get_ports "DDR4_C2_CKE"] ;# Bank  41 VCCO - VCC1V2_FPGA - IO_L15N_T2L_N5_AD11N_41
# set_property IOSTANDARD  SSTL12 [get_ports "DDR4_C2_CKE"] ;# Bank  41 VCCO - VCC1V2_FPGA - IO_L15N_T2L_N5_AD11N_41
# set_property PACKAGE_PIN AV28     [get_ports "DDR4_C2_A14_WE_B"] ;# Bank  41 VCCO - VCC1V2_FPGA - IO_L15P_T2L_N4_AD11P_41
# set_property IOSTANDARD  SSTL12 [get_ports "DDR4_C2_A14_WE_B"] ;# Bank  41 VCCO - VCC1V2_FPGA - IO_L15P_T2L_N4_AD11P_41
# set_property PACKAGE_PIN AV26     [get_ports "DDR4_C2_A16_RAS_B"] ;# Bank  41 VCCO - VCC1V2_FPGA - IO_L14N_T2L_N3_GC_41
# set_property IOSTANDARD  SSTL12 [get_ports "DDR4_C2_A16_RAS_B"] ;# Bank  41 VCCO - VCC1V2_FPGA - IO_L14N_T2L_N3_GC_41
# set_property PACKAGE_PIN AU26     [get_ports "DDR4_C2_A15_CAS_B"] ;# Bank  41 VCCO - VCC1V2_FPGA - IO_L14P_T2L_N2_GC_41
# set_property IOSTANDARD  SSTL12 [get_ports "DDR4_C2_A15_CAS_B"] ;# Bank  41 VCCO - VCC1V2_FPGA - IO_L14P_T2L_N2_GC_41
# set_property PACKAGE_PIN AW27     [get_ports "250MHZ_CLK2_N"] ;# Bank  41 VCCO - VCC1V2_FPGA - IO_L13N_T2L_N1_GC_QBC_41
# set_property IOSTANDARD  DIFF_SSTL12 [get_ports "250MHZ_CLK2_N"] ;# Bank  41 VCCO - VCC1V2_FPGA - IO_L13N_T2L_N1_GC_QBC_41
# set_property PACKAGE_PIN AW26     [get_ports "250MHZ_CLK2_P"] ;# Bank  41 VCCO - VCC1V2_FPGA - IO_L13P_T2L_N0_GC_QBC_41
# set_property IOSTANDARD  DIFF_SSTL12 [get_ports "250MHZ_CLK2_P"] ;# Bank  41 VCCO - VCC1V2_FPGA - IO_L13P_T2L_N0_GC_QBC_41
# set_property PACKAGE_PIN BB27     [get_ports "DDR4_C2_DQ79"] ;# Bank  41 VCCO - VCC1V2_FPGA - IO_L12N_T1U_N11_GC_41
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C2_DQ79"] ;# Bank  41 VCCO - VCC1V2_FPGA - IO_L12N_T1U_N11_GC_41
# set_property PACKAGE_PIN BA27     [get_ports "DDR4_C2_DQ78"] ;# Bank  41 VCCO - VCC1V2_FPGA - IO_L12P_T1U_N10_GC_41
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C2_DQ78"] ;# Bank  41 VCCO - VCC1V2_FPGA - IO_L12P_T1U_N10_GC_41
# set_property PACKAGE_PIN AY28     [get_ports "DDR4_C2_DQ77"] ;# Bank  41 VCCO - VCC1V2_FPGA - IO_L11N_T1U_N9_GC_41
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C2_DQ77"] ;# Bank  41 VCCO - VCC1V2_FPGA - IO_L11N_T1U_N9_GC_41
# set_property PACKAGE_PIN AY27     [get_ports "DDR4_C2_DQ76"] ;# Bank  41 VCCO - VCC1V2_FPGA - IO_L11P_T1U_N8_GC_41
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C2_DQ76"] ;# Bank  41 VCCO - VCC1V2_FPGA - IO_L11P_T1U_N8_GC_41
# set_property PACKAGE_PIN BB26     [get_ports "DDR4_C2_DQS9_C"] ;# Bank  41 VCCO - VCC1V2_FPGA - IO_L10N_T1U_N7_QBC_AD4N_41
# set_property IOSTANDARD  DIFF_POD12 [get_ports "DDR4_C2_DQS9_C"] ;# Bank  41 VCCO - VCC1V2_FPGA - IO_L10N_T1U_N7_QBC_AD4N_41
# set_property PACKAGE_PIN BA26     [get_ports "DDR4_C2_DQS9_T"] ;# Bank  41 VCCO - VCC1V2_FPGA - IO_L10P_T1U_N6_QBC_AD4P_41
# set_property IOSTANDARD  DIFF_POD12 [get_ports "DDR4_C2_DQS9_T"] ;# Bank  41 VCCO - VCC1V2_FPGA - IO_L10P_T1U_N6_QBC_AD4P_41
# set_property PACKAGE_PIN BC28     [get_ports "DDR4_C2_DQ75"] ;# Bank  41 VCCO - VCC1V2_FPGA - IO_L9N_T1L_N5_AD12N_41
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C2_DQ75"] ;# Bank  41 VCCO - VCC1V2_FPGA - IO_L9N_T1L_N5_AD12N_41
# set_property PACKAGE_PIN BB28     [get_ports "DDR4_C2_DQ74"] ;# Bank  41 VCCO - VCC1V2_FPGA - IO_L9P_T1L_N4_AD12P_41
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C2_DQ74"] ;# Bank  41 VCCO - VCC1V2_FPGA - IO_L9P_T1L_N4_AD12P_41
# set_property PACKAGE_PIN BC26     [get_ports "DDR4_C2_DQ73"] ;# Bank  41 VCCO - VCC1V2_FPGA - IO_L8N_T1L_N3_AD5N_41
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C2_DQ73"] ;# Bank  41 VCCO - VCC1V2_FPGA - IO_L8N_T1L_N3_AD5N_41
# set_property PACKAGE_PIN BC25     [get_ports "DDR4_C2_DQ72"] ;# Bank  41 VCCO - VCC1V2_FPGA - IO_L8P_T1L_N2_AD5P_41
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C2_DQ72"] ;# Bank  41 VCCO - VCC1V2_FPGA - IO_L8P_T1L_N2_AD5P_41
# set_property PACKAGE_PIN BB29     [get_ports "DDR4_C2_ODT"] ;# Bank  41 VCCO - VCC1V2_FPGA - IO_L7N_T1L_N1_QBC_AD13N_41
# set_property IOSTANDARD  SSTL12 [get_ports "DDR4_C2_ODT"] ;# Bank  41 VCCO - VCC1V2_FPGA - IO_L7N_T1L_N1_QBC_AD13N_41
# set_property PACKAGE_PIN BA29     [get_ports "DDR4_C2_DM9"] ;# Bank  41 VCCO - VCC1V2_FPGA - IO_L7P_T1L_N0_QBC_AD13P_41
# set_property IOSTANDARD  SSTL12 [get_ports "DDR4_C2_DM9"] ;# Bank  41 VCCO - VCC1V2_FPGA - IO_L7P_T1L_N0_QBC_AD13P_41
# set_property PACKAGE_PIN AY29     [get_ports "DDR4_C2_CS_B"] ;# Bank  41 VCCO - VCC1V2_FPGA - IO_T1U_N12_41
# set_property IOSTANDARD  SSTL12 [get_ports "DDR4_C2_CS_B"] ;# Bank  41 VCCO - VCC1V2_FPGA - IO_T1U_N12_41
# #set_property PACKAGE_PIN BC29     [get_ports "VRP_41"] ;# Bank  41 VCCO - VCC1V2_FPGA - IO_T0U_N12_VRP_41
# #set_property IOSTANDARD  LVCMOSxx [get_ports "VRP_41"] ;# Bank  41 VCCO - VCC1V2_FPGA - IO_T0U_N12_VRP_41
# set_property PACKAGE_PIN BD26     [get_ports "DDR4_C2_DQ71"] ;# Bank  41 VCCO - VCC1V2_FPGA - IO_L6N_T0U_N11_AD6N_41
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C2_DQ71"] ;# Bank  41 VCCO - VCC1V2_FPGA - IO_L6N_T0U_N11_AD6N_41
# set_property PACKAGE_PIN BD25     [get_ports "DDR4_C2_DQ70"] ;# Bank  41 VCCO - VCC1V2_FPGA - IO_L6P_T0U_N10_AD6P_41
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C2_DQ70"] ;# Bank  41 VCCO - VCC1V2_FPGA - IO_L6P_T0U_N10_AD6P_41
# set_property PACKAGE_PIN BE27     [get_ports "DDR4_C2_DQ69"] ;# Bank  41 VCCO - VCC1V2_FPGA - IO_L5N_T0U_N9_AD14N_41
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C2_DQ69"] ;# Bank  41 VCCO - VCC1V2_FPGA - IO_L5N_T0U_N9_AD14N_41
# set_property PACKAGE_PIN BD27     [get_ports "DDR4_C2_DQ68"] ;# Bank  41 VCCO - VCC1V2_FPGA - IO_L5P_T0U_N8_AD14P_41
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C2_DQ68"] ;# Bank  41 VCCO - VCC1V2_FPGA - IO_L5P_T0U_N8_AD14P_41
# set_property PACKAGE_PIN BF25     [get_ports "DDR4_C2_DQS8_C"] ;# Bank  41 VCCO - VCC1V2_FPGA - IO_L4N_T0U_N7_DBC_AD7N_41
# set_property IOSTANDARD  DIFF_POD12 [get_ports "DDR4_C2_DQS8_C"] ;# Bank  41 VCCO - VCC1V2_FPGA - IO_L4N_T0U_N7_DBC_AD7N_41
# set_property PACKAGE_PIN BE25     [get_ports "DDR4_C2_DQS8_T"] ;# Bank  41 VCCO - VCC1V2_FPGA - IO_L4P_T0U_N6_DBC_AD7P_41
# set_property IOSTANDARD  DIFF_POD12 [get_ports "DDR4_C2_DQS8_T"] ;# Bank  41 VCCO - VCC1V2_FPGA - IO_L4P_T0U_N6_DBC_AD7P_41
# set_property PACKAGE_PIN BE28     [get_ports "DDR4_C2_DQ67"] ;# Bank  41 VCCO - VCC1V2_FPGA - IO_L3N_T0L_N5_AD15N_41
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C2_DQ67"] ;# Bank  41 VCCO - VCC1V2_FPGA - IO_L3N_T0L_N5_AD15N_41
# set_property PACKAGE_PIN BD28     [get_ports "DDR4_C2_DQ66"] ;# Bank  41 VCCO - VCC1V2_FPGA - IO_L3P_T0L_N4_AD15P_41
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C2_DQ66"] ;# Bank  41 VCCO - VCC1V2_FPGA - IO_L3P_T0L_N4_AD15P_41
# set_property PACKAGE_PIN BF27     [get_ports "DDR4_C2_DQ65"] ;# Bank  41 VCCO - VCC1V2_FPGA - IO_L2N_T0L_N3_41
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C2_DQ65"] ;# Bank  41 VCCO - VCC1V2_FPGA - IO_L2N_T0L_N3_41
# set_property PACKAGE_PIN BF26     [get_ports "DDR4_C2_DQ64"] ;# Bank  41 VCCO - VCC1V2_FPGA - IO_L2P_T0L_N2_41
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C2_DQ64"] ;# Bank  41 VCCO - VCC1V2_FPGA - IO_L2P_T0L_N2_41
# set_property PACKAGE_PIN BF29     [get_ports "DDR4_C2_PAR"] ;# Bank  41 VCCO - VCC1V2_FPGA - IO_L1N_T0L_N1_DBC_41
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C2_PAR"] ;# Bank  41 VCCO - VCC1V2_FPGA - IO_L1N_T0L_N1_DBC_41
# set_property PACKAGE_PIN BE29     [get_ports "DDR4_C2_DM8"] ;# Bank  41 VCCO - VCC1V2_FPGA - IO_L1P_T0L_N0_DBC_41
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C2_DM8"] ;# Bank  41 VCCO - VCC1V2_FPGA - IO_L1P_T0L_N0_DBC_41
# #Other net   PACKAGE_PIN AL26     - 6N5608                    Bank  41 - VREF_41
# set_property PACKAGE_PIN AN31     [get_ports "DDR4_C2_DQ31"] ;# Bank  40 VCCO - VCC1V2_FPGA - IO_L24N_T3U_N11_40
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C2_DQ31"] ;# Bank  40 VCCO - VCC1V2_FPGA - IO_L24N_T3U_N11_40
# set_property PACKAGE_PIN AN30     [get_ports "DDR4_C2_DQ30"] ;# Bank  40 VCCO - VCC1V2_FPGA - IO_L24P_T3U_N10_40
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C2_DQ30"] ;# Bank  40 VCCO - VCC1V2_FPGA - IO_L24P_T3U_N10_40
# set_property PACKAGE_PIN AR30     [get_ports "DDR4_C2_DQ29"] ;# Bank  40 VCCO - VCC1V2_FPGA - IO_L23N_T3U_N9_40
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C2_DQ29"] ;# Bank  40 VCCO - VCC1V2_FPGA - IO_L23N_T3U_N9_40
# set_property PACKAGE_PIN AP30     [get_ports "DDR4_C2_DQ28"] ;# Bank  40 VCCO - VCC1V2_FPGA - IO_L23P_T3U_N8_40
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C2_DQ28"] ;# Bank  40 VCCO - VCC1V2_FPGA - IO_L23P_T3U_N8_40
# set_property PACKAGE_PIN AP32     [get_ports "DDR4_C2_DQS3_C"] ;# Bank  40 VCCO - VCC1V2_FPGA - IO_L22N_T3U_N7_DBC_AD0N_40
# set_property IOSTANDARD  DIFF_POD12 [get_ports "DDR4_C2_DQS3_C"] ;# Bank  40 VCCO - VCC1V2_FPGA - IO_L22N_T3U_N7_DBC_AD0N_40
# set_property PACKAGE_PIN AP31     [get_ports "DDR4_C2_DQS3_T"] ;# Bank  40 VCCO - VCC1V2_FPGA - IO_L22P_T3U_N6_DBC_AD0P_40
# set_property IOSTANDARD  DIFF_POD12 [get_ports "DDR4_C2_DQS3_T"] ;# Bank  40 VCCO - VCC1V2_FPGA - IO_L22P_T3U_N6_DBC_AD0P_40
# set_property PACKAGE_PIN AT30     [get_ports "DDR4_C2_DQ27"] ;# Bank  40 VCCO - VCC1V2_FPGA - IO_L21N_T3L_N5_AD8N_40
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C2_DQ27"] ;# Bank  40 VCCO - VCC1V2_FPGA - IO_L21N_T3L_N5_AD8N_40
# set_property PACKAGE_PIN AT29     [get_ports "DDR4_C2_DQ26"] ;# Bank  40 VCCO - VCC1V2_FPGA - IO_L21P_T3L_N4_AD8P_40
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C2_DQ26"] ;# Bank  40 VCCO - VCC1V2_FPGA - IO_L21P_T3L_N4_AD8P_40
# set_property PACKAGE_PIN AT34     [get_ports "DDR4_C2_DQ25"] ;# Bank  40 VCCO - VCC1V2_FPGA - IO_L20N_T3L_N3_AD1N_40
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C2_DQ25"] ;# Bank  40 VCCO - VCC1V2_FPGA - IO_L20N_T3L_N3_AD1N_40
# set_property PACKAGE_PIN AR33     [get_ports "DDR4_C2_DQ24"] ;# Bank  40 VCCO - VCC1V2_FPGA - IO_L20P_T3L_N2_AD1P_40
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C2_DQ24"] ;# Bank  40 VCCO - VCC1V2_FPGA - IO_L20P_T3L_N2_AD1P_40
# set_property PACKAGE_PIN AT32     [get_ports "GPIO_LED0"] ;# Bank  40 VCCO - VCC1V2_FPGA - IO_L19N_T3L_N1_DBC_AD9N_40
# set_property IOSTANDARD  LVCMOS12 [get_ports "GPIO_LED0"] ;# Bank  40 VCCO - VCC1V2_FPGA - IO_L19N_T3L_N1_DBC_AD9N_40
# set_property PACKAGE_PIN AR32     [get_ports "DDR4_C2_DM3"] ;# Bank  40 VCCO - VCC1V2_FPGA - IO_L19P_T3L_N0_DBC_AD9P_40
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C2_DM3"] ;# Bank  40 VCCO - VCC1V2_FPGA - IO_L19P_T3L_N0_DBC_AD9P_40
# set_property PACKAGE_PIN AR29     [get_ports "DDR4_C2_ALERT_B"] ;# Bank  40 VCCO - VCC1V2_FPGA - IO_T3U_N12_40
# set_property IOSTANDARD  SSTL12 [get_ports "DDR4_C2_ALERT_B"] ;# Bank  40 VCCO - VCC1V2_FPGA - IO_T3U_N12_40
# set_property PACKAGE_PIN AV34     [get_ports "GPIO_LED1"] ;# Bank  40 VCCO - VCC1V2_FPGA - IO_T2U_N12_40
# set_property IOSTANDARD  LVCMOS12 [get_ports "GPIO_LED1"] ;# Bank  40 VCCO - VCC1V2_FPGA - IO_T2U_N12_40
# set_property PACKAGE_PIN AV31     [get_ports "DDR4_C2_DQ23"] ;# Bank  40 VCCO - VCC1V2_FPGA - IO_L18N_T2U_N11_AD2N_40
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C2_DQ23"] ;# Bank  40 VCCO - VCC1V2_FPGA - IO_L18N_T2U_N11_AD2N_40
# set_property PACKAGE_PIN AU31     [get_ports "DDR4_C2_DQ22"] ;# Bank  40 VCCO - VCC1V2_FPGA - IO_L18P_T2U_N10_AD2P_40
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C2_DQ22"] ;# Bank  40 VCCO - VCC1V2_FPGA - IO_L18P_T2U_N10_AD2P_40
# set_property PACKAGE_PIN AU32     [get_ports "DDR4_C2_DQ21"] ;# Bank  40 VCCO - VCC1V2_FPGA - IO_L17N_T2U_N9_AD10N_40
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C2_DQ21"] ;# Bank  40 VCCO - VCC1V2_FPGA - IO_L17N_T2U_N9_AD10N_40
# set_property PACKAGE_PIN AT31     [get_ports "DDR4_C2_DQ20"] ;# Bank  40 VCCO - VCC1V2_FPGA - IO_L17P_T2U_N8_AD10P_40
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C2_DQ20"] ;# Bank  40 VCCO - VCC1V2_FPGA - IO_L17P_T2U_N8_AD10P_40
# set_property PACKAGE_PIN AV29     [get_ports "DDR4_C2_DQS2_C"] ;# Bank  40 VCCO - VCC1V2_FPGA - IO_L16N_T2U_N7_QBC_AD3N_40
# set_property IOSTANDARD  DIFF_POD12 [get_ports "DDR4_C2_DQS2_C"] ;# Bank  40 VCCO - VCC1V2_FPGA - IO_L16N_T2U_N7_QBC_AD3N_40
# set_property PACKAGE_PIN AU29     [get_ports "DDR4_C2_DQS2_T"] ;# Bank  40 VCCO - VCC1V2_FPGA - IO_L16P_T2U_N6_QBC_AD3P_40
# set_property IOSTANDARD  DIFF_POD12 [get_ports "DDR4_C2_DQS2_T"] ;# Bank  40 VCCO - VCC1V2_FPGA - IO_L16P_T2U_N6_QBC_AD3P_40
# set_property PACKAGE_PIN AU34     [get_ports "DDR4_C2_DQ19"] ;# Bank  40 VCCO - VCC1V2_FPGA - IO_L15N_T2L_N5_AD11N_40
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C2_DQ19"] ;# Bank  40 VCCO - VCC1V2_FPGA - IO_L15N_T2L_N5_AD11N_40
# set_property PACKAGE_PIN AU33     [get_ports "DDR4_C2_DQ18"] ;# Bank  40 VCCO - VCC1V2_FPGA - IO_L15P_T2L_N4_AD11P_40
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C2_DQ18"] ;# Bank  40 VCCO - VCC1V2_FPGA - IO_L15P_T2L_N4_AD11P_40
# set_property PACKAGE_PIN AW30     [get_ports "DDR4_C2_DQ17"] ;# Bank  40 VCCO - VCC1V2_FPGA - IO_L14N_T2L_N3_GC_40
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C2_DQ17"] ;# Bank  40 VCCO - VCC1V2_FPGA - IO_L14N_T2L_N3_GC_40
# set_property PACKAGE_PIN AV30     [get_ports "DDR4_C2_DQ16"] ;# Bank  40 VCCO - VCC1V2_FPGA - IO_L14P_T2L_N2_GC_40
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C2_DQ16"] ;# Bank  40 VCCO - VCC1V2_FPGA - IO_L14P_T2L_N2_GC_40
# set_property PACKAGE_PIN AW33     [get_ports "FAN_FAIL_LS_B"] ;# Bank  40 VCCO - VCC1V2_FPGA - IO_L13N_T2L_N1_GC_QBC_40
# set_property IOSTANDARD  LVCMOS12 [get_ports "FAN_FAIL_LS_B"] ;# Bank  40 VCCO - VCC1V2_FPGA - IO_L13N_T2L_N1_GC_QBC_40
# set_property PACKAGE_PIN AV33     [get_ports "DDR4_C2_DM2"] ;# Bank  40 VCCO - VCC1V2_FPGA - IO_L13P_T2L_N0_GC_QBC_40
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C2_DM2"] ;# Bank  40 VCCO - VCC1V2_FPGA - IO_L13P_T2L_N0_GC_QBC_40
# set_property PACKAGE_PIN AY33     [get_ports "DDR4_C2_DQ15"] ;# Bank  40 VCCO - VCC1V2_FPGA - IO_L12N_T1U_N11_GC_40
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C2_DQ15"] ;# Bank  40 VCCO - VCC1V2_FPGA - IO_L12N_T1U_N11_GC_40
# set_property PACKAGE_PIN AY32     [get_ports "DDR4_C2_DQ14"] ;# Bank  40 VCCO - VCC1V2_FPGA - IO_L12P_T1U_N10_GC_40
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C2_DQ14"] ;# Bank  40 VCCO - VCC1V2_FPGA - IO_L12P_T1U_N10_GC_40
# set_property PACKAGE_PIN AW32     [get_ports "DDR4_C2_DQ13"] ;# Bank  40 VCCO - VCC1V2_FPGA - IO_L11N_T1U_N9_GC_40
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C2_DQ13"] ;# Bank  40 VCCO - VCC1V2_FPGA - IO_L11N_T1U_N9_GC_40
# set_property PACKAGE_PIN AW31     [get_ports "DDR4_C2_DQ12"] ;# Bank  40 VCCO - VCC1V2_FPGA - IO_L11P_T1U_N8_GC_40
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C2_DQ12"] ;# Bank  40 VCCO - VCC1V2_FPGA - IO_L11P_T1U_N8_GC_40
# set_property PACKAGE_PIN BA34     [get_ports "DDR4_C2_DQS1_C"] ;# Bank  40 VCCO - VCC1V2_FPGA - IO_L10N_T1U_N7_QBC_AD4N_40
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C2_DQS1_C"] ;# Bank  40 VCCO - VCC1V2_FPGA - IO_L10N_T1U_N7_QBC_AD4N_40
# set_property PACKAGE_PIN AY34     [get_ports "DDR4_C2_DQS1_T"] ;# Bank  40 VCCO - VCC1V2_FPGA - IO_L10P_T1U_N6_QBC_AD4P_40
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C2_DQS1_T"] ;# Bank  40 VCCO - VCC1V2_FPGA - IO_L10P_T1U_N6_QBC_AD4P_40
# set_property PACKAGE_PIN BA31     [get_ports "DDR4_C2_DQ11"] ;# Bank  40 VCCO - VCC1V2_FPGA - IO_L9N_T1L_N5_AD12N_40
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C2_DQ11"] ;# Bank  40 VCCO - VCC1V2_FPGA - IO_L9N_T1L_N5_AD12N_40
# set_property PACKAGE_PIN BA30     [get_ports "DDR4_C2_DQ10"] ;# Bank  40 VCCO - VCC1V2_FPGA - IO_L9P_T1L_N4_AD12P_40
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C2_DQ10"] ;# Bank  40 VCCO - VCC1V2_FPGA - IO_L9P_T1L_N4_AD12P_40
# set_property PACKAGE_PIN BB33     [get_ports "DDR4_C2_DQ9"] ;# Bank  40 VCCO - VCC1V2_FPGA - IO_L8N_T1L_N3_AD5N_40
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C2_DQ9"] ;# Bank  40 VCCO - VCC1V2_FPGA - IO_L8N_T1L_N3_AD5N_40
# set_property PACKAGE_PIN BA32     [get_ports "DDR4_C2_DQ8"] ;# Bank  40 VCCO - VCC1V2_FPGA - IO_L8P_T1L_N2_AD5P_40
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C2_DQ8"] ;# Bank  40 VCCO - VCC1V2_FPGA - IO_L8P_T1L_N2_AD5P_40
# set_property PACKAGE_PIN BB32     [get_ports "GPIO_LED3"] ;# Bank  40 VCCO - VCC1V2_FPGA - IO_L7N_T1L_N1_QBC_AD13N_40
# set_property IOSTANDARD  LVCMOS12 [get_ports "GPIO_LED3"] ;# Bank  40 VCCO - VCC1V2_FPGA - IO_L7N_T1L_N1_QBC_AD13N_40
# set_property PACKAGE_PIN BB31     [get_ports "DDR4_C2_DM1"] ;# Bank  40 VCCO - VCC1V2_FPGA - IO_L7P_T1L_N0_QBC_AD13P_40
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C2_DM1"] ;# Bank  40 VCCO - VCC1V2_FPGA - IO_L7P_T1L_N0_QBC_AD13P_40
# set_property PACKAGE_PIN AY30     [get_ports "GPIO_LED2"] ;# Bank  40 VCCO - VCC1V2_FPGA - IO_T1U_N12_40
# set_property IOSTANDARD  LVCMOS12 [get_ports "GPIO_LED2"] ;# Bank  40 VCCO - VCC1V2_FPGA - IO_T1U_N12_40
# #set_property PACKAGE_PIN BC30     [get_ports "VRP_40"] ;# Bank  40 VCCO - VCC1V2_FPGA - IO_T0U_N12_VRP_40
# #set_property IOSTANDARD  LVCMOSxx [get_ports "VRP_40"] ;# Bank  40 VCCO - VCC1V2_FPGA - IO_T0U_N12_VRP_40
# set_property PACKAGE_PIN BD31     [get_ports "DDR4_C2_DQ7"] ;# Bank  40 VCCO - VCC1V2_FPGA - IO_L6N_T0U_N11_AD6N_40
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C2_DQ7"] ;# Bank  40 VCCO - VCC1V2_FPGA - IO_L6N_T0U_N11_AD6N_40
# set_property PACKAGE_PIN BC31     [get_ports "DDR4_C2_DQ6"] ;# Bank  40 VCCO - VCC1V2_FPGA - IO_L6P_T0U_N10_AD6P_40
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C2_DQ6"] ;# Bank  40 VCCO - VCC1V2_FPGA - IO_L6P_T0U_N10_AD6P_40
# set_property PACKAGE_PIN BD33     [get_ports "DDR4_C2_DQ5"] ;# Bank  40 VCCO - VCC1V2_FPGA - IO_L5N_T0U_N9_AD14N_40
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C2_DQ5"] ;# Bank  40 VCCO - VCC1V2_FPGA - IO_L5N_T0U_N9_AD14N_40
# set_property PACKAGE_PIN BC33     [get_ports "DDR4_C2_DQ4"] ;# Bank  40 VCCO - VCC1V2_FPGA - IO_L5P_T0U_N8_AD14P_40
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C2_DQ4"] ;# Bank  40 VCCO - VCC1V2_FPGA - IO_L5P_T0U_N8_AD14P_40
# set_property PACKAGE_PIN BF31     [get_ports "DDR4_C2_DQS0_C"] ;# Bank  40 VCCO - VCC1V2_FPGA - IO_L4N_T0U_N7_DBC_AD7N_40
# set_property IOSTANDARD  DIFF_POD12 [get_ports "DDR4_C2_DQS0_C"] ;# Bank  40 VCCO - VCC1V2_FPGA - IO_L4N_T0U_N7_DBC_AD7N_40
# set_property PACKAGE_PIN BF30     [get_ports "DDR4_C2_DQS0_T"] ;# Bank  40 VCCO - VCC1V2_FPGA - IO_L4P_T0U_N6_DBC_AD7P_40
# set_property IOSTANDARD  DIFF_POD12 [get_ports "DDR4_C2_DQS0_T"] ;# Bank  40 VCCO - VCC1V2_FPGA - IO_L4P_T0U_N6_DBC_AD7P_40
# set_property PACKAGE_PIN BE33     [get_ports "DDR4_C2_DQ3"] ;# Bank  40 VCCO - VCC1V2_FPGA - IO_L3N_T0L_N5_AD15N_40
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C2_DQ3"] ;# Bank  40 VCCO - VCC1V2_FPGA - IO_L3N_T0L_N5_AD15N_40
# set_property PACKAGE_PIN BD32     [get_ports "DDR4_C2_DQ2"] ;# Bank  40 VCCO - VCC1V2_FPGA - IO_L3P_T0L_N4_AD15P_40
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C2_DQ2"] ;# Bank  40 VCCO - VCC1V2_FPGA - IO_L3P_T0L_N4_AD15P_40
# set_property PACKAGE_PIN BE30     [get_ports "DDR4_C2_DQ1"] ;# Bank  40 VCCO - VCC1V2_FPGA - IO_L2N_T0L_N3_40
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C2_DQ1"] ;# Bank  40 VCCO - VCC1V2_FPGA - IO_L2N_T0L_N3_40
# set_property PACKAGE_PIN BD30     [get_ports "DDR4_C2_DQ0"] ;# Bank  40 VCCO - VCC1V2_FPGA - IO_L2P_T0L_N2_40
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C2_DQ0"] ;# Bank  40 VCCO - VCC1V2_FPGA - IO_L2P_T0L_N2_40
# set_property PACKAGE_PIN BF32     [get_ports "GPIO_LED4"] ;# Bank  40 VCCO - VCC1V2_FPGA - IO_L1N_T0L_N1_DBC_40
# set_property IOSTANDARD  LVCMOS12 [get_ports "GPIO_LED4"] ;# Bank  40 VCCO - VCC1V2_FPGA - IO_L1N_T0L_N1_DBC_40
# set_property PACKAGE_PIN BE32     [get_ports "DDR4_C2_DM0"] ;# Bank  40 VCCO - VCC1V2_FPGA - IO_L1P_T0L_N0_DBC_40
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C2_DM0"] ;# Bank  40 VCCO - VCC1V2_FPGA - IO_L1P_T0L_N0_DBC_40
# #Other net   PACKAGE_PIN AN29     - 5N11680                   Bank  40 - VREF_40
# set_property PACKAGE_PIN B20      [get_ports "DDR4_C1_DQ39"] ;# Bank  73 VCCO - VCC1V2_FPGA - IO_L24N_T3U_N11_73
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C1_DQ39"] ;# Bank  73 VCCO - VCC1V2_FPGA - IO_L24N_T3U_N11_73
# set_property PACKAGE_PIN C20      [get_ports "DDR4_C1_DQ38"] ;# Bank  73 VCCO - VCC1V2_FPGA - IO_L24P_T3U_N10_73
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C1_DQ38"] ;# Bank  73 VCCO - VCC1V2_FPGA - IO_L24P_T3U_N10_73
# set_property PACKAGE_PIN D19      [get_ports "DDR4_C1_DQ37"] ;# Bank  73 VCCO - VCC1V2_FPGA - IO_L23N_T3U_N9_73
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C1_DQ37"] ;# Bank  73 VCCO - VCC1V2_FPGA - IO_L23N_T3U_N9_73
# set_property PACKAGE_PIN D20      [get_ports "DDR4_C1_DQ36"] ;# Bank  73 VCCO - VCC1V2_FPGA - IO_L23P_T3U_N8_73
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C1_DQ36"] ;# Bank  73 VCCO - VCC1V2_FPGA - IO_L23P_T3U_N8_73
# set_property PACKAGE_PIN A18      [get_ports "DDR4_C1_DQS4_C"] ;# Bank  73 VCCO - VCC1V2_FPGA - IO_L22N_T3U_N7_DBC_AD0N_73
# set_property IOSTANDARD  DIFF_POD12 [get_ports "DDR4_C1_DQS4_C"] ;# Bank  73 VCCO - VCC1V2_FPGA - IO_L22N_T3U_N7_DBC_AD0N_73
# set_property PACKAGE_PIN A19      [get_ports "DDR4_C1_DQS4_T"] ;# Bank  73 VCCO - VCC1V2_FPGA - IO_L22P_T3U_N6_DBC_AD0P_73
# set_property IOSTANDARD  DIFF_POD12 [get_ports "DDR4_C1_DQS4_T"] ;# Bank  73 VCCO - VCC1V2_FPGA - IO_L22P_T3U_N6_DBC_AD0P_73
# set_property PACKAGE_PIN C18      [get_ports "DDR4_C1_DQ35"] ;# Bank  73 VCCO - VCC1V2_FPGA - IO_L21N_T3L_N5_AD8N_73
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C1_DQ35"] ;# Bank  73 VCCO - VCC1V2_FPGA - IO_L21N_T3L_N5_AD8N_73
# set_property PACKAGE_PIN C19      [get_ports "DDR4_C1_DQ34"] ;# Bank  73 VCCO - VCC1V2_FPGA - IO_L21P_T3L_N4_AD8P_73
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C1_DQ34"] ;# Bank  73 VCCO - VCC1V2_FPGA - IO_L21P_T3L_N4_AD8P_73
# set_property PACKAGE_PIN C17      [get_ports "DDR4_C1_DQ33"] ;# Bank  73 VCCO - VCC1V2_FPGA - IO_L20N_T3L_N3_AD1N_73
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C1_DQ33"] ;# Bank  73 VCCO - VCC1V2_FPGA - IO_L20N_T3L_N3_AD1N_73
# set_property PACKAGE_PIN D17      [get_ports "DDR4_C1_DQ32"] ;# Bank  73 VCCO - VCC1V2_FPGA - IO_L20P_T3L_N2_AD1P_73
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C1_DQ32"] ;# Bank  73 VCCO - VCC1V2_FPGA - IO_L20P_T3L_N2_AD1P_73
# set_property PACKAGE_PIN B17      [get_ports "GPIO_DIP_SW1"] ;# Bank  73 VCCO - VCC1V2_FPGA - IO_L19N_T3L_N1_DBC_AD9N_73
# set_property IOSTANDARD  LVCMOS12 [get_ports "GPIO_DIP_SW1"] ;# Bank  73 VCCO - VCC1V2_FPGA - IO_L19N_T3L_N1_DBC_AD9N_73
# set_property PACKAGE_PIN B18      [get_ports "DDR4_C1_DM4"] ;# Bank  73 VCCO - VCC1V2_FPGA - IO_L19P_T3L_N0_DBC_AD9P_73
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C1_DM4"] ;# Bank  73 VCCO - VCC1V2_FPGA - IO_L19P_T3L_N0_DBC_AD9P_73
# set_property PACKAGE_PIN A20      [get_ports "DDR4_C1_TEN"] ;# Bank  73 VCCO - VCC1V2_FPGA - IO_T3U_N12_73
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C1_TEN"] ;# Bank  73 VCCO - VCC1V2_FPGA - IO_T3U_N12_73
# set_property PACKAGE_PIN G16      [get_ports "GPIO_DIP_SW2"] ;# Bank  73 VCCO - VCC1V2_FPGA - IO_T2U_N12_73
# set_property IOSTANDARD  LVCMOS12 [get_ports "GPIO_DIP_SW2"] ;# Bank  73 VCCO - VCC1V2_FPGA - IO_T2U_N12_73
# set_property PACKAGE_PIN D16      [get_ports "DDR4_C1_DQ31"] ;# Bank  73 VCCO - VCC1V2_FPGA - IO_L18N_T2U_N11_AD2N_73
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C1_DQ31"] ;# Bank  73 VCCO - VCC1V2_FPGA - IO_L18N_T2U_N11_AD2N_73
# set_property PACKAGE_PIN E17      [get_ports "DDR4_C1_DQ30"] ;# Bank  73 VCCO - VCC1V2_FPGA - IO_L18P_T2U_N10_AD2P_73
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C1_DQ30"] ;# Bank  73 VCCO - VCC1V2_FPGA - IO_L18P_T2U_N10_AD2P_73
# set_property PACKAGE_PIN F20      [get_ports "DDR4_C1_DQ29"] ;# Bank  73 VCCO - VCC1V2_FPGA - IO_L17N_T2U_N9_AD10N_73
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C1_DQ29"] ;# Bank  73 VCCO - VCC1V2_FPGA - IO_L17N_T2U_N9_AD10N_73
# set_property PACKAGE_PIN G20      [get_ports "DDR4_C1_DQ28"] ;# Bank  73 VCCO - VCC1V2_FPGA - IO_L17P_T2U_N8_AD10P_73
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C1_DQ28"] ;# Bank  73 VCCO - VCC1V2_FPGA - IO_L17P_T2U_N8_AD10P_73
# set_property PACKAGE_PIN E16      [get_ports "DDR4_C1_DQS3_C"] ;# Bank  73 VCCO - VCC1V2_FPGA - IO_L16N_T2U_N7_QBC_AD3N_73
# set_property IOSTANDARD  DIFF_POD12 [get_ports "DDR4_C1_DQS3_C"] ;# Bank  73 VCCO - VCC1V2_FPGA - IO_L16N_T2U_N7_QBC_AD3N_73
# set_property PACKAGE_PIN F16      [get_ports "DDR4_C1_DQS3_T"] ;# Bank  73 VCCO - VCC1V2_FPGA - IO_L16P_T2U_N6_QBC_AD3P_73
# set_property IOSTANDARD  DIFF_POD12 [get_ports "DDR4_C1_DQS3_T"] ;# Bank  73 VCCO - VCC1V2_FPGA - IO_L16P_T2U_N6_QBC_AD3P_73
# set_property PACKAGE_PIN E18      [get_ports "DDR4_C1_DQ27"] ;# Bank  73 VCCO - VCC1V2_FPGA - IO_L15N_T2L_N5_AD11N_73
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C1_DQ27"] ;# Bank  73 VCCO - VCC1V2_FPGA - IO_L15N_T2L_N5_AD11N_73
# set_property PACKAGE_PIN E19      [get_ports "DDR4_C1_DQ26"] ;# Bank  73 VCCO - VCC1V2_FPGA - IO_L15P_T2L_N4_AD11P_73
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C1_DQ26"] ;# Bank  73 VCCO - VCC1V2_FPGA - IO_L15P_T2L_N4_AD11P_73
# set_property PACKAGE_PIN F18      [get_ports "DDR4_C1_DQ25"] ;# Bank  73 VCCO - VCC1V2_FPGA - IO_L14N_T2L_N3_GC_73
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C1_DQ25"] ;# Bank  73 VCCO - VCC1V2_FPGA - IO_L14N_T2L_N3_GC_73
# set_property PACKAGE_PIN F19      [get_ports "DDR4_C1_DQ24"] ;# Bank  73 VCCO - VCC1V2_FPGA - IO_L14P_T2L_N2_GC_73
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C1_DQ24"] ;# Bank  73 VCCO - VCC1V2_FPGA - IO_L14P_T2L_N2_GC_73
# set_property PACKAGE_PIN G17      [get_ports "5329N4285"] ;# Bank  73 VCCO - VCC1V2_FPGA - IO_L13N_T2L_N1_GC_QBC_73
# set_property IOSTANDARD  LVCMOSxx [get_ports "5329N4285"] ;# Bank  73 VCCO - VCC1V2_FPGA - IO_L13N_T2L_N1_GC_QBC_73
# set_property PACKAGE_PIN G18      [get_ports "DDR4_C1_DM3"] ;# Bank  73 VCCO - VCC1V2_FPGA - IO_L13P_T2L_N0_GC_QBC_73
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C1_DM3"] ;# Bank  73 VCCO - VCC1V2_FPGA - IO_L13P_T2L_N0_GC_QBC_73
# set_property PACKAGE_PIN H18      [get_ports "DDR4_C1_DQ23"] ;# Bank  73 VCCO - VCC1V2_FPGA - IO_L12N_T1U_N11_GC_73
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C1_DQ23"] ;# Bank  73 VCCO - VCC1V2_FPGA - IO_L12N_T1U_N11_GC_73
# set_property PACKAGE_PIN H19      [get_ports "DDR4_C1_DQ22"] ;# Bank  73 VCCO - VCC1V2_FPGA - IO_L12P_T1U_N10_GC_73
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C1_DQ22"] ;# Bank  73 VCCO - VCC1V2_FPGA - IO_L12P_T1U_N10_GC_73
# set_property PACKAGE_PIN H17      [get_ports "DDR4_C1_DQ21"] ;# Bank  73 VCCO - VCC1V2_FPGA - IO_L11N_T1U_N9_GC_73
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C1_DQ21"] ;# Bank  73 VCCO - VCC1V2_FPGA - IO_L11N_T1U_N9_GC_73
# set_property PACKAGE_PIN J17      [get_ports "DDR4_C1_DQ20"] ;# Bank  73 VCCO - VCC1V2_FPGA - IO_L11P_T1U_N8_GC_73
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C1_DQ20"] ;# Bank  73 VCCO - VCC1V2_FPGA - IO_L11P_T1U_N8_GC_73
# set_property PACKAGE_PIN J19      [get_ports "DDR4_C1_DQS2_C"] ;# Bank  73 VCCO - VCC1V2_FPGA - IO_L10N_T1U_N7_QBC_AD4N_73
# set_property IOSTANDARD  DIFF_POD12 [get_ports "DDR4_C1_DQS2_C"] ;# Bank  73 VCCO - VCC1V2_FPGA - IO_L10N_T1U_N7_QBC_AD4N_73
# set_property PACKAGE_PIN K19      [get_ports "DDR4_C1_DQS2_T"] ;# Bank  73 VCCO - VCC1V2_FPGA - IO_L10P_T1U_N6_QBC_AD4P_73
# set_property IOSTANDARD  DIFF_POD12 [get_ports "DDR4_C1_DQS2_T"] ;# Bank  73 VCCO - VCC1V2_FPGA - IO_L10P_T1U_N6_QBC_AD4P_73
# set_property PACKAGE_PIN K18      [get_ports "DDR4_C1_DQ19"] ;# Bank  73 VCCO - VCC1V2_FPGA - IO_L9N_T1L_N5_AD12N_73
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C1_DQ19"] ;# Bank  73 VCCO - VCC1V2_FPGA - IO_L9N_T1L_N5_AD12N_73
# set_property PACKAGE_PIN L18      [get_ports "DDR4_C1_DQ18"] ;# Bank  73 VCCO - VCC1V2_FPGA - IO_L9P_T1L_N4_AD12P_73
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C1_DQ18"] ;# Bank  73 VCCO - VCC1V2_FPGA - IO_L9P_T1L_N4_AD12P_73
# set_property PACKAGE_PIN K16      [get_ports "DDR4_C1_DQ17"] ;# Bank  73 VCCO - VCC1V2_FPGA - IO_L8N_T1L_N3_AD5N_73
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C1_DQ17"] ;# Bank  73 VCCO - VCC1V2_FPGA - IO_L8N_T1L_N3_AD5N_73
# set_property PACKAGE_PIN L16      [get_ports "DDR4_C1_DQ16"] ;# Bank  73 VCCO - VCC1V2_FPGA - IO_L8P_T1L_N2_AD5P_73
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C1_DQ16"] ;# Bank  73 VCCO - VCC1V2_FPGA - IO_L8P_T1L_N2_AD5P_73
# set_property PACKAGE_PIN J16      [get_ports "GPIO_DIP_SW3"] ;# Bank  73 VCCO - VCC1V2_FPGA - IO_L7N_T1L_N1_QBC_AD13N_73
# set_property IOSTANDARD  LVCMOS12 [get_ports "GPIO_DIP_SW3"] ;# Bank  73 VCCO - VCC1V2_FPGA - IO_L7N_T1L_N1_QBC_AD13N_73
# set_property PACKAGE_PIN K17      [get_ports "DDR4_C1_DM2"] ;# Bank  73 VCCO - VCC1V2_FPGA - IO_L7P_T1L_N0_QBC_AD13P_73
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C1_DM2"] ;# Bank  73 VCCO - VCC1V2_FPGA - IO_L7P_T1L_N0_QBC_AD13P_73
# #set_property PACKAGE_PIN T18      [get_ports "VRP_73"] ;# Bank  73 VCCO - VCC1V2_FPGA - IO_T0U_N12_VRP_73
# #set_property IOSTANDARD  LVCMOSxx [get_ports "VRP_73"] ;# Bank  73 VCCO - VCC1V2_FPGA - IO_T0U_N12_VRP_73
# set_property PACKAGE_PIN M16      [get_ports "DDR4_C1_DQ15"] ;# Bank  73 VCCO - VCC1V2_FPGA - IO_L6N_T0U_N11_AD6N_73
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C1_DQ15"] ;# Bank  73 VCCO - VCC1V2_FPGA - IO_L6N_T0U_N11_AD6N_73
# set_property PACKAGE_PIN N17      [get_ports "DDR4_C1_DQ14"] ;# Bank  73 VCCO - VCC1V2_FPGA - IO_L6P_T0U_N10_AD6P_73
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C1_DQ14"] ;# Bank  73 VCCO - VCC1V2_FPGA - IO_L6P_T0U_N10_AD6P_73
# set_property PACKAGE_PIN N18      [get_ports "DDR4_C1_DQ13"] ;# Bank  73 VCCO - VCC1V2_FPGA - IO_L5N_T0U_N9_AD14N_73
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C1_DQ13"] ;# Bank  73 VCCO - VCC1V2_FPGA - IO_L5N_T0U_N9_AD14N_73
# set_property PACKAGE_PIN N19      [get_ports "DDR4_C1_DQ12"] ;# Bank  73 VCCO - VCC1V2_FPGA - IO_L5P_T0U_N8_AD14P_73
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C1_DQ12"] ;# Bank  73 VCCO - VCC1V2_FPGA - IO_L5P_T0U_N8_AD14P_73
# set_property PACKAGE_PIN P16      [get_ports "DDR4_C1_DQS1_C"] ;# Bank  73 VCCO - VCC1V2_FPGA - IO_L4N_T0U_N7_DBC_AD7N_73
# set_property IOSTANDARD  DIFF_POD12 [get_ports "DDR4_C1_DQS1_C"] ;# Bank  73 VCCO - VCC1V2_FPGA - IO_L4N_T0U_N7_DBC_AD7N_73
# set_property PACKAGE_PIN P17      [get_ports "DDR4_C1_DQS1_T"] ;# Bank  73 VCCO - VCC1V2_FPGA - IO_L4P_T0U_N6_DBC_AD7P_73
# set_property IOSTANDARD  DIFF_POD12 [get_ports "DDR4_C1_DQS1_T"] ;# Bank  73 VCCO - VCC1V2_FPGA - IO_L4P_T0U_N6_DBC_AD7P_73
# set_property PACKAGE_PIN M17      [get_ports "DDR4_C1_DQ11"] ;# Bank  73 VCCO - VCC1V2_FPGA - IO_L3N_T0L_N5_AD15N_73
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C1_DQ11"] ;# Bank  73 VCCO - VCC1V2_FPGA - IO_L3N_T0L_N5_AD15N_73
# set_property PACKAGE_PIN M18      [get_ports "DDR4_C1_DQ10"] ;# Bank  73 VCCO - VCC1V2_FPGA - IO_L3P_T0L_N4_AD15P_73
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C1_DQ10"] ;# Bank  73 VCCO - VCC1V2_FPGA - IO_L3P_T0L_N4_AD15P_73
# set_property PACKAGE_PIN P19      [get_ports "DDR4_C1_DQ9"] ;# Bank  73 VCCO - VCC1V2_FPGA - IO_L2N_T0L_N3_73
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C1_DQ9"] ;# Bank  73 VCCO - VCC1V2_FPGA - IO_L2N_T0L_N3_73
# set_property PACKAGE_PIN R19      [get_ports "DDR4_C1_DQ8"] ;# Bank  73 VCCO - VCC1V2_FPGA - IO_L2P_T0L_N2_73
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C1_DQ8"] ;# Bank  73 VCCO - VCC1V2_FPGA - IO_L2P_T0L_N2_73
# set_property PACKAGE_PIN R17      [get_ports "DDR4_C1_ALERT_B"] ;# Bank  73 VCCO - VCC1V2_FPGA - IO_L1N_T0L_N1_DBC_73
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C1_ALERT_B"] ;# Bank  73 VCCO - VCC1V2_FPGA - IO_L1N_T0L_N1_DBC_73
# set_property PACKAGE_PIN R18      [get_ports "DDR4_C1_DM1"] ;# Bank  73 VCCO - VCC1V2_FPGA - IO_L1P_T0L_N0_DBC_73
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C1_DM1"] ;# Bank  73 VCCO - VCC1V2_FPGA - IO_L1P_T0L_N0_DBC_73
# #Other net   PACKAGE_PIN T19      - 5329N4282                 Bank  73 - VREF_73
# set_property PACKAGE_PIN A21      [get_ports "DDR4_C1_DQ71"] ;# Bank  72 VCCO - VCC1V2_FPGA - IO_L24N_T3U_N11_72
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C1_DQ71"] ;# Bank  72 VCCO - VCC1V2_FPGA - IO_L24N_T3U_N11_72
# set_property PACKAGE_PIN B21      [get_ports "DDR4_C1_DQ70"] ;# Bank  72 VCCO - VCC1V2_FPGA - IO_L24P_T3U_N10_72
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C1_DQ70"] ;# Bank  72 VCCO - VCC1V2_FPGA - IO_L24P_T3U_N10_72
# set_property PACKAGE_PIN B22      [get_ports "DDR4_C1_DQ69"] ;# Bank  72 VCCO - VCC1V2_FPGA - IO_L23N_T3U_N9_72
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C1_DQ69"] ;# Bank  72 VCCO - VCC1V2_FPGA - IO_L23N_T3U_N9_72
# set_property PACKAGE_PIN B23      [get_ports "DDR4_C1_DQ68"] ;# Bank  72 VCCO - VCC1V2_FPGA - IO_L23P_T3U_N8_72
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C1_DQ68"] ;# Bank  72 VCCO - VCC1V2_FPGA - IO_L23P_T3U_N8_72
# set_property PACKAGE_PIN C22      [get_ports "DDR4_C1_DQS8_C"] ;# Bank  72 VCCO - VCC1V2_FPGA - IO_L22N_T3U_N7_DBC_AD0N_72
# set_property IOSTANDARD  DIFF_POD12 [get_ports "DDR4_C1_DQS8_C"] ;# Bank  72 VCCO - VCC1V2_FPGA - IO_L22N_T3U_N7_DBC_AD0N_72
# set_property PACKAGE_PIN D22      [get_ports "DDR4_C1_DQS8_T"] ;# Bank  72 VCCO - VCC1V2_FPGA - IO_L22P_T3U_N6_DBC_AD0P_72
# set_property IOSTANDARD  DIFF_POD12 [get_ports "DDR4_C1_DQS8_T"] ;# Bank  72 VCCO - VCC1V2_FPGA - IO_L22P_T3U_N6_DBC_AD0P_72
# set_property PACKAGE_PIN C23      [get_ports "DDR4_C1_DQ67"] ;# Bank  72 VCCO - VCC1V2_FPGA - IO_L21N_T3L_N5_AD8N_72
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C1_DQ67"] ;# Bank  72 VCCO - VCC1V2_FPGA - IO_L21N_T3L_N5_AD8N_72
# set_property PACKAGE_PIN C24      [get_ports "DDR4_C1_DQ66"] ;# Bank  72 VCCO - VCC1V2_FPGA - IO_L21P_T3L_N4_AD8P_72
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C1_DQ66"] ;# Bank  72 VCCO - VCC1V2_FPGA - IO_L21P_T3L_N4_AD8P_72
# set_property PACKAGE_PIN A23      [get_ports "DDR4_C1_DQ65"] ;# Bank  72 VCCO - VCC1V2_FPGA - IO_L20N_T3L_N3_AD1N_72
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C1_DQ65"] ;# Bank  72 VCCO - VCC1V2_FPGA - IO_L20N_T3L_N3_AD1N_72
# set_property PACKAGE_PIN A24      [get_ports "DDR4_C1_DQ64"] ;# Bank  72 VCCO - VCC1V2_FPGA - IO_L20P_T3L_N2_AD1P_72
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C1_DQ64"] ;# Bank  72 VCCO - VCC1V2_FPGA - IO_L20P_T3L_N2_AD1P_72
# set_property PACKAGE_PIN D24      [get_ports "5329N4244"] ;# Bank  72 VCCO - VCC1V2_FPGA - IO_L19N_T3L_N1_DBC_AD9N_72
# set_property IOSTANDARD  LVCMOSxx [get_ports "5329N4244"] ;# Bank  72 VCCO - VCC1V2_FPGA - IO_L19N_T3L_N1_DBC_AD9N_72
# set_property PACKAGE_PIN E24      [get_ports "DDR4_C1_DM8"] ;# Bank  72 VCCO - VCC1V2_FPGA - IO_L19P_T3L_N0_DBC_AD9P_72
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C1_DM8"] ;# Bank  72 VCCO - VCC1V2_FPGA - IO_L19P_T3L_N0_DBC_AD9P_72
# set_property PACKAGE_PIN D21      [get_ports "GPIO_DIP_SW4"] ;# Bank  72 VCCO - VCC1V2_FPGA - IO_T3U_N12_72
# set_property IOSTANDARD  LVCMOS12 [get_ports "GPIO_DIP_SW4"] ;# Bank  72 VCCO - VCC1V2_FPGA - IO_T3U_N12_72
# set_property PACKAGE_PIN H20      [get_ports "SI5328_INT_ALM_LS"] ;# Bank  72 VCCO - VCC1V2_FPGA - IO_T2U_N12_72
# set_property IOSTANDARD  LVCMOS12 [get_ports "SI5328_INT_ALM_LS"] ;# Bank  72 VCCO - VCC1V2_FPGA - IO_T2U_N12_72
# set_property PACKAGE_PIN F23      [get_ports "DDR4_C1_DQ63"] ;# Bank  72 VCCO - VCC1V2_FPGA - IO_L18N_T2U_N11_AD2N_72
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C1_DQ63"] ;# Bank  72 VCCO - VCC1V2_FPGA - IO_L18N_T2U_N11_AD2N_72
# set_property PACKAGE_PIN F24      [get_ports "DDR4_C1_DQ62"] ;# Bank  72 VCCO - VCC1V2_FPGA - IO_L18P_T2U_N10_AD2P_72
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C1_DQ62"] ;# Bank  72 VCCO - VCC1V2_FPGA - IO_L18P_T2U_N10_AD2P_72
# set_property PACKAGE_PIN E21      [get_ports "DDR4_C1_DQ61"] ;# Bank  72 VCCO - VCC1V2_FPGA - IO_L17N_T2U_N9_AD10N_72
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C1_DQ61"] ;# Bank  72 VCCO - VCC1V2_FPGA - IO_L17N_T2U_N9_AD10N_72
# set_property PACKAGE_PIN F21      [get_ports "DDR4_C1_DQ60"] ;# Bank  72 VCCO - VCC1V2_FPGA - IO_L17P_T2U_N8_AD10P_72
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C1_DQ60"] ;# Bank  72 VCCO - VCC1V2_FPGA - IO_L17P_T2U_N8_AD10P_72
# set_property PACKAGE_PIN G23      [get_ports "DDR4_C1_DQS7_C"] ;# Bank  72 VCCO - VCC1V2_FPGA - IO_L16N_T2U_N7_QBC_AD3N_72
# set_property IOSTANDARD  DIFF_POD12 [get_ports "DDR4_C1_DQS7_C"] ;# Bank  72 VCCO - VCC1V2_FPGA - IO_L16N_T2U_N7_QBC_AD3N_72
# set_property PACKAGE_PIN H24      [get_ports "DDR4_C1_DQS7_T"] ;# Bank  72 VCCO - VCC1V2_FPGA - IO_L16P_T2U_N6_QBC_AD3P_72
# set_property IOSTANDARD  DIFF_POD12 [get_ports "DDR4_C1_DQS7_T"] ;# Bank  72 VCCO - VCC1V2_FPGA - IO_L16P_T2U_N6_QBC_AD3P_72
# set_property PACKAGE_PIN E22      [get_ports "DDR4_C1_DQ59"] ;# Bank  72 VCCO - VCC1V2_FPGA - IO_L15N_T2L_N5_AD11N_72
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C1_DQ59"] ;# Bank  72 VCCO - VCC1V2_FPGA - IO_L15N_T2L_N5_AD11N_72
# set_property PACKAGE_PIN E23      [get_ports "DDR4_C1_DQ58"] ;# Bank  72 VCCO - VCC1V2_FPGA - IO_L15P_T2L_N4_AD11P_72
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C1_DQ58"] ;# Bank  72 VCCO - VCC1V2_FPGA - IO_L15P_T2L_N4_AD11P_72
# set_property PACKAGE_PIN H22      [get_ports "DDR4_C1_DQ57"] ;# Bank  72 VCCO - VCC1V2_FPGA - IO_L14N_T2L_N3_GC_72
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C1_DQ57"] ;# Bank  72 VCCO - VCC1V2_FPGA - IO_L14N_T2L_N3_GC_72
# set_property PACKAGE_PIN H23      [get_ports "DDR4_C1_DQ56"] ;# Bank  72 VCCO - VCC1V2_FPGA - IO_L14P_T2L_N2_GC_72
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C1_DQ56"] ;# Bank  72 VCCO - VCC1V2_FPGA - IO_L14P_T2L_N2_GC_72
# set_property PACKAGE_PIN G21      [get_ports "5329N4246"] ;# Bank  72 VCCO - VCC1V2_FPGA - IO_L13N_T2L_N1_GC_QBC_72
# set_property IOSTANDARD  LVCMOSxx [get_ports "5329N4246"] ;# Bank  72 VCCO - VCC1V2_FPGA - IO_L13N_T2L_N1_GC_QBC_72
# set_property PACKAGE_PIN G22      [get_ports "DDR4_C1_DM7"] ;# Bank  72 VCCO - VCC1V2_FPGA - IO_L13P_T2L_N0_GC_QBC_72
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C1_DM7"] ;# Bank  72 VCCO - VCC1V2_FPGA - IO_L13P_T2L_N0_GC_QBC_72
# set_property PACKAGE_PIN J22      [get_ports "DDR4_C1_DQ55"] ;# Bank  72 VCCO - VCC1V2_FPGA - IO_L12N_T1U_N11_GC_72
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C1_DQ55"] ;# Bank  72 VCCO - VCC1V2_FPGA - IO_L12N_T1U_N11_GC_72
# set_property PACKAGE_PIN K22      [get_ports "DDR4_C1_DQ54"] ;# Bank  72 VCCO - VCC1V2_FPGA - IO_L12P_T1U_N10_GC_72
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C1_DQ54"] ;# Bank  72 VCCO - VCC1V2_FPGA - IO_L12P_T1U_N10_GC_72
# set_property PACKAGE_PIN J21      [get_ports "DDR4_C1_DQ53"] ;# Bank  72 VCCO - VCC1V2_FPGA - IO_L11N_T1U_N9_GC_72
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C1_DQ53"] ;# Bank  72 VCCO - VCC1V2_FPGA - IO_L11N_T1U_N9_GC_72
# set_property PACKAGE_PIN K21      [get_ports "DDR4_C1_DQ52"] ;# Bank  72 VCCO - VCC1V2_FPGA - IO_L11P_T1U_N8_GC_72
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C1_DQ52"] ;# Bank  72 VCCO - VCC1V2_FPGA - IO_L11P_T1U_N8_GC_72
# set_property PACKAGE_PIN L20      [get_ports "DDR4_C1_DQS6_C"] ;# Bank  72 VCCO - VCC1V2_FPGA - IO_L10N_T1U_N7_QBC_AD4N_72
# set_property IOSTANDARD  DIFF_POD12 [get_ports "DDR4_C1_DQS6_C"] ;# Bank  72 VCCO - VCC1V2_FPGA - IO_L10N_T1U_N7_QBC_AD4N_72
# set_property PACKAGE_PIN M20      [get_ports "DDR4_C1_DQS6_T"] ;# Bank  72 VCCO - VCC1V2_FPGA - IO_L10P_T1U_N6_QBC_AD4P_72
# set_property IOSTANDARD  DIFF_POD12 [get_ports "DDR4_C1_DQS6_T"] ;# Bank  72 VCCO - VCC1V2_FPGA - IO_L10P_T1U_N6_QBC_AD4P_72
# set_property PACKAGE_PIN L21      [get_ports "DDR4_C1_DQ51"] ;# Bank  72 VCCO - VCC1V2_FPGA - IO_L9N_T1L_N5_AD12N_72
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C1_DQ51"] ;# Bank  72 VCCO - VCC1V2_FPGA - IO_L9N_T1L_N5_AD12N_72
# set_property PACKAGE_PIN M21      [get_ports "DDR4_C1_DQ50"] ;# Bank  72 VCCO - VCC1V2_FPGA - IO_L9P_T1L_N4_AD12P_72
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C1_DQ50"] ;# Bank  72 VCCO - VCC1V2_FPGA - IO_L9P_T1L_N4_AD12P_72
# set_property PACKAGE_PIN J24      [get_ports "DDR4_C1_DQ49"] ;# Bank  72 VCCO - VCC1V2_FPGA - IO_L8N_T1L_N3_AD5N_72
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C1_DQ49"] ;# Bank  72 VCCO - VCC1V2_FPGA - IO_L8N_T1L_N3_AD5N_72
# set_property PACKAGE_PIN K24      [get_ports "DDR4_C1_DQ48"] ;# Bank  72 VCCO - VCC1V2_FPGA - IO_L8P_T1L_N2_AD5P_72
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C1_DQ48"] ;# Bank  72 VCCO - VCC1V2_FPGA - IO_L8P_T1L_N2_AD5P_72
# set_property PACKAGE_PIN K23      [get_ports "5329N4248"] ;# Bank  72 VCCO - VCC1V2_FPGA - IO_L7N_T1L_N1_QBC_AD13N_72
# set_property IOSTANDARD  LVCMOSxx [get_ports "5329N4248"] ;# Bank  72 VCCO - VCC1V2_FPGA - IO_L7N_T1L_N1_QBC_AD13N_72
# set_property PACKAGE_PIN L23      [get_ports "DDR4_C1_DM6"] ;# Bank  72 VCCO - VCC1V2_FPGA - IO_L7P_T1L_N0_QBC_AD13P_72
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C1_DM6"] ;# Bank  72 VCCO - VCC1V2_FPGA - IO_L7P_T1L_N0_QBC_AD13P_72
# set_property PACKAGE_PIN J20      [get_ports "5329N4257"] ;# Bank  72 VCCO - VCC1V2_FPGA - IO_T1U_N12_72
# set_property IOSTANDARD  LVCMOSxx [get_ports "5329N4257"] ;# Bank  72 VCCO - VCC1V2_FPGA - IO_T1U_N12_72
# #set_property PACKAGE_PIN T21      [get_ports "VRP_72"] ;# Bank  72 VCCO - VCC1V2_FPGA - IO_T0U_N12_VRP_72
# #set_property IOSTANDARD  LVCMOSxx [get_ports "VRP_72"] ;# Bank  72 VCCO - VCC1V2_FPGA - IO_T0U_N12_VRP_72
# set_property PACKAGE_PIN R23      [get_ports "DDR4_C1_DQ47"] ;# Bank  72 VCCO - VCC1V2_FPGA - IO_L6N_T0U_N11_AD6N_72
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C1_DQ47"] ;# Bank  72 VCCO - VCC1V2_FPGA - IO_L6N_T0U_N11_AD6N_72
# set_property PACKAGE_PIN T23      [get_ports "DDR4_C1_DQ46"] ;# Bank  72 VCCO - VCC1V2_FPGA - IO_L6P_T0U_N10_AD6P_72
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C1_DQ46"] ;# Bank  72 VCCO - VCC1V2_FPGA - IO_L6P_T0U_N10_AD6P_72
# set_property PACKAGE_PIN P22      [get_ports "DDR4_C1_DQ45"] ;# Bank  72 VCCO - VCC1V2_FPGA - IO_L5N_T0U_N9_AD14N_72
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C1_DQ45"] ;# Bank  72 VCCO - VCC1V2_FPGA - IO_L5N_T0U_N9_AD14N_72
# set_property PACKAGE_PIN R22      [get_ports "DDR4_C1_DQ44"] ;# Bank  72 VCCO - VCC1V2_FPGA - IO_L5P_T0U_N8_AD14P_72
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C1_DQ44"] ;# Bank  72 VCCO - VCC1V2_FPGA - IO_L5P_T0U_N8_AD14P_72
# set_property PACKAGE_PIN M22      [get_ports "DDR4_C1_DQS5_C"] ;# Bank  72 VCCO - VCC1V2_FPGA - IO_L4N_T0U_N7_DBC_AD7N_72
# set_property IOSTANDARD  DIFF_POD12 [get_ports "DDR4_C1_DQS5_C"] ;# Bank  72 VCCO - VCC1V2_FPGA - IO_L4N_T0U_N7_DBC_AD7N_72
# set_property PACKAGE_PIN N22      [get_ports "DDR4_C1_DQS5_T"] ;# Bank  72 VCCO - VCC1V2_FPGA - IO_L4P_T0U_N6_DBC_AD7P_72
# set_property IOSTANDARD  DIFF_POD12 [get_ports "DDR4_C1_DQS5_T"] ;# Bank  72 VCCO - VCC1V2_FPGA - IO_L4P_T0U_N6_DBC_AD7P_72
# set_property PACKAGE_PIN P21      [get_ports "DDR4_C1_DQ43"] ;# Bank  72 VCCO - VCC1V2_FPGA - IO_L3N_T0L_N5_AD15N_72
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C1_DQ43"] ;# Bank  72 VCCO - VCC1V2_FPGA - IO_L3N_T0L_N5_AD15N_72
# set_property PACKAGE_PIN R21      [get_ports "DDR4_C1_DQ42"] ;# Bank  72 VCCO - VCC1V2_FPGA - IO_L3P_T0L_N4_AD15P_72
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C1_DQ42"] ;# Bank  72 VCCO - VCC1V2_FPGA - IO_L3P_T0L_N4_AD15P_72
# set_property PACKAGE_PIN M23      [get_ports "DDR4_C1_DQ41"] ;# Bank  72 VCCO - VCC1V2_FPGA - IO_L2N_T0L_N3_72
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C1_DQ41"] ;# Bank  72 VCCO - VCC1V2_FPGA - IO_L2N_T0L_N3_72
# set_property PACKAGE_PIN N23      [get_ports "DDR4_C1_DQ40"] ;# Bank  72 VCCO - VCC1V2_FPGA - IO_L2P_T0L_N2_72
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C1_DQ40"] ;# Bank  72 VCCO - VCC1V2_FPGA - IO_L2P_T0L_N2_72
# set_property PACKAGE_PIN N20      [get_ports "DDR4_C1_RESET_B"] ;# Bank  72 VCCO - VCC1V2_FPGA - IO_L1N_T0L_N1_DBC_72
# set_property IOSTANDARD  LVCMOS12 [get_ports "DDR4_C1_RESET_B"] ;# Bank  72 VCCO - VCC1V2_FPGA - IO_L1N_T0L_N1_DBC_72
# set_property PACKAGE_PIN P20      [get_ports "DDR4_C1_DM5"] ;# Bank  72 VCCO - VCC1V2_FPGA - IO_L1P_T0L_N0_DBC_72
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C1_DM5"] ;# Bank  72 VCCO - VCC1V2_FPGA - IO_L1P_T0L_N0_DBC_72
# #Other net   PACKAGE_PIN T20      - 5329N4288                 Bank  72 - VREF_72
# set_property PACKAGE_PIN B15      [get_ports "DDR4_C1_A1"] ;# Bank  71 VCCO - VCC1V2_FPGA - IO_L24N_T3U_N11_71
# set_property IOSTANDARD  SSTL12 [get_ports "DDR4_C1_A1"] ;# Bank  71 VCCO - VCC1V2_FPGA - IO_L24N_T3U_N11_71
# set_property PACKAGE_PIN B16      [get_ports "DDR4_C1_A2"] ;# Bank  71 VCCO - VCC1V2_FPGA - IO_L24P_T3U_N10_71
# set_property IOSTANDARD  SSTL12 [get_ports "DDR4_C1_A2"] ;# Bank  71 VCCO - VCC1V2_FPGA - IO_L24P_T3U_N10_71
# set_property PACKAGE_PIN C14      [get_ports "DDR4_C1_A3"] ;# Bank  71 VCCO - VCC1V2_FPGA - IO_L23N_T3U_N9_71
# set_property IOSTANDARD  SSTL12 [get_ports "DDR4_C1_A3"] ;# Bank  71 VCCO - VCC1V2_FPGA - IO_L23N_T3U_N9_71
# set_property PACKAGE_PIN C15      [get_ports "DDR4_C1_A4"] ;# Bank  71 VCCO - VCC1V2_FPGA - IO_L23P_T3U_N8_71
# set_property IOSTANDARD  SSTL12 [get_ports "DDR4_C1_A4"] ;# Bank  71 VCCO - VCC1V2_FPGA - IO_L23P_T3U_N8_71
# set_property PACKAGE_PIN A13      [get_ports "DDR4_C1_A5"] ;# Bank  71 VCCO - VCC1V2_FPGA - IO_L22N_T3U_N7_DBC_AD0N_71
# set_property IOSTANDARD  SSTL12 [get_ports "DDR4_C1_A5"] ;# Bank  71 VCCO - VCC1V2_FPGA - IO_L22N_T3U_N7_DBC_AD0N_71
# set_property PACKAGE_PIN A14      [get_ports "DDR4_C1_A6"] ;# Bank  71 VCCO - VCC1V2_FPGA - IO_L22P_T3U_N6_DBC_AD0P_71
# set_property IOSTANDARD  SSTL12 [get_ports "DDR4_C1_A6"] ;# Bank  71 VCCO - VCC1V2_FPGA - IO_L22P_T3U_N6_DBC_AD0P_71
# set_property PACKAGE_PIN A15      [get_ports "DDR4_C1_A7"] ;# Bank  71 VCCO - VCC1V2_FPGA - IO_L21N_T3L_N5_AD8N_71
# set_property IOSTANDARD  SSTL12 [get_ports "DDR4_C1_A7"] ;# Bank  71 VCCO - VCC1V2_FPGA - IO_L21N_T3L_N5_AD8N_71
# set_property PACKAGE_PIN A16      [get_ports "DDR4_C1_A8"] ;# Bank  71 VCCO - VCC1V2_FPGA - IO_L21P_T3L_N4_AD8P_71
# set_property IOSTANDARD  SSTL12 [get_ports "DDR4_C1_A8"] ;# Bank  71 VCCO - VCC1V2_FPGA - IO_L21P_T3L_N4_AD8P_71
# set_property PACKAGE_PIN B12      [get_ports "DDR4_C1_A9"] ;# Bank  71 VCCO - VCC1V2_FPGA - IO_L20N_T3L_N3_AD1N_71
# set_property IOSTANDARD  SSTL12 [get_ports "DDR4_C1_A9"] ;# Bank  71 VCCO - VCC1V2_FPGA - IO_L20N_T3L_N3_AD1N_71
# set_property PACKAGE_PIN C12      [get_ports "DDR4_C1_A10"] ;# Bank  71 VCCO - VCC1V2_FPGA - IO_L20P_T3L_N2_AD1P_71
# set_property IOSTANDARD  SSTL12 [get_ports "DDR4_C1_A10"] ;# Bank  71 VCCO - VCC1V2_FPGA - IO_L20P_T3L_N2_AD1P_71
# set_property PACKAGE_PIN B13      [get_ports "DDR4_C1_A11"] ;# Bank  71 VCCO - VCC1V2_FPGA - IO_L19N_T3L_N1_DBC_AD9N_71
# set_property IOSTANDARD  SSTL12 [get_ports "DDR4_C1_A11"] ;# Bank  71 VCCO - VCC1V2_FPGA - IO_L19N_T3L_N1_DBC_AD9N_71
# set_property PACKAGE_PIN C13      [get_ports "DDR4_C1_A12"] ;# Bank  71 VCCO - VCC1V2_FPGA - IO_L19P_T3L_N0_DBC_AD9P_71
# set_property IOSTANDARD  SSTL12 [get_ports "DDR4_C1_A12"] ;# Bank  71 VCCO - VCC1V2_FPGA - IO_L19P_T3L_N0_DBC_AD9P_71
# set_property PACKAGE_PIN D14      [get_ports "DDR4_C1_A0"] ;# Bank  71 VCCO - VCC1V2_FPGA - IO_T3U_N12_71
# set_property IOSTANDARD  SSTL12 [get_ports "DDR4_C1_A0"] ;# Bank  71 VCCO - VCC1V2_FPGA - IO_T3U_N12_71
# set_property PACKAGE_PIN D15      [get_ports "DDR4_C1_A13"] ;# Bank  71 VCCO - VCC1V2_FPGA - IO_T2U_N12_71
# set_property IOSTANDARD  SSTL12 [get_ports "DDR4_C1_A13"] ;# Bank  71 VCCO - VCC1V2_FPGA - IO_T2U_N12_71
# set_property PACKAGE_PIN H14      [get_ports "DDR4_C1_A14_WE_B"] ;# Bank  71 VCCO - VCC1V2_FPGA - IO_L18N_T2U_N11_AD2N_71
# set_property IOSTANDARD  SSTL12 [get_ports "DDR4_C1_A14_WE_B"] ;# Bank  71 VCCO - VCC1V2_FPGA - IO_L18N_T2U_N11_AD2N_71
# set_property PACKAGE_PIN H15      [get_ports "DDR4_C1_A15_CAS_B"] ;# Bank  71 VCCO - VCC1V2_FPGA - IO_L18P_T2U_N10_AD2P_71
# set_property IOSTANDARD  SSTL12 [get_ports "DDR4_C1_A15_CAS_B"] ;# Bank  71 VCCO - VCC1V2_FPGA - IO_L18P_T2U_N10_AD2P_71
# set_property PACKAGE_PIN F15      [get_ports "DDR4_C1_A16_RAS_B"] ;# Bank  71 VCCO - VCC1V2_FPGA - IO_L17N_T2U_N9_AD10N_71
# set_property IOSTANDARD  SSTL12 [get_ports "DDR4_C1_A16_RAS_B"] ;# Bank  71 VCCO - VCC1V2_FPGA - IO_L17N_T2U_N9_AD10N_71
# set_property PACKAGE_PIN G15      [get_ports "DDR4_C1_BA0"] ;# Bank  71 VCCO - VCC1V2_FPGA - IO_L17P_T2U_N8_AD10P_71
# set_property IOSTANDARD  SSTL12 [get_ports "DDR4_C1_BA0"] ;# Bank  71 VCCO - VCC1V2_FPGA - IO_L17P_T2U_N8_AD10P_71
# set_property PACKAGE_PIN E14      [get_ports "DDR4_C1_CK_C"] ;# Bank  71 VCCO - VCC1V2_FPGA - IO_L16N_T2U_N7_QBC_AD3N_71
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C1_CK_C"] ;# Bank  71 VCCO - VCC1V2_FPGA - IO_L16N_T2U_N7_QBC_AD3N_71
# set_property PACKAGE_PIN F14      [get_ports "DDR4_C1_CK_T"] ;# Bank  71 VCCO - VCC1V2_FPGA - IO_L16P_T2U_N6_QBC_AD3P_71
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C1_CK_T"] ;# Bank  71 VCCO - VCC1V2_FPGA - IO_L16P_T2U_N6_QBC_AD3P_71
# set_property PACKAGE_PIN G13      [get_ports "DDR4_C1_BA1"] ;# Bank  71 VCCO - VCC1V2_FPGA - IO_L15N_T2L_N5_AD11N_71
# set_property IOSTANDARD  SSTL12 [get_ports "DDR4_C1_BA1"] ;# Bank  71 VCCO - VCC1V2_FPGA - IO_L15N_T2L_N5_AD11N_71
# set_property PACKAGE_PIN H13      [get_ports "DDR4_C1_BG0"] ;# Bank  71 VCCO - VCC1V2_FPGA - IO_L15P_T2L_N4_AD11P_71
# set_property IOSTANDARD  SSTL12 [get_ports "DDR4_C1_BG0"] ;# Bank  71 VCCO - VCC1V2_FPGA - IO_L15P_T2L_N4_AD11P_71
# set_property PACKAGE_PIN E13      [get_ports "DDR4_C1_ACT_B"] ;# Bank  71 VCCO - VCC1V2_FPGA - IO_L14N_T2L_N3_GC_71
# set_property IOSTANDARD  SSTL12 [get_ports "DDR4_C1_ACT_B"] ;# Bank  71 VCCO - VCC1V2_FPGA - IO_L14N_T2L_N3_GC_71
# set_property PACKAGE_PIN F13      [get_ports "DDR4_C1_CS_B"] ;# Bank  71 VCCO - VCC1V2_FPGA - IO_L14P_T2L_N2_GC_71
# set_property IOSTANDARD  SSTL12 [get_ports "DDR4_C1_CS_B"] ;# Bank  71 VCCO - VCC1V2_FPGA - IO_L14P_T2L_N2_GC_71
# set_property PACKAGE_PIN D12      [get_ports "250MHZ_CLK1_N"] ;# Bank  71 VCCO - VCC1V2_FPGA - IO_L13N_T2L_N1_GC_QBC_71
# set_property IOSTANDARD  DIFF_SSTL12 [get_ports "250MHZ_CLK1_N"] ;# Bank  71 VCCO - VCC1V2_FPGA - IO_L13N_T2L_N1_GC_QBC_71
# set_property PACKAGE_PIN E12      [get_ports "250MHZ_CLK1_P"] ;# Bank  71 VCCO - VCC1V2_FPGA - IO_L13P_T2L_N0_GC_QBC_71
# set_property IOSTANDARD  DIFF_SSTL12 [get_ports "250MHZ_CLK1_P"] ;# Bank  71 VCCO - VCC1V2_FPGA - IO_L13P_T2L_N0_GC_QBC_71
# set_property PACKAGE_PIN A11      [get_ports "DDR4_C1_DQ79"] ;# Bank  71 VCCO - VCC1V2_FPGA - IO_L12N_T1U_N11_GC_71
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C1_DQ79"] ;# Bank  71 VCCO - VCC1V2_FPGA - IO_L12N_T1U_N11_GC_71
# set_property PACKAGE_PIN B11      [get_ports "DDR4_C1_DQ78"] ;# Bank  71 VCCO - VCC1V2_FPGA - IO_L12P_T1U_N10_GC_71
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C1_DQ78"] ;# Bank  71 VCCO - VCC1V2_FPGA - IO_L12P_T1U_N10_GC_71
# set_property PACKAGE_PIN B10      [get_ports "DDR4_C1_DQ77"] ;# Bank  71 VCCO - VCC1V2_FPGA - IO_L11N_T1U_N9_GC_71
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C1_DQ77"] ;# Bank  71 VCCO - VCC1V2_FPGA - IO_L11N_T1U_N9_GC_71
# set_property PACKAGE_PIN C10      [get_ports "DDR4_C1_DQ76"] ;# Bank  71 VCCO - VCC1V2_FPGA - IO_L11P_T1U_N8_GC_71
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C1_DQ76"] ;# Bank  71 VCCO - VCC1V2_FPGA - IO_L11P_T1U_N8_GC_71
# set_property PACKAGE_PIN A8       [get_ports "DDR4_C1_DQS9_C"] ;# Bank  71 VCCO - VCC1V2_FPGA - IO_L10N_T1U_N7_QBC_AD4N_71
# set_property IOSTANDARD  DIFF_POD12 [get_ports "DDR4_C1_DQS9_C"] ;# Bank  71 VCCO - VCC1V2_FPGA - IO_L10N_T1U_N7_QBC_AD4N_71
# set_property PACKAGE_PIN A9       [get_ports "DDR4_C1_DQS9_T"] ;# Bank  71 VCCO - VCC1V2_FPGA - IO_L10P_T1U_N6_QBC_AD4P_71
# set_property IOSTANDARD  DIFF_POD12 [get_ports "DDR4_C1_DQS9_T"] ;# Bank  71 VCCO - VCC1V2_FPGA - IO_L10P_T1U_N6_QBC_AD4P_71
# set_property PACKAGE_PIN B7       [get_ports "DDR4_C1_DQ75"] ;# Bank  71 VCCO - VCC1V2_FPGA - IO_L9N_T1L_N5_AD12N_71
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C1_DQ75"] ;# Bank  71 VCCO - VCC1V2_FPGA - IO_L9N_T1L_N5_AD12N_71
# set_property PACKAGE_PIN B8       [get_ports "DDR4_C1_DQ74"] ;# Bank  71 VCCO - VCC1V2_FPGA - IO_L9P_T1L_N4_AD12P_71
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C1_DQ74"] ;# Bank  71 VCCO - VCC1V2_FPGA - IO_L9P_T1L_N4_AD12P_71
# set_property PACKAGE_PIN C7       [get_ports "DDR4_C1_DQ73"] ;# Bank  71 VCCO - VCC1V2_FPGA - IO_L8N_T1L_N3_AD5N_71
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C1_DQ73"] ;# Bank  71 VCCO - VCC1V2_FPGA - IO_L8N_T1L_N3_AD5N_71
# set_property PACKAGE_PIN D7       [get_ports "DDR4_C1_DQ72"] ;# Bank  71 VCCO - VCC1V2_FPGA - IO_L8P_T1L_N2_AD5P_71
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C1_DQ72"] ;# Bank  71 VCCO - VCC1V2_FPGA - IO_L8P_T1L_N2_AD5P_71
# set_property PACKAGE_PIN C8       [get_ports "DDR4_C1_ODT"] ;# Bank  71 VCCO - VCC1V2_FPGA - IO_L7N_T1L_N1_QBC_AD13N_71
# set_property IOSTANDARD  SSTL12 [get_ports "DDR4_C1_ODT"] ;# Bank  71 VCCO - VCC1V2_FPGA - IO_L7N_T1L_N1_QBC_AD13N_71
# set_property PACKAGE_PIN C9       [get_ports "DDR4_C1_DM9"] ;# Bank  71 VCCO - VCC1V2_FPGA - IO_L7P_T1L_N0_QBC_AD13P_71
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C1_DM9"] ;# Bank  71 VCCO - VCC1V2_FPGA - IO_L7P_T1L_N0_QBC_AD13P_71
# set_property PACKAGE_PIN A10      [get_ports "DDR4_C1_CKE"] ;# Bank  71 VCCO - VCC1V2_FPGA - IO_T1U_N12_71
# set_property IOSTANDARD  SSTL12 [get_ports "DDR4_C1_CKE"] ;# Bank  71 VCCO - VCC1V2_FPGA - IO_T1U_N12_71
# #set_property PACKAGE_PIN D8       [get_ports "VRP_71"] ;# Bank  71 VCCO - VCC1V2_FPGA - IO_T0U_N12_VRP_71
# #set_property IOSTANDARD  LVCMOSxx [get_ports "VRP_71"] ;# Bank  71 VCCO - VCC1V2_FPGA - IO_T0U_N12_VRP_71
# set_property PACKAGE_PIN D9       [get_ports "DDR4_C1_DQ7"] ;# Bank  71 VCCO - VCC1V2_FPGA - IO_L6N_T0U_N11_AD6N_71
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C1_DQ7"] ;# Bank  71 VCCO - VCC1V2_FPGA - IO_L6N_T0U_N11_AD6N_71
# set_property PACKAGE_PIN E9       [get_ports "DDR4_C1_DQ6"] ;# Bank  71 VCCO - VCC1V2_FPGA - IO_L6P_T0U_N10_AD6P_71
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C1_DQ6"] ;# Bank  71 VCCO - VCC1V2_FPGA - IO_L6P_T0U_N10_AD6P_71
# set_property PACKAGE_PIN G12      [get_ports "DDR4_C1_DQ5"] ;# Bank  71 VCCO - VCC1V2_FPGA - IO_L5N_T0U_N9_AD14N_71
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C1_DQ5"] ;# Bank  71 VCCO - VCC1V2_FPGA - IO_L5N_T0U_N9_AD14N_71
# set_property PACKAGE_PIN H12      [get_ports "DDR4_C1_DQ4"] ;# Bank  71 VCCO - VCC1V2_FPGA - IO_L5P_T0U_N8_AD14P_71
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C1_DQ4"] ;# Bank  71 VCCO - VCC1V2_FPGA - IO_L5P_T0U_N8_AD14P_71
# set_property PACKAGE_PIN D10      [get_ports "DDR4_C1_DQS0_C"] ;# Bank  71 VCCO - VCC1V2_FPGA - IO_L4N_T0U_N7_DBC_AD7N_71
# set_property IOSTANDARD  DIFF_POD12 [get_ports "DDR4_C1_DQS0_C"] ;# Bank  71 VCCO - VCC1V2_FPGA - IO_L4N_T0U_N7_DBC_AD7N_71
# set_property PACKAGE_PIN D11      [get_ports "DDR4_C1_DQS0_T"] ;# Bank  71 VCCO - VCC1V2_FPGA - IO_L4P_T0U_N6_DBC_AD7P_71
# set_property IOSTANDARD  DIFF_POD12 [get_ports "DDR4_C1_DQS0_T"] ;# Bank  71 VCCO - VCC1V2_FPGA - IO_L4P_T0U_N6_DBC_AD7P_71
# set_property PACKAGE_PIN F9       [get_ports "DDR4_C1_DQ3"] ;# Bank  71 VCCO - VCC1V2_FPGA - IO_L3N_T0L_N5_AD15N_71
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C1_DQ3"] ;# Bank  71 VCCO - VCC1V2_FPGA - IO_L3N_T0L_N5_AD15N_71
# set_property PACKAGE_PIN F10      [get_ports "DDR4_C1_DQ2"] ;# Bank  71 VCCO - VCC1V2_FPGA - IO_L3P_T0L_N4_AD15P_71
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C1_DQ2"] ;# Bank  71 VCCO - VCC1V2_FPGA - IO_L3P_T0L_N4_AD15P_71
# set_property PACKAGE_PIN E11      [get_ports "DDR4_C1_DQ1"] ;# Bank  71 VCCO - VCC1V2_FPGA - IO_L2N_T0L_N3_71
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C1_DQ1"] ;# Bank  71 VCCO - VCC1V2_FPGA - IO_L2N_T0L_N3_71
# set_property PACKAGE_PIN F11      [get_ports "DDR4_C1_DQ0"] ;# Bank  71 VCCO - VCC1V2_FPGA - IO_L2P_T0L_N2_71
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C1_DQ0"] ;# Bank  71 VCCO - VCC1V2_FPGA - IO_L2P_T0L_N2_71
# set_property PACKAGE_PIN G10      [get_ports "DDR4_C1_PAR"] ;# Bank  71 VCCO - VCC1V2_FPGA - IO_L1N_T0L_N1_DBC_71
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C1_PAR"] ;# Bank  71 VCCO - VCC1V2_FPGA - IO_L1N_T0L_N1_DBC_71
# set_property PACKAGE_PIN G11      [get_ports "DDR4_C1_DM0"] ;# Bank  71 VCCO - VCC1V2_FPGA - IO_L1P_T0L_N0_DBC_71
# set_property IOSTANDARD  POD12 [get_ports "DDR4_C1_DM0"] ;# Bank  71 VCCO - VCC1V2_FPGA - IO_L1P_T0L_N0_DBC_71
# #Other net   PACKAGE_PIN J15      - 7N8237                    Bank  71 - VREF_71
# set_property PACKAGE_PIN J12      [get_ports "FMCP_HSPC_HA22_N"] ;# Bank  70 VCCO - VADJ_1V8_FPGA - IO_L24N_T3U_N11_70
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_HA22_N"] ;# Bank  70 VCCO - VADJ_1V8_FPGA - IO_L24N_T3U_N11_70
# set_property PACKAGE_PIN K12      [get_ports "FMCP_HSPC_HA22_P"] ;# Bank  70 VCCO - VADJ_1V8_FPGA - IO_L24P_T3U_N10_70
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_HA22_P"] ;# Bank  70 VCCO - VADJ_1V8_FPGA - IO_L24P_T3U_N10_70
# set_property PACKAGE_PIN K13      [get_ports "FMCP_HSPC_HA21_N"] ;# Bank  70 VCCO - VADJ_1V8_FPGA - IO_L23N_T3U_N9_70
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_HA21_N"] ;# Bank  70 VCCO - VADJ_1V8_FPGA - IO_L23N_T3U_N9_70
# set_property PACKAGE_PIN K14      [get_ports "FMCP_HSPC_HA21_P"] ;# Bank  70 VCCO - VADJ_1V8_FPGA - IO_L23P_T3U_N8_70
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_HA21_P"] ;# Bank  70 VCCO - VADJ_1V8_FPGA - IO_L23P_T3U_N8_70
# set_property PACKAGE_PIN L11      [get_ports "FMCP_HSPC_HA14_N"] ;# Bank  70 VCCO - VADJ_1V8_FPGA - IO_L22N_T3U_N7_DBC_AD0N_70
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_HA14_N"] ;# Bank  70 VCCO - VADJ_1V8_FPGA - IO_L22N_T3U_N7_DBC_AD0N_70
# set_property PACKAGE_PIN M11      [get_ports "FMCP_HSPC_HA14_P"] ;# Bank  70 VCCO - VADJ_1V8_FPGA - IO_L22P_T3U_N6_DBC_AD0P_70
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_HA14_P"] ;# Bank  70 VCCO - VADJ_1V8_FPGA - IO_L22P_T3U_N6_DBC_AD0P_70
# set_property PACKAGE_PIN J11      [get_ports "FMCP_HSPC_HA23_N"] ;# Bank  70 VCCO - VADJ_1V8_FPGA - IO_L21N_T3L_N5_AD8N_70
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_HA23_N"] ;# Bank  70 VCCO - VADJ_1V8_FPGA - IO_L21N_T3L_N5_AD8N_70
# set_property PACKAGE_PIN K11      [get_ports "FMCP_HSPC_HA23_P"] ;# Bank  70 VCCO - VADJ_1V8_FPGA - IO_L21P_T3L_N4_AD8P_70
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_HA23_P"] ;# Bank  70 VCCO - VADJ_1V8_FPGA - IO_L21P_T3L_N4_AD8P_70
# set_property PACKAGE_PIN L13      [get_ports "FMCP_HSPC_HA19_N"] ;# Bank  70 VCCO - VADJ_1V8_FPGA - IO_L20N_T3L_N3_AD1N_70
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_HA19_N"] ;# Bank  70 VCCO - VADJ_1V8_FPGA - IO_L20N_T3L_N3_AD1N_70
# set_property PACKAGE_PIN L14      [get_ports "FMCP_HSPC_HA19_P"] ;# Bank  70 VCCO - VADJ_1V8_FPGA - IO_L20P_T3L_N2_AD1P_70
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_HA19_P"] ;# Bank  70 VCCO - VADJ_1V8_FPGA - IO_L20P_T3L_N2_AD1P_70
# set_property PACKAGE_PIN M12      [get_ports "FMCP_HSPC_HA15_N"] ;# Bank  70 VCCO - VADJ_1V8_FPGA - IO_L19N_T3L_N1_DBC_AD9N_70
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_HA15_N"] ;# Bank  70 VCCO - VADJ_1V8_FPGA - IO_L19N_T3L_N1_DBC_AD9N_70
# set_property PACKAGE_PIN M13      [get_ports "FMCP_HSPC_HA15_P"] ;# Bank  70 VCCO - VADJ_1V8_FPGA - IO_L19P_T3L_N0_DBC_AD9P_70
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_HA15_P"] ;# Bank  70 VCCO - VADJ_1V8_FPGA - IO_L19P_T3L_N0_DBC_AD9P_70
# set_property PACKAGE_PIN J14      [get_ports "30N3618"] ;# Bank  70 VCCO - VADJ_1V8_FPGA - IO_T3U_N12_70
# set_property IOSTANDARD  LVCMOSxx [get_ports "30N3618"] ;# Bank  70 VCCO - VADJ_1V8_FPGA - IO_T3U_N12_70
# set_property PACKAGE_PIN N12      [get_ports "30N3617"] ;# Bank  70 VCCO - VADJ_1V8_FPGA - IO_T2U_N12_70
# set_property IOSTANDARD  LVCMOSxx [get_ports "30N3617"] ;# Bank  70 VCCO - VADJ_1V8_FPGA - IO_T2U_N12_70
# set_property PACKAGE_PIN P12      [get_ports "FMCP_HSPC_HA11_N"] ;# Bank  70 VCCO - VADJ_1V8_FPGA - IO_L18N_T2U_N11_AD2N_70
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_HA11_N"] ;# Bank  70 VCCO - VADJ_1V8_FPGA - IO_L18N_T2U_N11_AD2N_70
# set_property PACKAGE_PIN R12      [get_ports "FMCP_HSPC_HA11_P"] ;# Bank  70 VCCO - VADJ_1V8_FPGA - IO_L18P_T2U_N10_AD2P_70
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_HA11_P"] ;# Bank  70 VCCO - VADJ_1V8_FPGA - IO_L18P_T2U_N10_AD2P_70
# set_property PACKAGE_PIN L15      [get_ports "FMCP_HSPC_HA20_N"] ;# Bank  70 VCCO - VADJ_1V8_FPGA - IO_L17N_T2U_N9_AD10N_70
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_HA20_N"] ;# Bank  70 VCCO - VADJ_1V8_FPGA - IO_L17N_T2U_N9_AD10N_70
# set_property PACKAGE_PIN M15      [get_ports "FMCP_HSPC_HA20_P"] ;# Bank  70 VCCO - VADJ_1V8_FPGA - IO_L17P_T2U_N8_AD10P_70
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_HA20_P"] ;# Bank  70 VCCO - VADJ_1V8_FPGA - IO_L17P_T2U_N8_AD10P_70
# set_property PACKAGE_PIN P11      [get_ports "FMCP_HSPC_HA17_CC_N"] ;# Bank  70 VCCO - VADJ_1V8_FPGA - IO_L16N_T2U_N7_QBC_AD3N_70
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_HA17_CC_N"] ;# Bank  70 VCCO - VADJ_1V8_FPGA - IO_L16N_T2U_N7_QBC_AD3N_70
# set_property PACKAGE_PIN R11      [get_ports "FMCP_HSPC_HA17_CC_P"] ;# Bank  70 VCCO - VADJ_1V8_FPGA - IO_L16P_T2U_N6_QBC_AD3P_70
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_HA17_CC_P"] ;# Bank  70 VCCO - VADJ_1V8_FPGA - IO_L16P_T2U_N6_QBC_AD3P_70
# set_property PACKAGE_PIN N15      [get_ports "FMCP_HSPC_HA18_N"] ;# Bank  70 VCCO - VADJ_1V8_FPGA - IO_L15N_T2L_N5_AD11N_70
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_HA18_N"] ;# Bank  70 VCCO - VADJ_1V8_FPGA - IO_L15N_T2L_N5_AD11N_70
# set_property PACKAGE_PIN P15      [get_ports "FMCP_HSPC_HA18_P"] ;# Bank  70 VCCO - VADJ_1V8_FPGA - IO_L15P_T2L_N4_AD11P_70
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_HA18_P"] ;# Bank  70 VCCO - VADJ_1V8_FPGA - IO_L15P_T2L_N4_AD11P_70
# set_property PACKAGE_PIN P14      [get_ports "FMCP_HSPC_HA05_N"] ;# Bank  70 VCCO - VADJ_1V8_FPGA - IO_L14N_T2L_N3_GC_70
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_HA05_N"] ;# Bank  70 VCCO - VADJ_1V8_FPGA - IO_L14N_T2L_N3_GC_70
# set_property PACKAGE_PIN R14      [get_ports "FMCP_HSPC_HA05_P"] ;# Bank  70 VCCO - VADJ_1V8_FPGA - IO_L14P_T2L_N2_GC_70
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_HA05_P"] ;# Bank  70 VCCO - VADJ_1V8_FPGA - IO_L14P_T2L_N2_GC_70
# set_property PACKAGE_PIN N13      [get_ports "FMCP_HSPC_HA00_CC_N"] ;# Bank  70 VCCO - VADJ_1V8_FPGA - IO_L13N_T2L_N1_GC_QBC_70
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_HA00_CC_N"] ;# Bank  70 VCCO - VADJ_1V8_FPGA - IO_L13N_T2L_N1_GC_QBC_70
# set_property PACKAGE_PIN N14      [get_ports "FMCP_HSPC_HA00_CC_P"] ;# Bank  70 VCCO - VADJ_1V8_FPGA - IO_L13P_T2L_N0_GC_QBC_70
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_HA00_CC_P"] ;# Bank  70 VCCO - VADJ_1V8_FPGA - IO_L13P_T2L_N0_GC_QBC_70
# set_property PACKAGE_PIN T13      [get_ports "FMCP_HSPC_HA06_N"] ;# Bank  70 VCCO - VADJ_1V8_FPGA - IO_L12N_T1U_N11_GC_70
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_HA06_N"] ;# Bank  70 VCCO - VADJ_1V8_FPGA - IO_L12N_T1U_N11_GC_70
# set_property PACKAGE_PIN U13      [get_ports "FMCP_HSPC_HA06_P"] ;# Bank  70 VCCO - VADJ_1V8_FPGA - IO_L12P_T1U_N10_GC_70
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_HA06_P"] ;# Bank  70 VCCO - VADJ_1V8_FPGA - IO_L12P_T1U_N10_GC_70
# set_property PACKAGE_PIN R13      [get_ports "FMCP_HSPC_HA16_N"] ;# Bank  70 VCCO - VADJ_1V8_FPGA - IO_L11N_T1U_N9_GC_70
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_HA16_N"] ;# Bank  70 VCCO - VADJ_1V8_FPGA - IO_L11N_T1U_N9_GC_70
# set_property PACKAGE_PIN T14      [get_ports "FMCP_HSPC_HA16_P"] ;# Bank  70 VCCO - VADJ_1V8_FPGA - IO_L11P_T1U_N8_GC_70
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_HA16_P"] ;# Bank  70 VCCO - VADJ_1V8_FPGA - IO_L11P_T1U_N8_GC_70
# set_property PACKAGE_PIN T11      [get_ports "FMCP_HSPC_HA08_N"] ;# Bank  70 VCCO - VADJ_1V8_FPGA - IO_L10N_T1U_N7_QBC_AD4N_70
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_HA08_N"] ;# Bank  70 VCCO - VADJ_1V8_FPGA - IO_L10N_T1U_N7_QBC_AD4N_70
# set_property PACKAGE_PIN U11      [get_ports "FMCP_HSPC_HA08_P"] ;# Bank  70 VCCO - VADJ_1V8_FPGA - IO_L10P_T1U_N6_QBC_AD4P_70
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_HA08_P"] ;# Bank  70 VCCO - VADJ_1V8_FPGA - IO_L10P_T1U_N6_QBC_AD4P_70
# set_property PACKAGE_PIN T15      [get_ports "FMCP_HSPC_HA12_N"] ;# Bank  70 VCCO - VADJ_1V8_FPGA - IO_L9N_T1L_N5_AD12N_70
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_HA12_N"] ;# Bank  70 VCCO - VADJ_1V8_FPGA - IO_L9N_T1L_N5_AD12N_70
# set_property PACKAGE_PIN T16      [get_ports "FMCP_HSPC_HA12_P"] ;# Bank  70 VCCO - VADJ_1V8_FPGA - IO_L9P_T1L_N4_AD12P_70
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_HA12_P"] ;# Bank  70 VCCO - VADJ_1V8_FPGA - IO_L9P_T1L_N4_AD12P_70
# set_property PACKAGE_PIN U16      [get_ports "FMCP_HSPC_HA10_N"] ;# Bank  70 VCCO - VADJ_1V8_FPGA - IO_L8N_T1L_N3_AD5N_70
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_HA10_N"] ;# Bank  70 VCCO - VADJ_1V8_FPGA - IO_L8N_T1L_N3_AD5N_70
# set_property PACKAGE_PIN V16      [get_ports "FMCP_HSPC_HA10_P"] ;# Bank  70 VCCO - VADJ_1V8_FPGA - IO_L8P_T1L_N2_AD5P_70
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_HA10_P"] ;# Bank  70 VCCO - VADJ_1V8_FPGA - IO_L8P_T1L_N2_AD5P_70
# set_property PACKAGE_PIN U15      [get_ports "FMCP_HSPC_HA01_CC_N"] ;# Bank  70 VCCO - VADJ_1V8_FPGA - IO_L7N_T1L_N1_QBC_AD13N_70
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_HA01_CC_N"] ;# Bank  70 VCCO - VADJ_1V8_FPGA - IO_L7N_T1L_N1_QBC_AD13N_70
# set_property PACKAGE_PIN V15      [get_ports "FMCP_HSPC_HA01_CC_P"] ;# Bank  70 VCCO - VADJ_1V8_FPGA - IO_L7P_T1L_N0_QBC_AD13P_70
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_HA01_CC_P"] ;# Bank  70 VCCO - VADJ_1V8_FPGA - IO_L7P_T1L_N0_QBC_AD13P_70
# set_property PACKAGE_PIN R16      [get_ports "30N3619"] ;# Bank  70 VCCO - VADJ_1V8_FPGA - IO_T1U_N12_70
# set_property IOSTANDARD  LVCMOSxx [get_ports "30N3619"] ;# Bank  70 VCCO - VADJ_1V8_FPGA - IO_T1U_N12_70
# #set_property PACKAGE_PIN W15      [get_ports "VRP_70"] ;# Bank  70 VCCO - VADJ_1V8_FPGA - IO_T0U_N12_VRP_70
# #set_property IOSTANDARD  LVCMOSxx [get_ports "VRP_70"] ;# Bank  70 VCCO - VADJ_1V8_FPGA - IO_T0U_N12_VRP_70
# set_property PACKAGE_PIN V14      [get_ports "FMCP_HSPC_HA09_N"] ;# Bank  70 VCCO - VADJ_1V8_FPGA - IO_L6N_T0U_N11_AD6N_70
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_HA09_N"] ;# Bank  70 VCCO - VADJ_1V8_FPGA - IO_L6N_T0U_N11_AD6N_70
# set_property PACKAGE_PIN W14      [get_ports "FMCP_HSPC_HA09_P"] ;# Bank  70 VCCO - VADJ_1V8_FPGA - IO_L6P_T0U_N10_AD6P_70
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_HA09_P"] ;# Bank  70 VCCO - VADJ_1V8_FPGA - IO_L6P_T0U_N10_AD6P_70
# set_property PACKAGE_PIN Y12      [get_ports "FMCP_HSPC_HA02_N"] ;# Bank  70 VCCO - VADJ_1V8_FPGA - IO_L5N_T0U_N9_AD14N_70
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_HA02_N"] ;# Bank  70 VCCO - VADJ_1V8_FPGA - IO_L5N_T0U_N9_AD14N_70
# set_property PACKAGE_PIN AA12     [get_ports "FMCP_HSPC_HA02_P"] ;# Bank  70 VCCO - VADJ_1V8_FPGA - IO_L5P_T0U_N8_AD14P_70
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_HA02_P"] ;# Bank  70 VCCO - VADJ_1V8_FPGA - IO_L5P_T0U_N8_AD14P_70
# set_property PACKAGE_PIN U12      [get_ports "FMCP_HSPC_HA13_N"] ;# Bank  70 VCCO - VADJ_1V8_FPGA - IO_L4N_T0U_N7_DBC_AD7N_70
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_HA13_N"] ;# Bank  70 VCCO - VADJ_1V8_FPGA - IO_L4N_T0U_N7_DBC_AD7N_70
# set_property PACKAGE_PIN V13      [get_ports "FMCP_HSPC_HA13_P"] ;# Bank  70 VCCO - VADJ_1V8_FPGA - IO_L4P_T0U_N6_DBC_AD7P_70
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_HA13_P"] ;# Bank  70 VCCO - VADJ_1V8_FPGA - IO_L4P_T0U_N6_DBC_AD7P_70
# set_property PACKAGE_PIN V12      [get_ports "FMCP_HSPC_HA03_N"] ;# Bank  70 VCCO - VADJ_1V8_FPGA - IO_L3N_T0L_N5_AD15N_70
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_HA03_N"] ;# Bank  70 VCCO - VADJ_1V8_FPGA - IO_L3N_T0L_N5_AD15N_70
# set_property PACKAGE_PIN W12      [get_ports "FMCP_HSPC_HA03_P"] ;# Bank  70 VCCO - VADJ_1V8_FPGA - IO_L3P_T0L_N4_AD15P_70
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_HA03_P"] ;# Bank  70 VCCO - VADJ_1V8_FPGA - IO_L3P_T0L_N4_AD15P_70
# set_property PACKAGE_PIN Y14      [get_ports "FMCP_HSPC_HA07_N"] ;# Bank  70 VCCO - VADJ_1V8_FPGA - IO_L2N_T0L_N3_70
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_HA07_N"] ;# Bank  70 VCCO - VADJ_1V8_FPGA - IO_L2N_T0L_N3_70
# set_property PACKAGE_PIN AA14     [get_ports "FMCP_HSPC_HA07_P"] ;# Bank  70 VCCO - VADJ_1V8_FPGA - IO_L2P_T0L_N2_70
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_HA07_P"] ;# Bank  70 VCCO - VADJ_1V8_FPGA - IO_L2P_T0L_N2_70
# set_property PACKAGE_PIN Y13      [get_ports "FMCP_HSPC_HA04_N"] ;# Bank  70 VCCO - VADJ_1V8_FPGA - IO_L1N_T0L_N1_DBC_70
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_HA04_N"] ;# Bank  70 VCCO - VADJ_1V8_FPGA - IO_L1N_T0L_N1_DBC_70
# set_property PACKAGE_PIN AA13     [get_ports "FMCP_HSPC_HA04_P"] ;# Bank  70 VCCO - VADJ_1V8_FPGA - IO_L1P_T0L_N0_DBC_70
# set_property IOSTANDARD  LVDS [get_ports "FMCP_HSPC_HA04_P"] ;# Bank  70 VCCO - VADJ_1V8_FPGA - IO_L1P_T0L_N0_DBC_70
# #Other net   PACKAGE_PIN AB13     - VREF_70                   Bank  70 - VREF_70
# set_property PACKAGE_PIN AV43     [get_ports "FMCP_HSPC_DP23_C2M_N"] ;# Bank 120 - MGTYTXN3_120
# set_property PACKAGE_PIN AV42     [get_ports "FMCP_HSPC_DP23_C2M_P"] ;# Bank 120 - MGTYTXP3_120
# set_property PACKAGE_PIN AU45     [get_ports "FMCP_HSPC_DP23_M2C_P"] ;# Bank 120 - MGTYRXP3_120
# set_property PACKAGE_PIN AU46     [get_ports "FMCP_HSPC_DP23_M2C_N"] ;# Bank 120 - MGTYRXN3_120
# set_property PACKAGE_PIN AM39     [get_ports "FMCP_HSPC_GBT1_5_N"] ;# Bank 120 - MGTREFCLK1N_120
# set_property PACKAGE_PIN AM38     [get_ports "FMCP_HSPC_GBT1_5_P"] ;# Bank 120 - MGTREFCLK1P_120
# set_property PACKAGE_PIN AY43     [get_ports "FMCP_HSPC_DP22_C2M_N"] ;# Bank 120 - MGTYTXN2_120
# set_property PACKAGE_PIN AY42     [get_ports "FMCP_HSPC_DP22_C2M_P"] ;# Bank 120 - MGTYTXP2_120
# set_property PACKAGE_PIN AW45     [get_ports "FMCP_HSPC_DP22_M2C_P"] ;# Bank 120 - MGTYRXP2_120
# set_property PACKAGE_PIN AW46     [get_ports "FMCP_HSPC_DP22_M2C_N"] ;# Bank 120 - MGTYRXN2_120
# set_property PACKAGE_PIN BB43     [get_ports "FMCP_HSPC_DP21_C2M_N"] ;# Bank 120 - MGTYTXN1_120
# set_property PACKAGE_PIN BB42     [get_ports "FMCP_HSPC_DP21_C2M_P"] ;# Bank 120 - MGTYTXP1_120
# set_property PACKAGE_PIN BA45     [get_ports "FMCP_HSPC_DP21_M2C_P"] ;# Bank 120 - MGTYRXP1_120
# set_property PACKAGE_PIN BA46     [get_ports "FMCP_HSPC_DP21_M2C_N"] ;# Bank 120 - MGTYRXN1_120
# set_property PACKAGE_PIN AN41     [get_ports "FMCP_HSPC_GBTCLK5_M2C_C_N"] ;# Bank 120 - MGTREFCLK0N_120
# set_property PACKAGE_PIN AN40     [get_ports "FMCP_HSPC_GBTCLK5_M2C_C_P"] ;# Bank 120 - MGTREFCLK0P_120
# set_property PACKAGE_PIN BD43     [get_ports "FMCP_HSPC_DP20_C2M_N"] ;# Bank 120 - MGTYTXN0_120
# set_property PACKAGE_PIN BD42     [get_ports "FMCP_HSPC_DP20_C2M_P"] ;# Bank 120 - MGTYTXP0_120
# set_property PACKAGE_PIN BC45     [get_ports "FMCP_HSPC_DP20_M2C_P"] ;# Bank 120 - MGTYRXP0_120
# set_property PACKAGE_PIN BC46     [get_ports "FMCP_HSPC_DP20_M2C_N"] ;# Bank 120 - MGTYRXN0_120
# set_property PACKAGE_PIN AL41     [get_ports "FMCP_HSPC_DP3_C2M_N"] ;# Bank 121 - MGTYTXN3_121
# set_property PACKAGE_PIN AL40     [get_ports "FMCP_HSPC_DP3_C2M_P"] ;# Bank 121 - MGTYTXP3_121
# set_property PACKAGE_PIN AJ45     [get_ports "FMCP_HSPC_DP3_M2C_P"] ;# Bank 121 - MGTYRXP3_121
# set_property PACKAGE_PIN AJ46     [get_ports "FMCP_HSPC_DP3_M2C_N"] ;# Bank 121 - MGTYRXN3_121
# set_property PACKAGE_PIN AH39     [get_ports "FMCP_HSPC_GBT1_0_N"] ;# Bank 121 - MGTREFCLK1N_121
# set_property PACKAGE_PIN AH38     [get_ports "FMCP_HSPC_GBT1_0_P"] ;# Bank 121 - MGTREFCLK1P_121
# set_property PACKAGE_PIN AM43     [get_ports "FMCP_HSPC_DP2_C2M_N"] ;# Bank 121 - MGTYTXN2_121
# set_property PACKAGE_PIN AM42     [get_ports "FMCP_HSPC_DP2_C2M_P"] ;# Bank 121 - MGTYTXP2_121
# set_property PACKAGE_PIN AL45     [get_ports "FMCP_HSPC_DP2_M2C_P"] ;# Bank 121 - MGTYRXP2_121
# set_property PACKAGE_PIN AL46     [get_ports "FMCP_HSPC_DP2_M2C_N"] ;# Bank 121 - MGTYRXN2_121
# #Other net   PACKAGE_PIN BF42     - MGTAVTT_FPGA              Bank 121 - MGTAVTTRCAL_LS
# set_property PACKAGE_PIN BF43     [get_ports "MGTRREF_121"] ;# Bank 121 - MGTRREF_LS
# set_property PACKAGE_PIN AP43     [get_ports "FMCP_HSPC_DP1_C2M_N"] ;# Bank 121 - MGTYTXN1_121
# set_property PACKAGE_PIN AP42     [get_ports "FMCP_HSPC_DP1_C2M_P"] ;# Bank 121 - MGTYTXP1_121
# set_property PACKAGE_PIN AN45     [get_ports "FMCP_HSPC_DP1_M2C_P"] ;# Bank 121 - MGTYRXP1_121
# set_property PACKAGE_PIN AN46     [get_ports "FMCP_HSPC_DP1_M2C_N"] ;# Bank 121 - MGTYRXN1_121
# set_property PACKAGE_PIN AK39     [get_ports "FMCP_HSPC_GBT0_0_N"] ;# Bank 121 - MGTREFCLK0N_121
# set_property PACKAGE_PIN AK38     [get_ports "FMCP_HSPC_GBT0_0_P"] ;# Bank 121 - MGTREFCLK0P_121
# set_property PACKAGE_PIN AT43     [get_ports "FMCP_HSPC_DP0_C2M_N"] ;# Bank 121 - MGTYTXN0_121
# set_property PACKAGE_PIN AT42     [get_ports "FMCP_HSPC_DP0_C2M_P"] ;# Bank 121 - MGTYTXP0_121
# set_property PACKAGE_PIN AR45     [get_ports "FMCP_HSPC_DP0_M2C_P"] ;# Bank 121 - MGTYRXP0_121
# set_property PACKAGE_PIN AR46     [get_ports "FMCP_HSPC_DP0_M2C_N"] ;# Bank 121 - MGTYRXN0_121
# set_property PACKAGE_PIN AE41     [get_ports "FMCP_HSPC_DP11_C2M_N"] ;# Bank 122 - MGTYTXN3_122
# set_property PACKAGE_PIN AE40     [get_ports "FMCP_HSPC_DP11_C2M_P"] ;# Bank 122 - MGTYTXP3_122
# set_property PACKAGE_PIN AD43     [get_ports "FMCP_HSPC_DP11_M2C_P"] ;# Bank 122 - MGTYRXP3_122
# set_property PACKAGE_PIN AD44     [get_ports "FMCP_HSPC_DP11_M2C_N"] ;# Bank 122 - MGTYRXN3_122
# set_property PACKAGE_PIN AD39     [get_ports "FMCP_HSPC_GBT1_2_N"] ;# Bank 122 - MGTREFCLK1N_122
# set_property PACKAGE_PIN AD38     [get_ports "FMCP_HSPC_GBT1_2_P"] ;# Bank 122 - MGTREFCLK1P_122
# set_property PACKAGE_PIN AG41     [get_ports "FMCP_HSPC_DP10_C2M_N"] ;# Bank 122 - MGTYTXN2_122
# set_property PACKAGE_PIN AG40     [get_ports "FMCP_HSPC_DP10_C2M_P"] ;# Bank 122 - MGTYTXP2_122
# set_property PACKAGE_PIN AE45     [get_ports "FMCP_HSPC_DP10_M2C_P"] ;# Bank 122 - MGTYRXP2_122
# set_property PACKAGE_PIN AE46     [get_ports "FMCP_HSPC_DP10_M2C_N"] ;# Bank 122 - MGTYRXN2_122
# set_property PACKAGE_PIN AJ41     [get_ports "FMCP_HSPC_DP9_C2M_N"] ;# Bank 122 - MGTYTXN1_122
# set_property PACKAGE_PIN AJ40     [get_ports "FMCP_HSPC_DP9_C2M_P"] ;# Bank 122 - MGTYTXP1_122
# set_property PACKAGE_PIN AF43     [get_ports "FMCP_HSPC_DP9_M2C_P"] ;# Bank 122 - MGTYRXP1_122
# set_property PACKAGE_PIN AF44     [get_ports "FMCP_HSPC_DP9_M2C_N"] ;# Bank 122 - MGTYRXN1_122
# set_property PACKAGE_PIN AF39     [get_ports "FMCP_HSPC_GBTCLK2_M2C_C_N"] ;# Bank 122 - MGTREFCLK0N_122
# set_property PACKAGE_PIN AF38     [get_ports "FMCP_HSPC_GBTCLK2_M2C_C_P"] ;# Bank 122 - MGTREFCLK0P_122
# set_property PACKAGE_PIN AK43     [get_ports "FMCP_HSPC_DP8_C2M_N"] ;# Bank 122 - MGTYTXN0_122
# set_property PACKAGE_PIN AK42     [get_ports "FMCP_HSPC_DP8_C2M_P"] ;# Bank 122 - MGTYTXP0_122
# set_property PACKAGE_PIN AG45     [get_ports "FMCP_HSPC_DP8_M2C_P"] ;# Bank 122 - MGTYRXP0_122
# set_property PACKAGE_PIN AG46     [get_ports "FMCP_HSPC_DP8_M2C_N"] ;# Bank 122 - MGTYRXN0_122
# set_property PACKAGE_PIN U41      [get_ports "FMCP_HSPC_DP15_C2M_N"] ;# Bank 125 - MGTYTXN3_125
# set_property PACKAGE_PIN U40      [get_ports "FMCP_HSPC_DP15_C2M_P"] ;# Bank 125 - MGTYTXP3_125
# set_property PACKAGE_PIN Y43      [get_ports "FMCP_HSPC_DP15_M2C_P"] ;# Bank 125 - MGTYRXP3_125
# set_property PACKAGE_PIN Y44      [get_ports "FMCP_HSPC_DP15_M2C_N"] ;# Bank 125 - MGTYRXN3_125
# set_property PACKAGE_PIN Y39      [get_ports "FMCP_HSPC_GBT1_3_N"] ;# Bank 125 - MGTREFCLK1N_125
# set_property PACKAGE_PIN Y38      [get_ports "FMCP_HSPC_GBT1_3_P"] ;# Bank 125 - MGTREFCLK1P_125
# set_property PACKAGE_PIN W41      [get_ports "FMCP_HSPC_DP14_C2M_N"] ;# Bank 125 - MGTYTXN2_125
# set_property PACKAGE_PIN W40      [get_ports "FMCP_HSPC_DP14_C2M_P"] ;# Bank 125 - MGTYTXP2_125
# set_property PACKAGE_PIN AA45     [get_ports "FMCP_HSPC_DP14_M2C_P"] ;# Bank 125 - MGTYRXP2_125
# set_property PACKAGE_PIN AA46     [get_ports "FMCP_HSPC_DP14_M2C_N"] ;# Bank 125 - MGTYRXN2_125
# set_property PACKAGE_PIN AA41     [get_ports "FMCP_HSPC_DP13_C2M_N"] ;# Bank 125 - MGTYTXN1_125
# set_property PACKAGE_PIN AA40     [get_ports "FMCP_HSPC_DP13_C2M_P"] ;# Bank 125 - MGTYTXP1_125
# set_property PACKAGE_PIN AB43     [get_ports "FMCP_HSPC_DP13_M2C_P"] ;# Bank 125 - MGTYRXP1_125
# set_property PACKAGE_PIN AB44     [get_ports "FMCP_HSPC_DP13_M2C_N"] ;# Bank 125 - MGTYRXN1_125
# set_property PACKAGE_PIN AB39     [get_ports "FMCP_HSPC_GBTCLK3_M2C_C_N"] ;# Bank 125 - MGTREFCLK0N_125
# set_property PACKAGE_PIN AB38     [get_ports "FMCP_HSPC_GBTCLK3_M2C_C_P"] ;# Bank 125 - MGTREFCLK0P_125
# set_property PACKAGE_PIN AC41     [get_ports "FMCP_HSPC_DP12_C2M_N"] ;# Bank 125 - MGTYTXN0_125
# set_property PACKAGE_PIN AC40     [get_ports "FMCP_HSPC_DP12_C2M_P"] ;# Bank 125 - MGTYTXP0_125
# set_property PACKAGE_PIN AC45     [get_ports "FMCP_HSPC_DP12_M2C_P"] ;# Bank 125 - MGTYRXP0_125
# set_property PACKAGE_PIN AC46     [get_ports "FMCP_HSPC_DP12_M2C_N"] ;# Bank 125 - MGTYRXN0_125
# set_property PACKAGE_PIN K43      [get_ports "FMCP_HSPC_DP7_C2M_N"] ;# Bank 126 - MGTYTXN3_126
# set_property PACKAGE_PIN K42      [get_ports "FMCP_HSPC_DP7_C2M_P"] ;# Bank 126 - MGTYTXP3_126
# set_property PACKAGE_PIN N45      [get_ports "FMCP_HSPC_DP7_M2C_P"] ;# Bank 126 - MGTYRXP3_126
# set_property PACKAGE_PIN N46      [get_ports "FMCP_HSPC_DP7_M2C_N"] ;# Bank 126 - MGTYRXN3_126
# set_property PACKAGE_PIN T39      [get_ports "FMCP_HSPC_GBT1_1_N"] ;# Bank 126 - MGTREFCLK1N_126
# set_property PACKAGE_PIN T38      [get_ports "FMCP_HSPC_GBT1_1_P"] ;# Bank 126 - MGTREFCLK1P_126
# set_property PACKAGE_PIN M43      [get_ports "FMCP_HSPC_DP6_C2M_N"] ;# Bank 126 - MGTYTXN2_126
# set_property PACKAGE_PIN M42      [get_ports "FMCP_HSPC_DP6_C2M_P"] ;# Bank 126 - MGTYTXP2_126
# set_property PACKAGE_PIN R45      [get_ports "FMCP_HSPC_DP6_M2C_P"] ;# Bank 126 - MGTYRXP2_126
# set_property PACKAGE_PIN R46      [get_ports "FMCP_HSPC_DP6_M2C_N"] ;# Bank 126 - MGTYRXN2_126
# #Other net   PACKAGE_PIN L40      - MGTAVTT_FPGA              Bank 126 - MGTAVTTRCAL_LN
# set_property PACKAGE_PIN L41      [get_ports "MGTRREF_126"] ;# Bank 126 - MGTRREF_LN
# set_property PACKAGE_PIN P43      [get_ports "FMCP_HSPC_DP5_C2M_N"] ;# Bank 126 - MGTYTXN1_126
# set_property PACKAGE_PIN P42      [get_ports "FMCP_HSPC_DP5_C2M_P"] ;# Bank 126 - MGTYTXP1_126
# set_property PACKAGE_PIN U45      [get_ports "FMCP_HSPC_DP5_M2C_P"] ;# Bank 126 - MGTYRXP1_126
# set_property PACKAGE_PIN U46      [get_ports "FMCP_HSPC_DP5_M2C_N"] ;# Bank 126 - MGTYRXN1_126
# set_property PACKAGE_PIN V39      [get_ports "FMCP_HSPC_GBT0_1_N"] ;# Bank 126 - MGTREFCLK0N_126
# set_property PACKAGE_PIN V38      [get_ports "FMCP_HSPC_GBT0_1_P"] ;# Bank 126 - MGTREFCLK0P_126
# set_property PACKAGE_PIN T43      [get_ports "FMCP_HSPC_DP4_C2M_N"] ;# Bank 126 - MGTYTXN0_126
# set_property PACKAGE_PIN T42      [get_ports "FMCP_HSPC_DP4_C2M_P"] ;# Bank 126 - MGTYTXP0_126
# set_property PACKAGE_PIN W45      [get_ports "FMCP_HSPC_DP4_M2C_P"] ;# Bank 126 - MGTYRXP0_126
# set_property PACKAGE_PIN W46      [get_ports "FMCP_HSPC_DP4_M2C_N"] ;# Bank 126 - MGTYRXN0_126
# set_property PACKAGE_PIN B43      [get_ports "FMCP_HSPC_DP19_C2M_N"] ;# Bank 127 - MGTYTXN3_127
# set_property PACKAGE_PIN B42      [get_ports "FMCP_HSPC_DP19_C2M_P"] ;# Bank 127 - MGTYTXP3_127
# set_property PACKAGE_PIN E45      [get_ports "FMCP_HSPC_DP19_M2C_P"] ;# Bank 127 - MGTYRXP3_127
# set_property PACKAGE_PIN E46      [get_ports "FMCP_HSPC_DP19_M2C_N"] ;# Bank 127 - MGTYRXN3_127
# set_property PACKAGE_PIN N41      [get_ports "FMCP_HSPC_GBT1_4_N"] ;# Bank 127 - MGTREFCLK1N_127
# set_property PACKAGE_PIN N40      [get_ports "FMCP_HSPC_GBT1_4_P"] ;# Bank 127 - MGTREFCLK1P_127
# set_property PACKAGE_PIN D43      [get_ports "FMCP_HSPC_DP18_C2M_N"] ;# Bank 127 - MGTYTXN2_127
# set_property PACKAGE_PIN D42      [get_ports "FMCP_HSPC_DP18_C2M_P"] ;# Bank 127 - MGTYTXP2_127
# set_property PACKAGE_PIN G45      [get_ports "FMCP_HSPC_DP18_M2C_P"] ;# Bank 127 - MGTYRXP2_127
# set_property PACKAGE_PIN G46      [get_ports "FMCP_HSPC_DP18_M2C_N"] ;# Bank 127 - MGTYRXN2_127
# set_property PACKAGE_PIN F43      [get_ports "FMCP_HSPC_DP17_C2M_N"] ;# Bank 127 - MGTYTXN1_127
# set_property PACKAGE_PIN F42      [get_ports "FMCP_HSPC_DP17_C2M_P"] ;# Bank 127 - MGTYTXP1_127
# set_property PACKAGE_PIN J45      [get_ports "FMCP_HSPC_DP17_M2C_P"] ;# Bank 127 - MGTYRXP1_127
# set_property PACKAGE_PIN J46      [get_ports "FMCP_HSPC_DP17_M2C_N"] ;# Bank 127 - MGTYRXN1_127
# set_property PACKAGE_PIN R41      [get_ports "FMCP_HSPC_GBTCLK4_M2C_C_N"] ;# Bank 127 - MGTREFCLK0N_127
# set_property PACKAGE_PIN R40      [get_ports "FMCP_HSPC_GBTCLK4_M2C_C_P"] ;# Bank 127 - MGTREFCLK0P_127
# set_property PACKAGE_PIN H43      [get_ports "FMCP_HSPC_DP16_C2M_N"] ;# Bank 127 - MGTYTXN0_127
# set_property PACKAGE_PIN H42      [get_ports "FMCP_HSPC_DP16_C2M_P"] ;# Bank 127 - MGTYTXP0_127
# set_property PACKAGE_PIN L45      [get_ports "FMCP_HSPC_DP16_M2C_P"] ;# Bank 127 - MGTYRXP0_127
# set_property PACKAGE_PIN L46      [get_ports "FMCP_HSPC_DP16_M2C_N"] ;# Bank 127 - MGTYRXN0_127
# set_property PACKAGE_PIN AW5      [get_ports "PCIE_TX12_P"] ;# Bank 224 - MGTYTXP3_224
# set_property PACKAGE_PIN AT2      [get_ports "PCIE_RX12_P"] ;# Bank 224 - MGTYRXP3_224
# set_property PACKAGE_PIN AT1      [get_ports "PCIE_RX12_N"] ;# Bank 224 - MGTYRXN3_224
# set_property PACKAGE_PIN AW4      [get_ports "PCIE_TX12_N"] ;# Bank 224 - MGTYTXN3_224
# set_property PACKAGE_PIN AN9      [get_ports "11N8666"] ;# Bank 224 - MGTREFCLK1P_224
# set_property PACKAGE_PIN AN8      [get_ports "11N8667"] ;# Bank 224 - MGTREFCLK1N_224
# set_property PACKAGE_PIN BA5      [get_ports "PCIE_TX13_P"] ;# Bank 224 - MGTYTXP2_224
# set_property PACKAGE_PIN AV2      [get_ports "PCIE_RX13_P"] ;# Bank 224 - MGTYRXP2_224
# set_property PACKAGE_PIN AV1      [get_ports "PCIE_RX13_N"] ;# Bank 224 - MGTYRXN2_224
# set_property PACKAGE_PIN BA4      [get_ports "PCIE_TX13_N"] ;# Bank 224 - MGTYTXN2_224
# set_property PACKAGE_PIN BC5      [get_ports "PCIE_TX14_P"] ;# Bank 224 - MGTYTXP1_224
# set_property PACKAGE_PIN AY2      [get_ports "PCIE_RX14_P"] ;# Bank 224 - MGTYRXP1_224
# set_property PACKAGE_PIN AY1      [get_ports "PCIE_RX14_N"] ;# Bank 224 - MGTYRXN1_224
# set_property PACKAGE_PIN BC4      [get_ports "PCIE_TX14_N"] ;# Bank 224 - MGTYTXN1_224
# set_property PACKAGE_PIN AR9      [get_ports "11N9044"] ;# Bank 224 - MGTREFCLK0P_224
# set_property PACKAGE_PIN AR8      [get_ports "11N9045"] ;# Bank 224 - MGTREFCLK0N_224
# set_property PACKAGE_PIN BE5      [get_ports "PCIE_TX15_P"] ;# Bank 224 - MGTYTXP0_224
# set_property PACKAGE_PIN BB2      [get_ports "PCIE_RX15_P"] ;# Bank 224 - MGTYRXP0_224
# set_property PACKAGE_PIN BB1      [get_ports "PCIE_RX15_N"] ;# Bank 224 - MGTYRXN0_224
# set_property PACKAGE_PIN BE4      [get_ports "PCIE_TX15_N"] ;# Bank 224 - MGTYTXN0_224
# set_property PACKAGE_PIN AP7      [get_ports "PCIE_TX8_P"] ;# Bank 225 - MGTYTXP3_225
# set_property PACKAGE_PIN AJ4      [get_ports "PCIE_RX8_P"] ;# Bank 225 - MGTYRXP3_225
# set_property PACKAGE_PIN AJ3      [get_ports "PCIE_RX8_N"] ;# Bank 225 - MGTYRXN3_225
# set_property PACKAGE_PIN AP6      [get_ports "PCIE_TX8_N"] ;# Bank 225 - MGTYTXN3_225
# set_property PACKAGE_PIN AJ9      [get_ports "MGT_SI570_CLOCK1_C_P"] ;# Bank 225 - MGTREFCLK1P_225
# set_property PACKAGE_PIN AJ8      [get_ports "MGT_SI570_CLOCK1_C_N"] ;# Bank 225 - MGTREFCLK1N_225
# set_property PACKAGE_PIN AR5      [get_ports "PCIE_TX9_P"] ;# Bank 225 - MGTYTXP2_225
# set_property PACKAGE_PIN AK2      [get_ports "PCIE_RX9_P"] ;# Bank 225 - MGTYRXP2_225
# set_property PACKAGE_PIN AK1      [get_ports "PCIE_RX9_N"] ;# Bank 225 - MGTYRXN2_225
# set_property PACKAGE_PIN AR4      [get_ports "PCIE_TX9_N"] ;# Bank 225 - MGTYTXN2_225
# set_property PACKAGE_PIN AT7      [get_ports "PCIE_TX10_P"] ;# Bank 225 - MGTYTXP1_225
# set_property PACKAGE_PIN AM2      [get_ports "PCIE_RX10_P"] ;# Bank 225 - MGTYRXP1_225
# set_property PACKAGE_PIN AM1      [get_ports "PCIE_RX10_N"] ;# Bank 225 - MGTYRXN1_225
# set_property PACKAGE_PIN AT6      [get_ports "PCIE_TX10_N"] ;# Bank 225 - MGTYTXN1_225
# set_property PACKAGE_PIN AL9      [get_ports "PCIE_CLK1_P"] ;# Bank 225 - MGTREFCLK0P_225
# set_property PACKAGE_PIN AL8      [get_ports "PCIE_CLK1_N"] ;# Bank 225 - MGTREFCLK0N_225
# set_property PACKAGE_PIN AU5      [get_ports "PCIE_TX11_P"] ;# Bank 225 - MGTYTXP0_225
# set_property PACKAGE_PIN AP2      [get_ports "PCIE_RX11_P"] ;# Bank 225 - MGTYRXP0_225
# set_property PACKAGE_PIN AP1      [get_ports "PCIE_RX11_N"] ;# Bank 225 - MGTYRXN0_225
# set_property PACKAGE_PIN AU4      [get_ports "PCIE_TX11_N"] ;# Bank 225 - MGTYTXN0_225
# set_property PACKAGE_PIN AH7      [get_ports "PCIE_TX4_P"] ;# Bank 226 - MGTYTXP3_226
# set_property PACKAGE_PIN AE4      [get_ports "PCIE_RX4_P"] ;# Bank 226 - MGTYRXP3_226
# set_property PACKAGE_PIN AE3      [get_ports "PCIE_RX4_N"] ;# Bank 226 - MGTYRXN3_226
# set_property PACKAGE_PIN AH6      [get_ports "PCIE_TX4_N"] ;# Bank 226 - MGTYTXN3_226
# set_property PACKAGE_PIN AE9      [get_ports "11N5839"] ;# Bank 226 - MGTREFCLK1P_226
# set_property PACKAGE_PIN AE8      [get_ports "11N5838"] ;# Bank 226 - MGTREFCLK1N_226
# set_property PACKAGE_PIN AK7      [get_ports "PCIE_TX5_P"] ;# Bank 226 - MGTYTXP2_226
# set_property PACKAGE_PIN AF2      [get_ports "PCIE_RX5_P"] ;# Bank 226 - MGTYRXP2_226
# set_property PACKAGE_PIN AF1      [get_ports "PCIE_RX5_N"] ;# Bank 226 - MGTYRXN2_226
# set_property PACKAGE_PIN AK6      [get_ports "PCIE_TX5_N"] ;# Bank 226 - MGTYTXN2_226
# set_property PACKAGE_PIN BD2      [get_ports "MGTRREF_226"] ;# Bank 226 - MGTRREF_RS
# #Other net   PACKAGE_PIN BD3      - MGTAVTT_FPGA              Bank 226 - MGTAVTTRCAL_RS
# set_property PACKAGE_PIN AM7      [get_ports "PCIE_TX6_P"] ;# Bank 226 - MGTYTXP1_226
# set_property PACKAGE_PIN AG4      [get_ports "PCIE_RX6_P"] ;# Bank 226 - MGTYRXP1_226
# set_property PACKAGE_PIN AG3      [get_ports "PCIE_RX6_N"] ;# Bank 226 - MGTYRXN1_226
# set_property PACKAGE_PIN AM6      [get_ports "PCIE_TX6_N"] ;# Bank 226 - MGTYTXN1_226
# set_property PACKAGE_PIN AG9      [get_ports "MGT226_CLK0_P"] ;# Bank 226 - MGTREFCLK0P_226
# set_property PACKAGE_PIN AG8      [get_ports "MGT226_CLK0_N"] ;# Bank 226 - MGTREFCLK0N_226
# set_property PACKAGE_PIN AN5      [get_ports "PCIE_TX7_P"] ;# Bank 226 - MGTYTXP0_226
# set_property PACKAGE_PIN AH2      [get_ports "PCIE_RX7_P"] ;# Bank 226 - MGTYRXP0_226
# set_property PACKAGE_PIN AH1      [get_ports "PCIE_RX7_N"] ;# Bank 226 - MGTYRXN0_226
# set_property PACKAGE_PIN AN4      [get_ports "PCIE_TX7_N"] ;# Bank 226 - MGTYTXN0_226
# set_property PACKAGE_PIN Y7       [get_ports "PCIE_TX0_P"] ;# Bank 227 - MGTYTXP3_227
# set_property PACKAGE_PIN AA4      [get_ports "PCIE_RX0_P"] ;# Bank 227 - MGTYRXP3_227
# set_property PACKAGE_PIN AA3      [get_ports "PCIE_RX0_N"] ;# Bank 227 - MGTYRXN3_227
# set_property PACKAGE_PIN Y6       [get_ports "PCIE_TX0_N"] ;# Bank 227 - MGTYTXN3_227
# set_property PACKAGE_PIN AA9      [get_ports "11N8774"] ;# Bank 227 - MGTREFCLK1P_227
# set_property PACKAGE_PIN AA8      [get_ports "11N8775"] ;# Bank 227 - MGTREFCLK1N_227
# set_property PACKAGE_PIN AB7      [get_ports "PCIE_TX1_P"] ;# Bank 227 - MGTYTXP2_227
# set_property PACKAGE_PIN AB2      [get_ports "PCIE_RX1_P"] ;# Bank 227 - MGTYRXP2_227
# set_property PACKAGE_PIN AB1      [get_ports "PCIE_RX1_N"] ;# Bank 227 - MGTYRXN2_227
# set_property PACKAGE_PIN AB6      [get_ports "PCIE_TX1_N"] ;# Bank 227 - MGTYTXN2_227
# set_property PACKAGE_PIN AD7      [get_ports "PCIE_TX2_P"] ;# Bank 227 - MGTYTXP1_227
# set_property PACKAGE_PIN AC4      [get_ports "PCIE_RX2_P"] ;# Bank 227 - MGTYRXP1_227
# set_property PACKAGE_PIN AC3      [get_ports "PCIE_RX2_N"] ;# Bank 227 - MGTYRXN1_227
# set_property PACKAGE_PIN AD6      [get_ports "PCIE_TX2_N"] ;# Bank 227 - MGTYTXN1_227
# set_property PACKAGE_PIN AC9      [get_ports "PCIE_CLK2_P"] ;# Bank 227 - MGTREFCLK0P_227
# set_property PACKAGE_PIN AC8      [get_ports "PCIE_CLK2_N"] ;# Bank 227 - MGTREFCLK0N_227
# set_property PACKAGE_PIN AF7      [get_ports "PCIE_TX3_P"] ;# Bank 227 - MGTYTXP0_227
# set_property PACKAGE_PIN AD2      [get_ports "PCIE_RX3_P"] ;# Bank 227 - MGTYRXP0_227
# set_property PACKAGE_PIN AD1      [get_ports "PCIE_RX3_N"] ;# Bank 227 - MGTYRXN0_227
# set_property PACKAGE_PIN AF6      [get_ports "PCIE_TX3_N"] ;# Bank 227 - MGTYTXN0_227
# set_property PACKAGE_PIN M7       [get_ports "QSFP1_TX4_P"] ;# Bank 231 - MGTYTXP3_231
# set_property PACKAGE_PIN U4       [get_ports "QSFP1_RX4_P"] ;# Bank 231 - MGTYRXP3_231
# set_property PACKAGE_PIN U3       [get_ports "QSFP1_RX4_N"] ;# Bank 231 - MGTYRXN3_231
# set_property PACKAGE_PIN M6       [get_ports "QSFP1_TX4_N"] ;# Bank 231 - MGTYTXN3_231
# set_property PACKAGE_PIN U9       [get_ports "SI5328_CLOCK1_C_P"] ;# Bank 231 - MGTREFCLK1P_231
# set_property PACKAGE_PIN U8       [get_ports "SI5328_CLOCK1_C_N"] ;# Bank 231 - MGTREFCLK1N_231
# set_property PACKAGE_PIN P7       [get_ports "QSFP1_TX3_P"] ;# Bank 231 - MGTYTXP2_231
# set_property PACKAGE_PIN V2       [get_ports "QSFP1_RX3_P"] ;# Bank 231 - MGTYRXP2_231
# set_property PACKAGE_PIN V1       [get_ports "QSFP1_RX3_N"] ;# Bank 231 - MGTYRXN2_231
# set_property PACKAGE_PIN P6       [get_ports "QSFP1_TX3_N"] ;# Bank 231 - MGTYTXN2_231
# set_property PACKAGE_PIN A4       [get_ports "MGTRREF_231"] ;# Bank 231 - MGTRREF_RN
# #Other net   PACKAGE_PIN A5       - MGTAVTT_FPGA              Bank 231 - MGTAVTTRCAL_RN
# set_property PACKAGE_PIN T7       [get_ports "QSFP1_TX2_P"] ;# Bank 231 - MGTYTXP1_231
# set_property PACKAGE_PIN W4       [get_ports "QSFP1_RX2_P"] ;# Bank 231 - MGTYRXP1_231
# set_property PACKAGE_PIN W3       [get_ports "QSFP1_RX2_N"] ;# Bank 231 - MGTYRXN1_231
# set_property PACKAGE_PIN T6       [get_ports "QSFP1_TX2_N"] ;# Bank 231 - MGTYTXN1_231
# set_property PACKAGE_PIN W9       [get_ports "QSFP_SI570_CLOCK_C_P"] ;# Bank 231 - MGTREFCLK0P_231
# set_property PACKAGE_PIN W8       [get_ports "QSFP_SI570_CLOCK_C_N"] ;# Bank 231 - MGTREFCLK0N_231
# set_property PACKAGE_PIN V7       [get_ports "QSFP1_TX1_P"] ;# Bank 231 - MGTYTXP0_231
# set_property PACKAGE_PIN Y2       [get_ports "QSFP1_RX1_P"] ;# Bank 231 - MGTYRXP0_231
# set_property PACKAGE_PIN Y1       [get_ports "QSFP1_RX1_N"] ;# Bank 231 - MGTYRXN0_231
# set_property PACKAGE_PIN V6       [get_ports "QSFP1_TX1_N"] ;# Bank 231 - MGTYTXN0_231
# set_property PACKAGE_PIN H7       [get_ports "QSFP2_TX4_P"] ;# Bank 232 - MGTYTXP3_232
# set_property PACKAGE_PIN M2       [get_ports "QSFP2_RX4_P"] ;# Bank 232 - MGTYRXP3_232
# set_property PACKAGE_PIN M1       [get_ports "QSFP2_RX4_N"] ;# Bank 232 - MGTYRXN3_232
# set_property PACKAGE_PIN H6       [get_ports "QSFP2_TX4_N"] ;# Bank 232 - MGTYTXN3_232
# set_property PACKAGE_PIN N9       [get_ports "SI5328_CLOCK2_C_P"] ;# Bank 232 - MGTREFCLK1P_232
# set_property PACKAGE_PIN N8       [get_ports "SI5328_CLOCK2_C_N"] ;# Bank 232 - MGTREFCLK1N_232
# set_property PACKAGE_PIN J5       [get_ports "QSFP2_TX3_P"] ;# Bank 232 - MGTYTXP2_232
# set_property PACKAGE_PIN P2       [get_ports "QSFP2_RX3_P"] ;# Bank 232 - MGTYRXP2_232
# set_property PACKAGE_PIN P1       [get_ports "QSFP2_RX3_N"] ;# Bank 232 - MGTYRXN2_232
# set_property PACKAGE_PIN J4       [get_ports "QSFP2_TX3_N"] ;# Bank 232 - MGTYTXN2_232
# set_property PACKAGE_PIN K7       [get_ports "QSFP2_TX2_P"] ;# Bank 232 - MGTYTXP1_232
# set_property PACKAGE_PIN R4       [get_ports "QSFP2_RX2_P"] ;# Bank 232 - MGTYRXP1_232
# set_property PACKAGE_PIN R3       [get_ports "QSFP2_RX2_N"] ;# Bank 232 - MGTYRXN1_232
# set_property PACKAGE_PIN K6       [get_ports "QSFP2_TX2_N"] ;# Bank 232 - MGTYTXN1_232
# set_property PACKAGE_PIN R9       [get_ports "MGT_SI570_CLOCK2_C_P"] ;# Bank 232 - MGTREFCLK0P_232
# set_property PACKAGE_PIN R8       [get_ports "MGT_SI570_CLOCK2_C_N"] ;# Bank 232 - MGTREFCLK0N_232
# set_property PACKAGE_PIN L5       [get_ports "QSFP2_TX1_P"] ;# Bank 232 - MGTYTXP0_232
# set_property PACKAGE_PIN T2       [get_ports "QSFP2_RX1_P"] ;# Bank 232 - MGTYRXP0_232
# set_property PACKAGE_PIN T1       [get_ports "QSFP2_RX1_N"] ;# Bank 232 - MGTYRXN0_232
# set_property PACKAGE_PIN L4       [get_ports "QSFP2_TX1_N"] ;# Bank 232 - MGTYTXN0_232
# set_property PACKAGE_PIN C5       [get_ports "FIREFLY_TX4_P"] ;# Bank 233 - MGTYTXP3_233
# set_property PACKAGE_PIN D2       [get_ports "FIREFLY_RX4_P"] ;# Bank 233 - MGTYRXP3_233
# set_property PACKAGE_PIN D1       [get_ports "FIREFLY_RX4_N"] ;# Bank 233 - MGTYRXN3_233
# set_property PACKAGE_PIN C4       [get_ports "FIREFLY_TX4_N"] ;# Bank 233 - MGTYTXN3_233
# set_property PACKAGE_PIN J9       [get_ports "MGT233_CLK1_P"] ;# Bank 233 - MGTREFCLK1P_233
# set_property PACKAGE_PIN J8       [get_ports "MGT233_CLK1_N"] ;# Bank 233 - MGTREFCLK1N_233
# set_property PACKAGE_PIN E5       [get_ports "FIREFLY_TX3_P"] ;# Bank 233 - MGTYTXP2_233
# set_property PACKAGE_PIN F2       [get_ports "FIREFLY_RX3_P"] ;# Bank 233 - MGTYRXP2_233
# set_property PACKAGE_PIN F1       [get_ports "FIREFLY_RX3_N"] ;# Bank 233 - MGTYRXN2_233
# set_property PACKAGE_PIN E4       [get_ports "FIREFLY_TX3_N"] ;# Bank 233 - MGTYTXN2_233
# set_property PACKAGE_PIN F7       [get_ports "FIREFLY_TX2_P"] ;# Bank 233 - MGTYTXP1_233
# set_property PACKAGE_PIN H2       [get_ports "FIREFLY_RX2_P"] ;# Bank 233 - MGTYRXP1_233
# set_property PACKAGE_PIN H1       [get_ports "FIREFLY_RX2_N"] ;# Bank 233 - MGTYRXN1_233
# set_property PACKAGE_PIN F6       [get_ports "FIREFLY_TX2_N"] ;# Bank 233 - MGTYTXN1_233
# set_property PACKAGE_PIN L9       [get_ports "MGT_SI570_CLOCK3_C_P"] ;# Bank 233 - MGTREFCLK0P_233
# set_property PACKAGE_PIN L8       [get_ports "MGT_SI570_CLOCK3_C_N"] ;# Bank 233 - MGTREFCLK0N_233
# set_property PACKAGE_PIN G5       [get_ports "FIREFLY_TX1_P"] ;# Bank 233 - MGTYTXP0_233
# set_property PACKAGE_PIN K2       [get_ports "FIREFLY_RX1_P"] ;# Bank 233 - MGTYRXP0_233
# set_property PACKAGE_PIN K1       [get_ports "FIREFLY_RX1_N"] ;# Bank 233 - MGTYRXN0_233
# set_property PACKAGE_PIN G4       [get_ports "FIREFLY_TX1_N"] ;# Bank 233 - MGTYTXN0_233
