############################################################################
### Alveo U200 (xcu200-fsgd2104-2-e) XDC for CVA6
### Derived from VCU118 CVA6 XDC with U200-specific pin locations.
###
### NOTE: DDR4 and PCIe lane pin constraints are NOT included here.
### They are generated automatically by the MIG (xlnx_ddr4) and XDMA
### (xlnx_xdma) Vivado IPs respectively via board-file automation.
### Only non-IP-managed user I/O and reference clocks appear below.
############################################################################

# Buttons / Reset
# U200 CPU_RESET_FPGA is directly from the satellite controller (active-low).
set_property -dict {PACKAGE_PIN AL20 IOSTANDARD LVCMOS12} [get_ports cpu_resetn] ;# Bank 64 VCCO - VCC1V2 - CPU_RESET_FPGA

# 300 MHz System Reference Clock (SYSCLK1_300, Bank 64)
# Independent board oscillator output for the CPU system PLL.
# SYSCLK1_300 is in Bank 64 (LVDS, near all user I/O), leaving SYSCLK0_300
# (Bank 42) free for the DDR4 MIG.  Decoupling the system PLL from the MIG
# eliminates cascaded-MMCM jitter and cross-domain over-constraining.
set_property -dict {PACKAGE_PIN AW20 IOSTANDARD LVDS} [get_ports ref_clk_p]
set_property -dict {PACKAGE_PIN AW19 IOSTANDARD LVDS} [get_ports ref_clk_n]
create_clock -name ref_clk -period 3.333 [get_ports ref_clk_p]

# PCIe
set_property -dict {PACKAGE_PIN BD21 IOSTANDARD LVCMOS12} [get_ports sys_rst_n];
set_property PACKAGE_PIN AM11 [get_ports sys_clk_p]
set_property PACKAGE_PIN AM10 [get_ports sys_clk_n]
create_clock -name sys_clk -period 10 [get_ports sys_clk_p]

# UART (FTDI FT4232 Port 3, exposed via microUSB on Alveo U200)
# Bank 64 VCCO = 1.2V (LVCMOS12), unlike VCU118's 1.8V (LVCMOS18).
set_property -dict {PACKAGE_PIN BF18 IOSTANDARD LVCMOS12} [get_ports rx]
set_property -dict {PACKAGE_PIN BB20 IOSTANDARD LVCMOS12} [get_ports tx]

# SD Card / SPI — not present on Alveo U200.
# InclSPI is already 0 in the U200 ifdef, but the ports are still on the
# top-level module (common section). Assign them to unused Bank 64 pins
# so Vivado can place them without error.  They will be inactive.
set_property -dict {PACKAGE_PIN AM19 IOSTANDARD LVCMOS12} [get_ports spi_clk_o] ;# SW_DP1 (unused)
set_property -dict {PACKAGE_PIN AL19 IOSTANDARD LVCMOS12} [get_ports spi_ss]    ;# SW_DP2 (unused)
set_property -dict {PACKAGE_PIN AP20 IOSTANDARD LVCMOS12} [get_ports spi_miso]  ;# SW_DP3 (unused)
set_property -dict {PACKAGE_PIN AL21 IOSTANDARD LVCMOS12} [get_ports spi_mosi]  ;# SW_SET1_FPGA (unused)

# JTAG and DPTI: the consumers (dmi_jtag, dpti_ctrl, slicer_DPTI) are gated
# out under `ifdef U200`, so the input/inout ports (tck, tms, tdi, prog_clko,
# prog_rxen, prog_txen, prog_spien, prog_d) are unread and Vivado trims them
# automatically — no PACKAGE_PIN needed for those.
#
# The 5 output ports (tdo, prog_oen, prog_rdn, prog_wrn, prog_siwun) cannot
# be optimized away — Vivado preserves any port declared on the top-level
# interface — so we tie them to constants under `ifdef U200` in
# ariane_xilinx.sv and park them on harmless Bank 64 GPIO_MSP / SW_DP test
# pins below (verified against the U200 board file / reference XDC).
set_property -dict {PACKAGE_PIN AR20 IOSTANDARD LVCMOS12} [get_ports tdo]        ;# GPIO_MSP[0]
set_property -dict {PACKAGE_PIN AM20 IOSTANDARD LVCMOS12} [get_ports prog_oen]   ;# GPIO_MSP[1]
set_property -dict {PACKAGE_PIN AM21 IOSTANDARD LVCMOS12} [get_ports prog_rdn]   ;# GPIO_MSP[2]
set_property -dict {PACKAGE_PIN AN21 IOSTANDARD LVCMOS12} [get_ports prog_wrn]   ;# GPIO_MSP[3]
set_property -dict {PACKAGE_PIN AN22 IOSTANDARD LVCMOS12} [get_ports prog_siwun] ;# SW_DP[0]

# U200 has a quad SPI flash
set_property CONFIG_VOLTAGE 1.8                        [current_design]
set_property CONFIG_MODE {SPIx4}                       [current_design]
set_property BITSTREAM.CONFIG.CONFIGFALLBACK Enable    [current_design]; # Golden image is the fall back image if  new …
set_property BITSTREAM.CONFIG.EXTMASTERCCLK_EN disable [current_design]
set_property BITSTREAM.CONFIG.CONFIGRATE 63.8          [current_design]
set_property BITSTREAM.CONFIG.SPI_BUSWIDTH 4           [current_design]
set_property BITSTREAM.GENERAL.COMPRESS TRUE           [current_design]
set_property BITSTREAM.CONFIG.SPI_FALL_EDGE YES        [current_design]
set_property BITSTREAM.CONFIG.SPI_32BIT_ADDR Yes       [current_design]
set_property BITSTREAM.CONFIG.UNUSEDPIN Pullup         [current_design]


#############################################
# Asynchronous Clock Domain Crossings
#############################################
# Three independent clock trees exist in this design:
#   1. ref_clk       (SYSCLK1_300 → xlnx_clk_gen MMCM → CPU 50 MHz, etc.)
#   2. c0_sys_clk_p  (SYSCLK1_300 → DDR4 MIG → mmcm_clkout0 UI clock)
#   3. sys_clk       (PCIe ref 100 MHz → XDMA → pcie_axi_clk, etc.)

 set_clock_groups -asynchronous \
  -group [get_clocks -include_generated_clocks ref_clk] \
  -group [get_clocks -include_generated_clocks {c0_sys_clk_p mmcm_clkout0}] \
  -group [get_clocks -include_generated_clocks sys_clk]