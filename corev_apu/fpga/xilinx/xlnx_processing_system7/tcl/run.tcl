set partNumber $::env(XILINX_PART)
set boardName  $::env(XILINX_BOARD)

set ipName xlnx_processing_system7

create_project $ipName . -force -part $partNumber
set_property board_part $boardName [current_project]

create_ip -name processing_system7 -vendor xilinx.com -library ip -module_name $ipName

set_property -dict [list CONFIG.PCW_ACT_APU_PERIPHERAL_FREQMHZ {666.666687} \
                        CONFIG.PCW_ACT_CAN_PERIPHERAL_FREQMHZ {10.000000} \
                        CONFIG.PCW_ACT_DCI_PERIPHERAL_FREQMHZ {10.158730} \
                        CONFIG.PCW_ACT_ENET0_PERIPHERAL_FREQMHZ {10.000000} \
                        CONFIG.PCW_ACT_ENET1_PERIPHERAL_FREQMHZ {10.000000} \
                        CONFIG.PCW_ACT_FPGA0_PERIPHERAL_FREQMHZ {10.000000} \
                        CONFIG.PCW_ACT_FPGA1_PERIPHERAL_FREQMHZ {10.000000} \
                        CONFIG.PCW_ACT_FPGA2_PERIPHERAL_FREQMHZ {10.000000} \
                        CONFIG.PCW_ACT_FPGA3_PERIPHERAL_FREQMHZ {10.000000} \
                        CONFIG.PCW_ACT_PCAP_PERIPHERAL_FREQMHZ {200.000000} \
                        CONFIG.PCW_ACT_QSPI_PERIPHERAL_FREQMHZ {10.000000} \
                        CONFIG.PCW_ACT_SDIO_PERIPHERAL_FREQMHZ {10.000000} \
                        CONFIG.PCW_ACT_SMC_PERIPHERAL_FREQMHZ {10.000000} \
                        CONFIG.PCW_ACT_SPI_PERIPHERAL_FREQMHZ {10.000000} \
                        CONFIG.PCW_ACT_TPIU_PERIPHERAL_FREQMHZ {200.000000} \
                        CONFIG.PCW_ACT_TTC0_CLK0_PERIPHERAL_FREQMHZ {111.111115} \
                        CONFIG.PCW_ACT_TTC0_CLK1_PERIPHERAL_FREQMHZ {111.111115} \
                        CONFIG.PCW_ACT_TTC0_CLK2_PERIPHERAL_FREQMHZ {111.111115} \
                        CONFIG.PCW_ACT_TTC1_CLK0_PERIPHERAL_FREQMHZ {111.111115} \
                        CONFIG.PCW_ACT_TTC1_CLK1_PERIPHERAL_FREQMHZ {111.111115} \
                        CONFIG.PCW_ACT_TTC1_CLK2_PERIPHERAL_FREQMHZ {111.111115} \
                        CONFIG.PCW_ACT_UART_PERIPHERAL_FREQMHZ {10.000000} \
                        CONFIG.PCW_ACT_WDT_PERIPHERAL_FREQMHZ {111.111115} \
                        CONFIG.PCW_ARMPLL_CTRL_FBDIV {40} \
                        CONFIG.PCW_CAN_PERIPHERAL_DIVISOR0 {1} \
                        CONFIG.PCW_CAN_PERIPHERAL_DIVISOR1 {1} \
                        CONFIG.PCW_CLK0_FREQ {10000000} \
                        CONFIG.PCW_CLK1_FREQ {10000000} \
                        CONFIG.PCW_CLK2_FREQ {10000000} \
                        CONFIG.PCW_CLK3_FREQ {10000000} \
                        CONFIG.PCW_CPU_CPU_PLL_FREQMHZ {1333.333} \
                        CONFIG.PCW_CPU_PERIPHERAL_DIVISOR0 {2} \
                        CONFIG.PCW_DCI_PERIPHERAL_DIVISOR0 {15} \
                        CONFIG.PCW_DCI_PERIPHERAL_DIVISOR1 {7} \
                        CONFIG.PCW_DDRPLL_CTRL_FBDIV {32} \
                        CONFIG.PCW_DDR_DDR_PLL_FREQMHZ {1066.667} \
                        CONFIG.PCW_DDR_PERIPHERAL_DIVISOR0 {2} \
                        CONFIG.PCW_DDR_RAM_HIGHADDR {0x3FFFFFFF} \
                        CONFIG.PCW_ENET0_PERIPHERAL_DIVISOR0 {1} \
                        CONFIG.PCW_ENET0_PERIPHERAL_DIVISOR1 {1} \
                        CONFIG.PCW_ENET1_PERIPHERAL_DIVISOR0 {1} \
                        CONFIG.PCW_ENET1_PERIPHERAL_DIVISOR1 {1} \
                        CONFIG.PCW_EN_CLK0_PORT {0} \
                        CONFIG.PCW_EN_RST0_PORT {0} \
                        CONFIG.PCW_FCLK0_PERIPHERAL_DIVISOR0 {1} \
                        CONFIG.PCW_FCLK0_PERIPHERAL_DIVISOR1 {1} \
                        CONFIG.PCW_FCLK1_PERIPHERAL_DIVISOR0 {1} \
                        CONFIG.PCW_FCLK1_PERIPHERAL_DIVISOR1 {1} \
                        CONFIG.PCW_FCLK2_PERIPHERAL_DIVISOR0 {1} \
                        CONFIG.PCW_FCLK2_PERIPHERAL_DIVISOR1 {1} \
                        CONFIG.PCW_FCLK3_PERIPHERAL_DIVISOR0 {1} \
                        CONFIG.PCW_FCLK3_PERIPHERAL_DIVISOR1 {1} \
                        CONFIG.PCW_FCLK_CLK0_BUF {FALSE} \
                        CONFIG.PCW_FPGA_FCLK0_ENABLE {0} \
                        CONFIG.PCW_FPGA_FCLK1_ENABLE {0} \
                        CONFIG.PCW_FPGA_FCLK2_ENABLE {0} \
                        CONFIG.PCW_FPGA_FCLK3_ENABLE {0} \
                        CONFIG.PCW_I2C_PERIPHERAL_FREQMHZ {25} \
                        CONFIG.PCW_IOPLL_CTRL_FBDIV {48} \
                        CONFIG.PCW_IO_IO_PLL_FREQMHZ {1600.000} \
                        CONFIG.PCW_PCAP_PERIPHERAL_DIVISOR0 {8} \
                        CONFIG.PCW_QSPI_PERIPHERAL_DIVISOR0 {1} \
                        CONFIG.PCW_SDIO_PERIPHERAL_DIVISOR0 {1} \
                        CONFIG.PCW_SMC_PERIPHERAL_DIVISOR0 {1} \
                        CONFIG.PCW_SPI_PERIPHERAL_DIVISOR0 {1} \
                        CONFIG.PCW_TPIU_PERIPHERAL_DIVISOR0 {1} \
                        CONFIG.PCW_UART_PERIPHERAL_DIVISOR0 {1} \
                        CONFIG.PCW_UIPARAM_ACT_DDR_FREQ_MHZ {533.333374} \
                        CONFIG.PCW_UIPARAM_DDR_BANK_ADDR_COUNT {3} \
                        CONFIG.PCW_UIPARAM_DDR_BL {8} \
                        CONFIG.PCW_UIPARAM_DDR_BOARD_DELAY0 {0.221} \
                        CONFIG.PCW_UIPARAM_DDR_BOARD_DELAY1 {0.222} \
                        CONFIG.PCW_UIPARAM_DDR_BOARD_DELAY2 {0.217} \
                        CONFIG.PCW_UIPARAM_DDR_BOARD_DELAY3 {0.244} \
                        CONFIG.PCW_UIPARAM_DDR_CL {7} \
                        CONFIG.PCW_UIPARAM_DDR_COL_ADDR_COUNT {10} \
                        CONFIG.PCW_UIPARAM_DDR_CWL {6} \
                        CONFIG.PCW_UIPARAM_DDR_DEVICE_CAPACITY {4096 MBits} \
                        CONFIG.PCW_UIPARAM_DDR_DQS_TO_CLK_DELAY_0 {-0.05} \
                        CONFIG.PCW_UIPARAM_DDR_DQS_TO_CLK_DELAY_1 {-0.044} \
                        CONFIG.PCW_UIPARAM_DDR_DQS_TO_CLK_DELAY_2 {-0.035} \
                        CONFIG.PCW_UIPARAM_DDR_DQS_TO_CLK_DELAY_3 {-0.100} \
                        CONFIG.PCW_UIPARAM_DDR_DRAM_WIDTH {16 Bits} \
                        CONFIG.PCW_UIPARAM_DDR_MEMORY_TYPE {DDR 3 (Low Voltage)} \
                        CONFIG.PCW_UIPARAM_DDR_PARTNO {MT41K256M16 RE-125} \
                        CONFIG.PCW_UIPARAM_DDR_ROW_ADDR_COUNT {15} \
                        CONFIG.PCW_UIPARAM_DDR_SPEED_BIN {DDR3_1066F} \
                        CONFIG.PCW_UIPARAM_DDR_T_FAW {40.0} \
                        CONFIG.PCW_UIPARAM_DDR_T_RAS_MIN {35.0} \
                        CONFIG.PCW_UIPARAM_DDR_T_RC {48.75} \
                        CONFIG.PCW_UIPARAM_DDR_T_RCD {7} \
                        CONFIG.PCW_UIPARAM_DDR_T_RP {7} \
                        CONFIG.PCW_USE_M_AXI_GP0 {0} \
                        CONFIG.PCW_USE_S_AXI_HP0 {1} \
                       ] [get_ips $ipName]


generate_target {instantiation_template} [get_files ./$ipName.srcs/sources_1/ip/$ipName/$ipName.xci]
generate_target all [get_files  ./$ipName.srcs/sources_1/ip/$ipName/$ipName.xci]
create_ip_run [get_files -of_objects [get_fileset sources_1] ./$ipName.srcs/sources_1/ip/$ipName/$ipName.xci]
launch_run -jobs 8 ${ipName}_synth_1
wait_on_run ${ipName}_synth_1
