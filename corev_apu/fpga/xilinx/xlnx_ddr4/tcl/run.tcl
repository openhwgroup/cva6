set partNumber $::env(XILINX_PART)
set boardName  $::env(XILINX_BOARD)

set ipName xlnx_ddr4

create_project $ipName . -force -part $partNumber
set_property board_part $boardName [current_project]

create_ip -name ddr4 -vendor xilinx.com -library ip -module_name $ipName

upgrade_ip [get_ips $ipName]

# Alveo U200 has 4× MTA18ASF2G72PZ-2G3 RDIMMs (16 GB / channel, 34-bit AXI addr).
# AxiSelection=true exposes a 512-bit AXI4 slave; we drive it from a 64→512
# converter. The IP's input clock is SYSCLK0_300 (default_300mhz_clk0, Bank 42),
# which keeps the system PLL on SYSCLK1_300 (Bank 64).
set_property -dict [list \
  CONFIG.ADDN_UI_CLKOUT1_FREQ_HZ {100} \
  CONFIG.C0.DDR4_AUTO_AP_COL_A3 {true} \
  CONFIG.C0.DDR4_AxiAddressWidth {34} \
  CONFIG.C0.DDR4_AxiDataWidth {512} \
  CONFIG.C0.DDR4_AxiSelection {true} \
  CONFIG.C0.DDR4_CasLatency {17} \
  CONFIG.C0.DDR4_DataMask {NONE} \
  CONFIG.C0.DDR4_Ecc {false} \
  CONFIG.C0.DDR4_InputClockPeriod {3332} \
  CONFIG.C0.DDR4_Mem_Add_Map {ROW_COLUMN_BANK_INTLV} \
  CONFIG.C0.DDR4_MemoryPart {MTA18ASF2G72PZ-2G3} \
  CONFIG.C0.DDR4_MemoryType {RDIMMs} \
  CONFIG.C0.DDR4_TimePeriod {833} \
  CONFIG.C0_CLOCK_BOARD_INTERFACE {default_300mhz_clk0} \
  CONFIG.C0_DDR4_BOARD_INTERFACE {ddr4_sdram_c0} \
] [get_ips xlnx_ddr4]

generate_target {instantiation_template} [get_files ./$ipName.srcs/sources_1/ip/$ipName/$ipName.xci]
generate_target all [get_files  ./$ipName.srcs/sources_1/ip/$ipName/$ipName.xci]
create_ip_run [get_files -of_objects [get_fileset sources_1] ./$ipName.srcs/sources_1/ip/$ipName/$ipName.xci]
launch_run -jobs 8 ${ipName}_synth_1
wait_on_run ${ipName}_synth_1
