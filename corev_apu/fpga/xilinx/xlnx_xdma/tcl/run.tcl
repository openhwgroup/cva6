set partNumber $::env(XILINX_PART)
set boardName  $::env(XILINX_BOARD)

set ipName xlnx_xdma

create_project $ipName . -force -part $partNumber
set_property board_part $boardName [current_project]

create_ip -name xdma -vendor xilinx.com -library ip -module_name $ipName

# Alveo U200 — XDMA PCIe Gen3 x16 AXI-MM Bridge (no DMA engine).
# AXI master: 512-bit data, 64-bit addr, 4-bit ID. PCIe refclk: 100 MHz (AM10/AM11).
# BAR0 = 256 MB; pciebar2axibar_0 = 0x80000000 → host writes to BAR0 + offset
# land at AXI address 0x80000000 + offset (DRAM base on the SoC).
set_property -dict [list \
    CONFIG.PCIE_BOARD_INTERFACE      {pci_express_x16} \
    CONFIG.SYS_RST_N_BOARD_INTERFACE {pcie_perstn} \
    CONFIG.functional_mode           {AXI_Bridge} \
    CONFIG.mode_selection            {Advanced} \
    CONFIG.device_port_type          {PCI_Express_Endpoint_device} \
    CONFIG.pl_link_cap_max_link_width {X16} \
    CONFIG.pl_link_cap_max_link_speed {8.0_GT/s} \
    CONFIG.axi_data_width            {512_bit} \
    CONFIG.axi_addr_width            {64} \
    CONFIG.axi_id_width              {4} \
    CONFIG.axilite_master_en         {false} \
    CONFIG.axist_bypass_en           {false} \
    CONFIG.ref_clk_freq              {100_MHz} \
    CONFIG.pf0_device_id             {903F} \
    CONFIG.pf0_subsystem_vendor_id   {10EE} \
    CONFIG.en_gt_selection           {true} \
    CONFIG.pf0_bar0_size             {256}     \
    CONFIG.pf0_bar0_scale            {Megabytes} \
    CONFIG.pf0_bar0_64bit            {true}    \
    CONFIG.pf0_bar0_prefetchable     {true}    \
    CONFIG.pciebar2axibar_0          {0x0000000080000000} \
] [get_ips $ipName]

generate_target {instantiation_template} [get_files ./$ipName.srcs/sources_1/ip/$ipName/$ipName.xci]
generate_target all [get_files  ./$ipName.srcs/sources_1/ip/$ipName/$ipName.xci]
create_ip_run [get_files -of_objects [get_fileset sources_1] ./$ipName.srcs/sources_1/ip/$ipName/$ipName.xci]
launch_run -jobs 8 ${ipName}_synth_1
wait_on_run ${ipName}_synth_1
