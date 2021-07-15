#Create constraint for the clock input of the zcu102 board
create_clock -period 8.000 -name ref_clk [get_ports ref_clk_p]
set_property CLOCK_DEDICATED_ROUTE ANY_CMT_COLUMN [get_nets ref_clk]

#alsaqr clock
create_clock -period 100.000 -name alsaqr_clk [get_pins i_clk_manager/clk_out1]

## JTAG
create_clock -period 100.000 -name tck -waveform {0.000 50.000} [get_ports pad_jtag_tck]
set_input_jitter tck 1.000
set_property CLOCK_DEDICATED_ROUTE FALSE [get_nets pad_jtag_tck_IBUF_inst/O]


# minimize routing delay
set_input_delay -clock tck -clock_fall 5.000 [get_ports pad_jtag_tdi]
set_input_delay -clock tck -clock_fall 5.000 [get_ports pad_jtag_tms]
set_output_delay -clock tck 5.000 [get_ports pad_jtag_tdo]

set_max_delay -to   [get_ports pad_jtag_tdo] 20.000
set_max_delay -from [get_ports pad_jtag_tms] 20.000
set_max_delay -from [get_ports pad_jtag_tdi] 20.000

set_max_delay -datapath_only -from [get_pins i_alsaqr/i_host_domain/i_cva_subsystem/i_dmi_jtag/i_dmi_cdc/i_cdc_resp/i_src/data_src_q_reg*/C] -to [get_pins i_alsaqr/i_host_domain/i_cva_subsystem/i_dmi_jtag/i_dmi_cdc/i_cdc_resp/i_dst/data_dst_q_reg*/D] 20.000
set_max_delay -datapath_only -from [get_pins i_alsaqr/i_host_domain/i_cva_subsystem/i_dmi_jtag/i_dmi_cdc/i_cdc_resp/i_src/req_src_q_reg/C]   -to [get_pins i_alsaqr/i_host_domain/i_cva_subsystem/i_dmi_jtag/i_dmi_cdc/i_cdc_resp/i_dst/req_dst_q_reg/D] 20.000
set_max_delay -datapath_only -from [get_pins i_alsaqr/i_host_domain/i_cva_subsystem/i_dmi_jtag/i_dmi_cdc/i_cdc_req/i_dst/ack_dst_q_reg/C]    -to [get_pins i_alsaqr/i_host_domain/i_cva_subsystem/i_dmi_jtag/i_dmi_cdc/i_cdc_req/i_src/ack_src_q_reg/D] 20.000


# reset signal
set_false_path -from [get_ports rst_ni]

# Set ASYNC_REG attribute for ff synchronizers to place them closer together and
# increase MTBF
#set_property ASYNC_REG true [get_cells i_pulp/soc_domain_i/pulp_soc_i/soc_peripherals_i/apb_adv_timer_i/u_tim0/u_in_stage/r_ls_clk_sync_reg*]
#set_property ASYNC_REG true [get_cells i_pulp/soc_domain_i/pulp_soc_i/soc_peripherals_i/apb_adv_timer_i/u_tim1/u_in_stage/r_ls_clk_sync_reg*]
#set_property ASYNC_REG true [get_cells i_pulp/soc_domain_i/pulp_soc_i/soc_peripherals_i/apb_adv_timer_i/u_tim2/u_in_stage/r_ls_clk_sync_reg*]
#set_property ASYNC_REG true [get_cells i_pulp/soc_domain_i/pulp_soc_i/soc_peripherals_i/apb_adv_timer_i/u_tim3/u_in_stage/r_ls_clk_sync_reg*]
#set_property ASYNC_REG true [get_cells i_pulp/soc_domain_i/pulp_soc_i/soc_peripherals_i/i_apb_timer_unit/s_ref_clk*]
#set_property ASYNC_REG true [get_cells i_pulp/soc_domain_i/pulp_soc_i/soc_peripherals_i/i_ref_clk_sync/i_pulp_sync/r_reg_reg*]
#set_property ASYNC_REG true [get_cells i_pulp/soc_domain_i/pulp_soc_i/soc_peripherals_i/u_evnt_gen/r_ls_sync_reg*]

# Create clocks (10 MHz)
#create_clock -period 100.000 -name pulp_soc_clk [get_pins i_pulp/soc_domain_i/pulp_soc_i/i_clk_rst_gen/i_fpga_clk_gen/soc_clk_o]
#create_clock -period 100.000 -name pulp_cluster_clk [get_pins i_pulp/soc_domain_i/pulp_soc_i/i_clk_rst_gen/i_fpga_clk_gen/cluster_clk_o] 
#create_clock -period 100.000 -name pulp_periph_clk [get_pins i_pulp/soc_domain_i/pulp_soc_i/i_clk_rst_gen/i_fpga_clk_gen/per_clk_o]

# Create asynchronous clock group between slow-clk and SoC clock. Those clocks
# are considered asynchronously and proper synchronization regs are in place
#set_clock_groups -asynchronous -group [get_clocks -of_objects [get_pins i_pulp/safe_domain_i/i_slow_clk_gen/slow_clk_o]] -group [get_clocks -of_objects [get_pins i_pulp/soc_domain_i/pulp_soc_i/i_clk_rst_gen/i_fpga_clk_gen/soc_clk_o]] -group [get_clocks -of_objects [get_pins i_pulp/soc_domain_i/pulp_soc_i/i_clk_rst_gen/i_fpga_clk_gen/cluster_clk_o]]


#Hyper bus
set tck_phy 100.000
set tck_sys 100.00
set jitter_phy 5.000
set jitter_sys 5.000

# Create RWDS clock
create_clock -period 100.000 -name rwds_clk [get_ports FMC_hyper_rwds0]

# Create the PHY clock
create_clock -name clk_phy -period ${tck_phy} [get_pins i_alsaqr/i_host_domain/axi_hyperbus/clk_phy_i]
set_clock_uncertainty [expr {${jitter_phy}*${tck_phy}}] clk_phy

# Create the system clock
create_clock -name clk_sys -period ${tck_sys} [get_ports i_alsaqr/i_host_domain/axi_hyperbus/clk_sys_i]
set_clock_uncertainty [expr {${jitter_sys}*${tck_sys}}] clk_sys

# Create generated clock for for outgoing RWDS after delay
set clk_tx_shift [expr 0.25*${tck_phy}]
create_generated_clock  -name clk_tx -edges {1 2 3} -edge_shift "$clk_tx_shift $clk_tx_shift $clk_tx_shift" \
    -source i_alsaqr/i_host_domain/axi_hyperbus/i_phy/i_trx/i_delay_tx_clk_90/i_delay/clk_i \
    i_alsaqr/i_host_domain/axi_hyperbus/i_phy/i_trx/i_delay_tx_clk_90/i_delay/clk_o

# Create generated clock for incoming RWDS after delay
set clk_rx_shift [expr 0.25*${tck_phy}]
create_generated_clock  -name clk_rx -edges {1 2 3} -edge_shift "$clk_rx_shift $clk_rx_shift $clk_rx_shift" \
    -source i_alsaqr/i_host_domain/axi_hyperbus/i_phy/i_trx/i_delay_rx_rwds_90/i_delay/clk_i \
    i_alsaqr/i_host_domain/axi_hyperbus/i_phy/i_trx/i_delay_rx_rwds_90/i_delay/clk_o

# Inform tool that system and PHY-derived clocks are asynchronous, but may have timed arcs between them
set_clock_groups -asynchronous -allow_paths -group {clk_sys} -group {clk_phy clk_tx clk_rwds_in clk_rx}

# Constrain i_cdc_fifo_gray CDC FIFOs (clocks already async above)
set async_pins [get_pins -hierarchical -filter async]
set_ungroup [get_designs cdc_fifo_gray*] false
set_boundary_optimization [get_designs cdc_fifo_gray*] false
set_max_delay [expr min(${tck_sys}, ${tck_phy})] -through ${async_pins} -through ${async_pins}
set_false_path -hold -through ${async_pins} -through ${async_pins}

# Constrain config register false paths to PHY
set cfg_from  [get_pins i_alsaqr/i_host_domain/axi_hyperbus/i_cfg_regs/cfg_o*]
set cfg_to    [get_pins i_alsaqr/i_host_domain/axi_hyperbus/i_phy/cfg_i*]
set_max_delay [expr min(${tck_sys}, ${tck_phy})] -through ${cfg_from} -through ${cfg_to}
set_false_path -hold -through ${cfg_from} -through ${cfg_to}
