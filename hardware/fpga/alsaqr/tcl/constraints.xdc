#Create constraint for the clock input of the zcu102 board
create_clock -period 8.000 -name ref_clk [get_ports ref_clk_p]
set_property CLOCK_DEDICATED_ROUTE ANY_CMT_COLUMN [get_nets i_sysclk_iobuf/O]

#alsaqr clock
create_clock -period 100.000  [get_pins i_clk_manager/clk_out1]

## JTAG
create_clock -period 100.000 -name tck -waveform {0.000 50.000} [get_ports pad_jtag_tck]
set_input_jitter tck 1.000
set_property CLOCK_DEDICATED_ROUTE FALSE [get_nets pad_jtag_tck_IBUF_inst/O]


# minimize routing delay
set_input_delay -clock tck -clock_fall 5.000 [get_ports pad_jtag_tdi]
set_input_delay -clock tck -clock_fall 5.000 [get_ports pad_jtag_tms]
set_output_delay -clock tck 5.000 [get_ports pad_jtag_tdo]

set_max_delay -to [get_ports pad_jtag_tdo] 20.000
set_max_delay -from [get_ports pad_jtag_tms] 20.000
set_max_delay -from [get_ports pad_jtag_tdi] 20.000

set_max_delay -datapath_only -from [get_pins i_alsaqr/i_host_domain/i_cva_subsystem/i_dmi_jtag/i_dmi_cdc/i_cdc_resp/i_src/data_src_q_reg*/C] -to [get_pins i_alsaqr/i_host_domain/i_cva_subsystem/i_dmi_jtag/i_dmi_cdc/i_cdc_resp/i_dst/data_dst_q_reg*/D] 20.000
set_max_delay -datapath_only -from [get_pins i_alsaqr/i_host_domain/i_cva_subsystem/i_dmi_jtag/i_dmi_cdc/i_cdc_resp/i_src/req_src_q_reg/C]   -to [get_pins i_alsaqr/i_host_domain/i_cva_subsystem/i_dmi_jtag/i_dmi_cdc/i_cdc_resp/i_dst/req_dst_q_reg/D] 20.000
set_max_delay -datapath_only -from [get_pins i_alsaqr/i_host_domain/i_cva_subsystem/i_dmi_jtag/i_dmi_cdc/i_cdc_req/i_dst/ack_dst_q_reg/C]    -to [get_pins i_alsaqr/i_host_domain/i_cva_subsystem/i_dmi_jtag/i_dmi_cdc/i_cdc_req/i_src/ack_src_q_reg/D] 20.000


# reset signal
set_false_path -from [get_ports pad_reset]

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

# Create RWDS clock
create_clock -period 100.000 -name rwds_clk [get_ports FMC_hyper_rwds0]
set_property CLOCK_DEDICATED_ROUTE FALSE [get_nets i_alsaqr/i_pad_frame/padinst_axi_hyper_rwds0/iobuf_i/O]

# Create the PHY clock
create_generated_clock -name clk_phy -source [get_pins  i_clk_manager/clk_out1] -divide_by 2 [get_pins i_alsaqr/i_host_domain/i_clk_gen_hyper/clk0_o]
create_generated_clock -name clk_phy_90 -source [get_pins  i_clk_manager/clk_out1] -edges {2 4 6} [get_pins i_alsaqr/i_host_domain/i_clk_gen_hyper/clk90_o]

# Inform tool that system and PHY-derived clocks are asynchronous, but may have timed arcs between them
set_clock_groups -asynchronous -group [get_clocks -of_objects [get_pins  i_clk_manager/clk_out1]] -group [get_clocks -of_objects [get_pins i_alsaqr/i_host_domain/i_clk_gen_hyper/clk90_o]] -group [get_clocks -of_objects [get_pins i_alsaqr/i_host_domain/i_clk_gen_hyper/clk0_o]]


set_false_path -from [get_clocks clk_phy_90] -to [get_clocks clk_phy]
set_false_path -from [get_clocks clk_phy_90] -to [get_clocks rwds_clk]

## Constrain config register false paths to PHY
set cfg_from  [get_pins i_alsaqr/i_host_domain/axi_hyperbus/i_cfg_regs/cfg_o*]
set cfg_to    [get_pins i_alsaqr/i_host_domain/axi_hyperbus/i_phy/cfg_i*]
set_max_delay 25.000 -through ${cfg_from} -through ${cfg_to}
set_false_path -hold -through ${cfg_from} -through ${cfg_to}

set des i_alsaqr/i_host_domain/axi_hyperbus/i_cdc_2phase_trans
set async_ports [get_pins $des/*/async_*]
set_max_delay 25.000 -through ${async_ports} -through ${async_ports}
set_false_path -hold -through ${async_ports} -through ${async_ports}

set des i_alsaqr/i_host_domain/axi_hyperbus/i_cdc_2phase_trans
set async_ports [get_pins $des/*/async_*]
set_max_delay 25.000 -through ${async_ports} -through ${async_ports}
set_false_path -hold -through ${async_ports} -through ${async_ports}

set des i_alsaqr/i_host_domain/axi_hyperbus/i_cdc_fifo_tx
set async_ports [get_pins $des/*/async_*]
set_max_delay 25.000 -through ${async_ports} -through ${async_ports}
set_false_path -hold -through ${async_ports} -through ${async_ports}

set des i_alsaqr/i_host_domain/axi_hyperbus/i_cdc_fifo_rx
set async_ports [get_pins $des/*/async_*]
set_max_delay 25.000 -through ${async_ports} -through ${async_ports}
set_false_path -hold -through ${async_ports} -through ${async_ports}
 
