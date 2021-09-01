# REF CLOCK: 10 MHz, actually 32 KHz
set REF_C_Period                 100000.0
set REF_C_Latency_Max            1000
set REF_C_Latency_Min            500
set REF_C_Uncertainty            500

# FLL1 CLOCK: 200 MHz
set SOC_C_Period                 5000
set SOC_C_Latency_Max            500
set SOC_C_Latency_Min            500
set SOC_C_Uncertainty            100

# FLL2 CLOCK: 200 MHz
set PER_C_Period                 5000
set PER_C_Latency_Max            500
set PER_C_Latency_Min            500
set PER_C_Uncertainty            100

# FLL3 CLOCK: 200 MHz
set CLUSTER_C_Period             4000
set CLUSTER_C_Latency_Max        500
set CLUSTER_C_Latency_Min        500
set CLUSTER_C_Uncertainty        100

# JTAG:       20 MHz
set JTAG_C_Period                50000
set JTAG_C_Latency_Max           1000
set JTAG_C_Latency_Min           500
set JTAG_C_Uncertainty           100

# RWDS:       200 MHz
set RWDS_C_Period                5000
set RWDS_C_Latency_Max           1000
set RWDS_C_Latency_Min           500
set RWDS_C_Uncertainty           100

#############################
### PAD CLOCKS DEFINITION ###
#############################

# REF CLOCK
create_clock -name REF_CLK   -period      $REF_C_Period      [get_ports rtc_i]
set_ideal_network                                            [get_ports rtc_i]
set_dont_touch_network                                       [get_ports rtc_i]
set_clock_uncertainty                     $REF_C_Uncertainty [get_clocks REF_CLK]
set_clock_transition                      100                [get_clocks REF_CLK]
set_clock_latency -max                    $REF_C_Latency_Max [get_clocks REF_CLK]
set_clock_latency -min                    $REF_C_Latency_Min [get_clocks REF_CLK]

# JTAG CLK
create_clock -period $JTAG_C_Period -name JTAG_CLK [get_ports jtag_TCK]
set_ideal_network                                  [get_ports jtag_TCK]
set_dont_touch_network                             [get_ports jtag_TCK]
set_clock_uncertainty   $JTAG_C_Uncertainty        [get_clocks JTAG_CLK]
set_clock_transition    100                        [get_clocks JTAG_CLK]
set_clock_latency -max  $JTAG_C_Latency_Max        [get_clocks JTAG_CLK]
set_clock_latency -min  $JTAG_C_Latency_Min        [get_clocks JTAG_CLK]

# RWDS CLK
create_clock -period $RWDS_C_Period -name RWDS_CLK [get_ports pad_hyper_rwds0]
set_ideal_network                                  [get_ports pad_hyper_rwds0]
set_dont_touch_network                             [get_ports pad_hyper_rwds0]
set_clock_uncertainty   $RWDS_C_Uncertainty        [get_clocks RWDS_CLK]
set_clock_transition    100                        [get_clocks RWDS_CLK]
set_clock_latency -max  $RWDS_C_Latency_Max        [get_clocks RWDS_CLK]
set_clock_latency -min  $RWDS_C_Latency_Min        [get_clocks RWDS_CLK]

#############################
### FLL CLOCKS DEFINITION ###
#############################
create_clock -name FLL_CLUSTER_CLK -period  $CLUSTER_C_Period      [get_pins i_host_domain/i_apb_subsystem/i_alsaqr_clk_rst_gen/i_fll_cluster/FLLCLK]
set_ideal_network                                                  [get_pins i_host_domain/i_apb_subsystem/i_alsaqr_clk_rst_gen/i_fll_cluster/FLLCLK]
set_dont_touch_network                                             [get_pins i_host_domain/i_apb_subsystem/i_alsaqr_clk_rst_gen/i_fll_cluster/FLLCLK]
set_clock_uncertainty                       $CLUSTER_C_Uncertainty [get_clocks FLL_CLUSTER_CLK]
set_clock_transition                        100                    [get_clocks FLL_CLUSTER_CLK]
set_clock_latency -max                      $CLUSTER_C_Latency_Max [get_clocks FLL_CLUSTER_CLK]
set_clock_latency -min                      $CLUSTER_C_Latency_Min [get_clocks FLL_CLUSTER_CLK]

create_clock -name FLL_SOC_CLK -period      $SOC_C_Period      [get_pins i_host_domain/i_apb_subsystem/i_alsaqr_clk_rst_gen/i_fll_soc/FLLCLK]
set_ideal_network                                              [get_pins i_host_domain/i_apb_subsystem/i_alsaqr_clk_rst_gen/i_fll_soc/FLLCLK]
set_dont_touch_network                                         [get_pins i_host_domain/i_apb_subsystem/i_alsaqr_clk_rst_gen/i_fll_soc/FLLCLK]
set_clock_uncertainty                       $SOC_C_Uncertainty [get_clocks FLL_SOC_CLK]
set_clock_transition                        100                [get_clocks FLL_SOC_CLK]
set_clock_latency -max                      $SOC_C_Latency_Max [get_clocks FLL_SOC_CLK]
set_clock_latency -min                      $SOC_C_Latency_Min [get_clocks FLL_SOC_CLK]

create_clock -name FLL_PER_CLK -period      $PER_C_Period      [get_pins i_host_domain/i_apb_subsystem/i_alsaqr_clk_rst_gen/i_fll_per/FLLCLK]
set_ideal_network                                              [get_pins i_host_domain/i_apb_subsystem/i_alsaqr_clk_rst_gen/i_fll_per/FLLCLK]
set_dont_touch_network                                         [get_pins i_host_domain/i_apb_subsystem/i_alsaqr_clk_rst_gen/i_fll_per/FLLCLK]
set_clock_uncertainty                       $PER_C_Uncertainty [get_clocks FLL_PER_CLK]
set_clock_transition                        100                [get_clocks FLL_PER_CLK]
set_clock_latency -max                      $PER_C_Latency_Max [get_clocks FLL_PER_CLK]
set_clock_latency -min                      $PER_C_Latency_Min [get_clocks FLL_PER_CLK]


########################################
### GENERATED CLOCK FROM CLOCK MUXES ###
########################################
# SOC CLK
create_generated_clock         [get_pins i_host_domain/i_clk_gen_hyper/clk0_o] \
     -name AXI_HYPER_CLK_PHY -source [get_pins  i_host_domain/i_apb_subsystem/i_alsaqr_clk_rst_gen/i_fll_soc/FLLCLK] -divide_by 2

create_generated_clock         [get_pins i_host_domain/i_clk_gen_hyper/clk90_o] \
     -name AXI_HYPER_CLK_PHY_90 -source [get_pins  i_host_domain/i_apb_subsystem/i_alsaqr_clk_rst_gen/i_fll_soc/FLLCLK]  -edges {2 4 6}

