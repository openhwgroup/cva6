create_clock -period 10.000 -name clk_p -waveform {0.000 5.000} [get_ports clk_p]


create_clock -period 100.000 -name jtag1/BSCANE2_inst/TCK -waveform {0.000 50.000} [get_pins i_dbg/jtag1/BSCANE2_inst/TCK]
create_clock -period 40.000 -name dram_ctl/u_mig_7series_0_mig/u_ddr2_infrastructure/gen_ui_extra_clocks.mmcm_i/LOCKED -waveform {0.000 20.000} [get_pins dram_ctl/u_mig_7series_0_mig/u_ddr2_infrastructure/gen_ui_extra_clocks.mmcm_i/LOCKED]
