create_clock -period 10.000 -name clk_p -waveform {0.000 5.000} [get_ports clk_p]
create_clock -period 100.000 -name dut/jtag1/BSCANE2_inst/TCK -waveform {0.000 50.000} [get_pins dut/jtag1/BSCANE2_inst/TCK]
create_clock -period 40.000 -name {dut/i_ariane/ex_stage_i/lsu_i/i_nbdcache/i_miss_handler/i_bypass_arbiter/req_q_reg[id][1]/Q} -waveform {0.000 5.000} [get_pins {dut/i_ariane/ex_stage_i/lsu_i/i_nbdcache/i_miss_handler/i_bypass_arbiter/req_q_reg[id][1]/Q}]
