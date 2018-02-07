set_false_path -reset_path -from [get_clocks clk_io_uart_clk_wiz_0] -to [get_clocks mmcm_clkout0]
set_false_path -reset_path -from [get_clocks mmcm_clkout0] -to [get_clocks clk_io_uart_clk_wiz_0]
