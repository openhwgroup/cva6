	cva6_intel_jtag_uart_0 u0 (
		.clk            (_connected_to_clk_),            //   input,   width = 1,               clk.clk
		.rst_n          (_connected_to_rst_n_),          //   input,   width = 1,             reset.reset_n
		.av_chipselect  (_connected_to_av_chipselect_),  //   input,   width = 1, avalon_jtag_slave.chipselect
		.av_address     (_connected_to_av_address_),     //   input,   width = 1,                  .address
		.av_read_n      (_connected_to_av_read_n_),      //   input,   width = 1,                  .read_n
		.av_readdata    (_connected_to_av_readdata_),    //  output,  width = 32,                  .readdata
		.av_write_n     (_connected_to_av_write_n_),     //   input,   width = 1,                  .write_n
		.av_writedata   (_connected_to_av_writedata_),   //   input,  width = 32,                  .writedata
		.av_waitrequest (_connected_to_av_waitrequest_), //  output,   width = 1,                  .waitrequest
		.av_irq         (_connected_to_av_irq_)          //  output,   width = 1,               irq.irq
	);

