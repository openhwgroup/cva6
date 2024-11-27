	test_mm_ccb_0 #(
		.DATA_WIDTH          (INTEGER_VALUE_FOR_DATA_WIDTH),
		.SYMBOL_WIDTH        (INTEGER_VALUE_FOR_SYMBOL_WIDTH),
		.HDL_ADDR_WIDTH      (INTEGER_VALUE_FOR_HDL_ADDR_WIDTH),
		.BURSTCOUNT_WIDTH    (INTEGER_VALUE_FOR_BURSTCOUNT_WIDTH),
		.COMMAND_FIFO_DEPTH  (INTEGER_VALUE_FOR_COMMAND_FIFO_DEPTH),
		.RESPONSE_FIFO_DEPTH (INTEGER_VALUE_FOR_RESPONSE_FIFO_DEPTH),
		.MASTER_SYNC_DEPTH   (INTEGER_VALUE_FOR_MASTER_SYNC_DEPTH),
		.SLAVE_SYNC_DEPTH    (INTEGER_VALUE_FOR_SLAVE_SYNC_DEPTH),
		.SYNC_RESET          (INTEGER_VALUE_FOR_SYNC_RESET)
	) u0 (
		.m0_clk           (_connected_to_m0_clk_),           //   input,                 width = 1,   m0_clk.clk
		.m0_reset         (_connected_to_m0_reset_),         //   input,                 width = 1, m0_reset.reset
		.s0_clk           (_connected_to_s0_clk_),           //   input,                 width = 1,   s0_clk.clk
		.s0_reset         (_connected_to_s0_reset_),         //   input,                 width = 1, s0_reset.reset
		.s0_waitrequest   (_connected_to_s0_waitrequest_),   //  output,                 width = 1,       s0.waitrequest
		.s0_readdata      (_connected_to_s0_readdata_),      //  output,        width = DATA_WIDTH,         .readdata
		.s0_readdatavalid (_connected_to_s0_readdatavalid_), //  output,                 width = 1,         .readdatavalid
		.s0_burstcount    (_connected_to_s0_burstcount_),    //   input,  width = BURSTCOUNT_WIDTH,         .burstcount
		.s0_writedata     (_connected_to_s0_writedata_),     //   input,        width = DATA_WIDTH,         .writedata
		.s0_address       (_connected_to_s0_address_),       //   input,    width = HDL_ADDR_WIDTH,         .address
		.s0_write         (_connected_to_s0_write_),         //   input,                 width = 1,         .write
		.s0_read          (_connected_to_s0_read_),          //   input,                 width = 1,         .read
		.s0_byteenable    (_connected_to_s0_byteenable_),    //   input,                width = 64,         .byteenable
		.s0_debugaccess   (_connected_to_s0_debugaccess_),   //   input,                 width = 1,         .debugaccess
		.m0_waitrequest   (_connected_to_m0_waitrequest_),   //   input,                 width = 1,       m0.waitrequest
		.m0_readdata      (_connected_to_m0_readdata_),      //   input,        width = DATA_WIDTH,         .readdata
		.m0_readdatavalid (_connected_to_m0_readdatavalid_), //   input,                 width = 1,         .readdatavalid
		.m0_burstcount    (_connected_to_m0_burstcount_),    //  output,  width = BURSTCOUNT_WIDTH,         .burstcount
		.m0_writedata     (_connected_to_m0_writedata_),     //  output,        width = DATA_WIDTH,         .writedata
		.m0_address       (_connected_to_m0_address_),       //  output,    width = HDL_ADDR_WIDTH,         .address
		.m0_write         (_connected_to_m0_write_),         //  output,                 width = 1,         .write
		.m0_read          (_connected_to_m0_read_),          //  output,                 width = 1,         .read
		.m0_byteenable    (_connected_to_m0_byteenable_),    //  output,                width = 64,         .byteenable
		.m0_debugaccess   (_connected_to_m0_debugaccess_)    //  output,                 width = 1,         .debugaccess
	);

