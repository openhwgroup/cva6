	emif_cal u0 (
		.calbus_read_0          (_connected_to_calbus_read_0_),          //  output,     width = 1,   emif_calbus_0.calbus_read
		.calbus_write_0         (_connected_to_calbus_write_0_),         //  output,     width = 1,                .calbus_write
		.calbus_address_0       (_connected_to_calbus_address_0_),       //  output,    width = 20,                .calbus_address
		.calbus_wdata_0         (_connected_to_calbus_wdata_0_),         //  output,    width = 32,                .calbus_wdata
		.calbus_rdata_0         (_connected_to_calbus_rdata_0_),         //   input,    width = 32,                .calbus_rdata
		.calbus_seq_param_tbl_0 (_connected_to_calbus_seq_param_tbl_0_), //   input,  width = 4096,                .calbus_seq_param_tbl
		.calbus_clk             (_connected_to_calbus_clk_)              //  output,     width = 1, emif_calbus_clk.clk
	);

