module emif_cal (
		output wire          calbus_read_0,          //   emif_calbus_0.calbus_read,          EMIF Calibration component bus for read
		output wire          calbus_write_0,         //                .calbus_write,         EMIF Calibration component bus for write
		output wire [19:0]   calbus_address_0,       //                .calbus_address,       EMIF Calibration component bus for address
		output wire [31:0]   calbus_wdata_0,         //                .calbus_wdata,         EMIF Calibration component bus for write data
		input  wire [31:0]   calbus_rdata_0,         //                .calbus_rdata,         EMIF Calibration component bus for read data
		input  wire [4095:0] calbus_seq_param_tbl_0, //                .calbus_seq_param_tbl, EMIF Calibration component bus for parameter table data
		output wire          calbus_clk              // emif_calbus_clk.clk,                  EMIF Calibration component bus for the clock
	);
endmodule

