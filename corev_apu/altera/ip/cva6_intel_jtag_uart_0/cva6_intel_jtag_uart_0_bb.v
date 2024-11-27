module cva6_intel_jtag_uart_0 (
		input  wire        clk,            //               clk.clk
		input  wire        rst_n,          //             reset.reset_n
		input  wire        av_chipselect,  // avalon_jtag_slave.chipselect
		input  wire        av_address,     //                  .address
		input  wire        av_read_n,      //                  .read_n
		output wire [31:0] av_readdata,    //                  .readdata
		input  wire        av_write_n,     //                  .write_n
		input  wire [31:0] av_writedata,   //                  .writedata
		output wire        av_waitrequest, //                  .waitrequest
		output wire        av_irq          //               irq.irq
	);
endmodule

