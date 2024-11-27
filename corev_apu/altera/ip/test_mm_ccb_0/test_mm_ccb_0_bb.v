module test_mm_ccb_0 #(
		parameter DATA_WIDTH          = 512,
		parameter SYMBOL_WIDTH        = 8,
		parameter HDL_ADDR_WIDTH      = 27,
		parameter BURSTCOUNT_WIDTH    = 8,
		parameter COMMAND_FIFO_DEPTH  = 256,
		parameter RESPONSE_FIFO_DEPTH = 256,
		parameter MASTER_SYNC_DEPTH   = 2,
		parameter SLAVE_SYNC_DEPTH    = 2,
		parameter SYNC_RESET          = 1
	) (
		input  wire                        m0_clk,           //   m0_clk.clk
		input  wire                        m0_reset,         // m0_reset.reset
		input  wire                        s0_clk,           //   s0_clk.clk
		input  wire                        s0_reset,         // s0_reset.reset
		output wire                        s0_waitrequest,   //       s0.waitrequest
		output wire [DATA_WIDTH-1:0]       s0_readdata,      //         .readdata
		output wire                        s0_readdatavalid, //         .readdatavalid
		input  wire [BURSTCOUNT_WIDTH-1:0] s0_burstcount,    //         .burstcount
		input  wire [DATA_WIDTH-1:0]       s0_writedata,     //         .writedata
		input  wire [HDL_ADDR_WIDTH-1:0]   s0_address,       //         .address
		input  wire                        s0_write,         //         .write
		input  wire                        s0_read,          //         .read
		input  wire [63:0]                 s0_byteenable,    //         .byteenable
		input  wire                        s0_debugaccess,   //         .debugaccess
		input  wire                        m0_waitrequest,   //       m0.waitrequest
		input  wire [DATA_WIDTH-1:0]       m0_readdata,      //         .readdata
		input  wire                        m0_readdatavalid, //         .readdatavalid
		output wire [BURSTCOUNT_WIDTH-1:0] m0_burstcount,    //         .burstcount
		output wire [DATA_WIDTH-1:0]       m0_writedata,     //         .writedata
		output wire [HDL_ADDR_WIDTH-1:0]   m0_address,       //         .address
		output wire                        m0_write,         //         .write
		output wire                        m0_read,          //         .read
		output wire [63:0]                 m0_byteenable,    //         .byteenable
		output wire                        m0_debugaccess    //         .debugaccess
	);
endmodule

