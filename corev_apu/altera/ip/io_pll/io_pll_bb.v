module io_pll (
		input  wire  refclk,   //  refclk.clk
		output wire  locked,   //  locked.export
		input  wire  rst,      //   reset.reset
		output wire  outclk_0, // outclk0.clk
		output wire  outclk_1, // outclk1.clk
		output wire  outclk_2, // outclk2.clk
		output wire  outclk_3, // outclk3.clk
		output wire  outclk_4  // outclk4.clk
	);
endmodule

