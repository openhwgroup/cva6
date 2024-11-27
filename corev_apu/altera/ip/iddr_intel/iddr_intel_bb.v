module iddr_intel (
		input  wire       ck,     //     ck.export, In input and output paths, this clock feeds a packed register or DDIO. In bidirectional mode, this clock is the unique clock for the input and output paths if you turn off the Separate input/output Clocks parameter.
		output wire [1:0] dout,   //   dout.export, Data output to the FPGA core in input or bidirectional mode, DATA_SIZE depends on the register mode: Bypass or simple register - DATA_SIZE = SIZE DDIO - DATA_SIZE = 2 x SIZE
		input  wire [0:0] pad_in  // pad_in.export, Input signal from the pad.
	);
endmodule

