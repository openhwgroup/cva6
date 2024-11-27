module oddr_intel (
		input  wire       ck,      //      ck.export, In input and output paths, this clock feeds a packed register or DDIO. In bidirectional mode, this clock is the unique clock for the input and output paths if you turn off the Separate input/output Clocks parameter.
		input  wire [1:0] din,     //     din.export, Data input from the FPGA core in output or bidirectional mode.
		output wire [0:0] pad_out  // pad_out.export, Output signal to the pad.Output signal to the pad.
	);
endmodule

