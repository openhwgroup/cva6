// (C) 2001-2024 Intel Corporation. All rights reserved.
// Your use of Intel Corporation's design tools, logic functions and other 
// software and tools, and its AMPP partner logic functions, and any output 
// files from any of the foregoing (including device programming or simulation 
// files), and any associated documentation or information are expressly subject 
// to the terms and conditions of the Intel Program License Subscription 
// Agreement, Intel FPGA IP License Agreement, or other applicable 
// license agreement, including, without limitation, that your use is for the 
// sole purpose of programming logic devices manufactured by Intel and sold by 
// Intel or its authorized distributors.  Please refer to the applicable 
// agreement for further details.







// synthesis VERILOG_INPUT_VERSION VERILOG_2001
//altera message_off 10463




`timescale 1 ps / 1 ps
module fmiohmc_ecc_decoder_64 (
	data,
	err_corrected,
	err_detected,
	err_fatal,
	err_sbe,
	q)/* synthesis synthesis_clearbox = 1 */;

	input	[71:0]  data;
	output	  err_corrected;
	output	  err_detected;
	output	  err_fatal;
	output	  err_sbe;
	output	[63:0]  q;

	wire  sub_wire0;
	wire  sub_wire1;
	wire  sub_wire2;
	wire  sub_wire4;
	wire [63:0] sub_wire3;
	wire  err_detected = sub_wire0;
	wire  err_fatal = sub_wire1;
	wire  err_corrected = sub_wire2;
	wire  err_sbe = sub_wire4;
	wire [63:0] q = sub_wire3[63:0];

	fmiohmc_ecc_decoder_64_altecc_decoder	iohmc_ecc_decoder_64_altecc_decoder_component (
				.data (data),
				.err_detected (sub_wire0),
				.err_fatal (sub_wire1),
				.err_corrected (sub_wire2),
				.err_sbe (sub_wire4),
				.q (sub_wire3));

endmodule

`ifdef QUESTA_INTEL_OEM
`pragma questa_oem_00 "sfv4CgBD2gRw66FfSic/D/DxyUF4ju6abSGjNZTz+XJ5wNcp1RmzgamT61rscvjMkkNKCYCGE4Hkry++3eL2fSJkmOtrYLQextJ2AFr2kX/6sa63SwNG1Dg8CndZgqHpcPsbI8J/52/6EA/5eQJiUNmwpEDzzugi2WpUBRBy4gGrSJ7A8zUzUrkHlWNSHE1mVOTkuXrL/BUqA6hBwwkS7qZD/J3TRyAu6L9p+9tB0EAUMKAt1mmYg3PY9ycWv2MGbuI4C+9okTgCG7iF5iEXDiJSguaAP/gcb2Pn1mwe+0dRPsDFFp5utgX18MMQ/MhLKFhVG1uUiWUJYyospLN0F5+8aM2y0XGia78C+Hzt1rH92rxquyAZUp09mUShEekbhtIPExUQkxWwq67M8hO4WgSF4Kqbkboc6+LjpubOrEAll2t4l8BVcI24HR5+4m+Hafb8Cx7khiX7xY0ExsA4SmkKOxs2xXuPWovA5xWyMeO9zfh+M1ie6LlVB6Qoo31qWBTMLds7dKOBxbAmcYF1Po//kQMDX8wB+me6FDLjvH3r25lTzQxLPdbaQ1s648p/KQIChW2+dYamQZGWPFHkb+tDLBPjeS2+VAnPkExAPcCU8aQPtVVuQgspZrRCOyiYlvpZJ+VDxD+MFDp98l014L1OuGfx7SpPT3lzaIfvwBVDKgASysKVwZwNswzV908eW5S2BXdTjc34oARt6YQdJss1HbUVBv9+D3OafIE7dwJhyBk8NV594PUZzhPg0u61rCuOU3CUR3UVwHTOSgKhsIgIz+RXTV3CGrAtcESmITRA9V7KSat/KmFFrG7/CjOywg392ljew6Fx3xRQvdqm9T7aXW39h1PyaQfgG2fAekfBq7g/35i4fz904VyQk9Qq7EfRhbzlx4nu9js1OL281F2yBmQ2pjDJNrsjpMancNwOw2Cy8npM0LtwPROWzwG8xMq2Wjc2nWMSsVrR/zSUwEzovUfmRDd1QTFNH0h3itCyA634CJuT9suCqz/TAmB9"
`endif