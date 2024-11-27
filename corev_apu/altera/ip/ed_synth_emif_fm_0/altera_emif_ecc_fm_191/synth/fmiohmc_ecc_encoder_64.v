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
module fmiohmc_ecc_encoder_64 (
	data,
	q)/* synthesis synthesis_clearbox = 1 */;

	input	[63:0]  data;
	output	[71:0]  q;

	wire [71:0] sub_wire0;
	wire [71:0] q = sub_wire0[71:0];

	fmiohmc_ecc_encoder_64_altecc_encoder	iohmc_ecc_encoder_64_altecc_encoder_component (
				.data (data),
				.q (sub_wire0));

endmodule

`ifdef QUESTA_INTEL_OEM
`pragma questa_oem_00 "sfv4CgBD2gRw66FfSic/D/DxyUF4ju6abSGjNZTz+XJ5wNcp1RmzgamT61rscvjMkkNKCYCGE4Hkry++3eL2fSJkmOtrYLQextJ2AFr2kX/6sa63SwNG1Dg8CndZgqHpcPsbI8J/52/6EA/5eQJiUNmwpEDzzugi2WpUBRBy4gGrSJ7A8zUzUrkHlWNSHE1mVOTkuXrL/BUqA6hBwwkS7qZD/J3TRyAu6L9p+9tB0EB4BzQn2Y/UVGf2tm8a1y+zV+7wYOuLc0X6EeJpoj9owEblMPnFgpIFh3WFhtS1aXJcuhevzxr/r2K3mwQ82wTAKzTedqM4sOJx5H69XsvpRRT1z+2G74hsVBDK1EqOTGFthnDZVJvCPbW/WB8Mp87nVMiM9fyUL5gvhZ37WOTI35KqYbJBESQPV3xbqsF7Y80W+LccFO9A6cL7LZglhWSPjGK2nJQxE0Utv6HAWwpk1ZU99IG2mr4Ab4Txo4fnbzWjmOUrAwe+FXwY53eXMsfpPUgPUjDq55mt72VoulZT+zyGgA/3rRmSPU+JEhRk6PMGo2m6bRNmoQ8gadPNgvu+Gok41+O9p0Kr3dEUR/u48mY2F07T+jQPXIoxBeslKe42//BDHXdKZFg/0V9Au9pJ7AdpNCDwWfJ08rTguD2N2EQQUlw3UuruA9aoAp8EpxkCW6R6grTXLixMPCp6y4q7mCDfuTWPzyepYP0Mv1ShHXtU+P4GMqhOGHw5sLLbvCmmmTuxwZaYEFZZh44G305hWGjRHQp0TsX42/8QktIklwizFcQ5KXxd0OE2AekuH7R/BK1/7s699AVMFYSlr7+bSLKroj2jn4XVFTKXl01btL0yAUq5e1CV2vMwlDv4AuyekLQik/g6VxXUWBfk4aQnpVLxC1yxAunh48PBu3u12pDLlPPg8aQxy9L1zWHf9OJYVRyfrjr+Ww+OZalRvqqYfD4CrQBSi9uQGPY3gqwO2pASgjUrF0s5PF4b71Bp0CbCV+8ow2X8oYk/2ZepvRee"
`endif