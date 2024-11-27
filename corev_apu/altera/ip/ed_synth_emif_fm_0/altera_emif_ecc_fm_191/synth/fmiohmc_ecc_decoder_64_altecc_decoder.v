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


// synthesis_resources = lut 144 mux21 64 
`timescale 1 ps / 1 ps
module  fmiohmc_ecc_decoder_64_altecc_decoder
	( 
	data,
	err_corrected,
	err_detected,
	err_fatal,
	err_sbe,
	q) /* synthesis synthesis_clearbox=1 */;
	input   [71:0]  data;
	output   err_corrected;
	output   err_detected;
	output   err_fatal;
	output   err_sbe;
	output   [63:0]  q;

	wire  [127:0]   wire_error_bit_decoder_eq;
	wire	wire_mux21_0_dataout;
	wire	wire_mux21_1_dataout;
	wire	wire_mux21_10_dataout;
	wire	wire_mux21_11_dataout;
	wire	wire_mux21_12_dataout;
	wire	wire_mux21_13_dataout;
	wire	wire_mux21_14_dataout;
	wire	wire_mux21_15_dataout;
	wire	wire_mux21_16_dataout;
	wire	wire_mux21_17_dataout;
	wire	wire_mux21_18_dataout;
	wire	wire_mux21_19_dataout;
	wire	wire_mux21_2_dataout;
	wire	wire_mux21_20_dataout;
	wire	wire_mux21_21_dataout;
	wire	wire_mux21_22_dataout;
	wire	wire_mux21_23_dataout;
	wire	wire_mux21_24_dataout;
	wire	wire_mux21_25_dataout;
	wire	wire_mux21_26_dataout;
	wire	wire_mux21_27_dataout;
	wire	wire_mux21_28_dataout;
	wire	wire_mux21_29_dataout;
	wire	wire_mux21_3_dataout;
	wire	wire_mux21_30_dataout;
	wire	wire_mux21_31_dataout;
	wire	wire_mux21_32_dataout;
	wire	wire_mux21_33_dataout;
	wire	wire_mux21_34_dataout;
	wire	wire_mux21_35_dataout;
	wire	wire_mux21_36_dataout;
	wire	wire_mux21_37_dataout;
	wire	wire_mux21_38_dataout;
	wire	wire_mux21_39_dataout;
	wire	wire_mux21_4_dataout;
	wire	wire_mux21_40_dataout;
	wire	wire_mux21_41_dataout;
	wire	wire_mux21_42_dataout;
	wire	wire_mux21_43_dataout;
	wire	wire_mux21_44_dataout;
	wire	wire_mux21_45_dataout;
	wire	wire_mux21_46_dataout;
	wire	wire_mux21_47_dataout;
	wire	wire_mux21_48_dataout;
	wire	wire_mux21_49_dataout;
	wire	wire_mux21_5_dataout;
	wire	wire_mux21_50_dataout;
	wire	wire_mux21_51_dataout;
	wire	wire_mux21_52_dataout;
	wire	wire_mux21_53_dataout;
	wire	wire_mux21_54_dataout;
	wire	wire_mux21_55_dataout;
	wire	wire_mux21_56_dataout;
	wire	wire_mux21_57_dataout;
	wire	wire_mux21_58_dataout;
	wire	wire_mux21_59_dataout;
	wire	wire_mux21_6_dataout;
	wire	wire_mux21_60_dataout;
	wire	wire_mux21_61_dataout;
	wire	wire_mux21_62_dataout;
	wire	wire_mux21_63_dataout;
	wire	wire_mux21_7_dataout;
	wire	wire_mux21_8_dataout;
	wire	wire_mux21_9_dataout;
	wire  data_bit;
	wire  [63:0]  data_t;
	wire  [71:0]  data_wire;
	wire  [127:0]  decode_output;
	wire  err_corrected_wire;
	wire  err_detected_wire;
	wire  err_fatal_wire;
	wire  [35:0]  parity_01_wire;
	wire  [17:0]  parity_02_wire;
	wire  [8:0]  parity_03_wire;
	wire  [3:0]  parity_04_wire;
	wire  [1:0]  parity_05_wire;
	wire  [30:0]  parity_06_wire;
	wire  [6:0]  parity_07_wire;
	wire  parity_bit;
	wire  [70:0]  parity_final_wire;
	wire  [6:0]  parity_t;
	wire  [63:0]  q_wire;
	wire  syn_bit;
	wire  syn_e;
	wire  [5:0]  syn_t;
	wire  [7:0]  syndrome;

	fmiohmc_ecc_decoder_64_decode   error_bit_decoder
	( 
	.data(syndrome[6:0]),
	.eq(wire_error_bit_decoder_eq));
	assign		wire_mux21_0_dataout = (syndrome[7] == 1'b1) ? (decode_output[3] ^ data_wire[0]) : data_wire[0];
	assign		wire_mux21_1_dataout = (syndrome[7] == 1'b1) ? (decode_output[5] ^ data_wire[1]) : data_wire[1];
	assign		wire_mux21_10_dataout = (syndrome[7] == 1'b1) ? (decode_output[15] ^ data_wire[10]) : data_wire[10];
	assign		wire_mux21_11_dataout = (syndrome[7] == 1'b1) ? (decode_output[17] ^ data_wire[11]) : data_wire[11];
	assign		wire_mux21_12_dataout = (syndrome[7] == 1'b1) ? (decode_output[18] ^ data_wire[12]) : data_wire[12];
	assign		wire_mux21_13_dataout = (syndrome[7] == 1'b1) ? (decode_output[19] ^ data_wire[13]) : data_wire[13];
	assign		wire_mux21_14_dataout = (syndrome[7] == 1'b1) ? (decode_output[20] ^ data_wire[14]) : data_wire[14];
	assign		wire_mux21_15_dataout = (syndrome[7] == 1'b1) ? (decode_output[21] ^ data_wire[15]) : data_wire[15];
	assign		wire_mux21_16_dataout = (syndrome[7] == 1'b1) ? (decode_output[22] ^ data_wire[16]) : data_wire[16];
	assign		wire_mux21_17_dataout = (syndrome[7] == 1'b1) ? (decode_output[23] ^ data_wire[17]) : data_wire[17];
	assign		wire_mux21_18_dataout = (syndrome[7] == 1'b1) ? (decode_output[24] ^ data_wire[18]) : data_wire[18];
	assign		wire_mux21_19_dataout = (syndrome[7] == 1'b1) ? (decode_output[25] ^ data_wire[19]) : data_wire[19];
	assign		wire_mux21_2_dataout = (syndrome[7] == 1'b1) ? (decode_output[6] ^ data_wire[2]) : data_wire[2];
	assign		wire_mux21_20_dataout = (syndrome[7] == 1'b1) ? (decode_output[26] ^ data_wire[20]) : data_wire[20];
	assign		wire_mux21_21_dataout = (syndrome[7] == 1'b1) ? (decode_output[27] ^ data_wire[21]) : data_wire[21];
	assign		wire_mux21_22_dataout = (syndrome[7] == 1'b1) ? (decode_output[28] ^ data_wire[22]) : data_wire[22];
	assign		wire_mux21_23_dataout = (syndrome[7] == 1'b1) ? (decode_output[29] ^ data_wire[23]) : data_wire[23];
	assign		wire_mux21_24_dataout = (syndrome[7] == 1'b1) ? (decode_output[30] ^ data_wire[24]) : data_wire[24];
	assign		wire_mux21_25_dataout = (syndrome[7] == 1'b1) ? (decode_output[31] ^ data_wire[25]) : data_wire[25];
	assign		wire_mux21_26_dataout = (syndrome[7] == 1'b1) ? (decode_output[33] ^ data_wire[26]) : data_wire[26];
	assign		wire_mux21_27_dataout = (syndrome[7] == 1'b1) ? (decode_output[34] ^ data_wire[27]) : data_wire[27];
	assign		wire_mux21_28_dataout = (syndrome[7] == 1'b1) ? (decode_output[35] ^ data_wire[28]) : data_wire[28];
	assign		wire_mux21_29_dataout = (syndrome[7] == 1'b1) ? (decode_output[36] ^ data_wire[29]) : data_wire[29];
	assign		wire_mux21_3_dataout = (syndrome[7] == 1'b1) ? (decode_output[7] ^ data_wire[3]) : data_wire[3];
	assign		wire_mux21_30_dataout = (syndrome[7] == 1'b1) ? (decode_output[37] ^ data_wire[30]) : data_wire[30];
	assign		wire_mux21_31_dataout = (syndrome[7] == 1'b1) ? (decode_output[38] ^ data_wire[31]) : data_wire[31];
	assign		wire_mux21_32_dataout = (syndrome[7] == 1'b1) ? (decode_output[39] ^ data_wire[32]) : data_wire[32];
	assign		wire_mux21_33_dataout = (syndrome[7] == 1'b1) ? (decode_output[40] ^ data_wire[33]) : data_wire[33];
	assign		wire_mux21_34_dataout = (syndrome[7] == 1'b1) ? (decode_output[41] ^ data_wire[34]) : data_wire[34];
	assign		wire_mux21_35_dataout = (syndrome[7] == 1'b1) ? (decode_output[42] ^ data_wire[35]) : data_wire[35];
	assign		wire_mux21_36_dataout = (syndrome[7] == 1'b1) ? (decode_output[43] ^ data_wire[36]) : data_wire[36];
	assign		wire_mux21_37_dataout = (syndrome[7] == 1'b1) ? (decode_output[44] ^ data_wire[37]) : data_wire[37];
	assign		wire_mux21_38_dataout = (syndrome[7] == 1'b1) ? (decode_output[45] ^ data_wire[38]) : data_wire[38];
	assign		wire_mux21_39_dataout = (syndrome[7] == 1'b1) ? (decode_output[46] ^ data_wire[39]) : data_wire[39];
	assign		wire_mux21_4_dataout = (syndrome[7] == 1'b1) ? (decode_output[9] ^ data_wire[4]) : data_wire[4];
	assign		wire_mux21_40_dataout = (syndrome[7] == 1'b1) ? (decode_output[47] ^ data_wire[40]) : data_wire[40];
	assign		wire_mux21_41_dataout = (syndrome[7] == 1'b1) ? (decode_output[48] ^ data_wire[41]) : data_wire[41];
	assign		wire_mux21_42_dataout = (syndrome[7] == 1'b1) ? (decode_output[49] ^ data_wire[42]) : data_wire[42];
	assign		wire_mux21_43_dataout = (syndrome[7] == 1'b1) ? (decode_output[50] ^ data_wire[43]) : data_wire[43];
	assign		wire_mux21_44_dataout = (syndrome[7] == 1'b1) ? (decode_output[51] ^ data_wire[44]) : data_wire[44];
	assign		wire_mux21_45_dataout = (syndrome[7] == 1'b1) ? (decode_output[52] ^ data_wire[45]) : data_wire[45];
	assign		wire_mux21_46_dataout = (syndrome[7] == 1'b1) ? (decode_output[53] ^ data_wire[46]) : data_wire[46];
	assign		wire_mux21_47_dataout = (syndrome[7] == 1'b1) ? (decode_output[54] ^ data_wire[47]) : data_wire[47];
	assign		wire_mux21_48_dataout = (syndrome[7] == 1'b1) ? (decode_output[55] ^ data_wire[48]) : data_wire[48];
	assign		wire_mux21_49_dataout = (syndrome[7] == 1'b1) ? (decode_output[56] ^ data_wire[49]) : data_wire[49];
	assign		wire_mux21_5_dataout = (syndrome[7] == 1'b1) ? (decode_output[10] ^ data_wire[5]) : data_wire[5];
	assign		wire_mux21_50_dataout = (syndrome[7] == 1'b1) ? (decode_output[57] ^ data_wire[50]) : data_wire[50];
	assign		wire_mux21_51_dataout = (syndrome[7] == 1'b1) ? (decode_output[58] ^ data_wire[51]) : data_wire[51];
	assign		wire_mux21_52_dataout = (syndrome[7] == 1'b1) ? (decode_output[59] ^ data_wire[52]) : data_wire[52];
	assign		wire_mux21_53_dataout = (syndrome[7] == 1'b1) ? (decode_output[60] ^ data_wire[53]) : data_wire[53];
	assign		wire_mux21_54_dataout = (syndrome[7] == 1'b1) ? (decode_output[61] ^ data_wire[54]) : data_wire[54];
	assign		wire_mux21_55_dataout = (syndrome[7] == 1'b1) ? (decode_output[62] ^ data_wire[55]) : data_wire[55];
	assign		wire_mux21_56_dataout = (syndrome[7] == 1'b1) ? (decode_output[63] ^ data_wire[56]) : data_wire[56];
	assign		wire_mux21_57_dataout = (syndrome[7] == 1'b1) ? (decode_output[65] ^ data_wire[57]) : data_wire[57];
	assign		wire_mux21_58_dataout = (syndrome[7] == 1'b1) ? (decode_output[66] ^ data_wire[58]) : data_wire[58];
	assign		wire_mux21_59_dataout = (syndrome[7] == 1'b1) ? (decode_output[67] ^ data_wire[59]) : data_wire[59];
	assign		wire_mux21_6_dataout = (syndrome[7] == 1'b1) ? (decode_output[11] ^ data_wire[6]) : data_wire[6];
	assign		wire_mux21_60_dataout = (syndrome[7] == 1'b1) ? (decode_output[68] ^ data_wire[60]) : data_wire[60];
	assign		wire_mux21_61_dataout = (syndrome[7] == 1'b1) ? (decode_output[69] ^ data_wire[61]) : data_wire[61];
	assign		wire_mux21_62_dataout = (syndrome[7] == 1'b1) ? (decode_output[70] ^ data_wire[62]) : data_wire[62];
	assign		wire_mux21_63_dataout = (syndrome[7] == 1'b1) ? (decode_output[71] ^ data_wire[63]) : data_wire[63];
	assign		wire_mux21_7_dataout = (syndrome[7] == 1'b1) ? (decode_output[12] ^ data_wire[7]) : data_wire[7];
	assign		wire_mux21_8_dataout = (syndrome[7] == 1'b1) ? (decode_output[13] ^ data_wire[8]) : data_wire[8];
	assign		wire_mux21_9_dataout = (syndrome[7] == 1'b1) ? (decode_output[14] ^ data_wire[9]) : data_wire[9];
	assign
		data_bit = data_t[63],
		data_t = {(data_t[62] | decode_output[71]), (data_t[61] | decode_output[70]), (data_t[60] | decode_output[69]), (data_t[59] | decode_output[68]), (data_t[58] | decode_output[67]), (data_t[57] | decode_output[66]), (data_t[56] | decode_output[65]), (data_t[55] | decode_output[63]), (data_t[54] | decode_output[62]), (data_t[53] | decode_output[61]), (data_t[52] | decode_output[60]), (data_t[51] | decode_output[59]), (data_t[50] | decode_output[58]), (data_t[49] | decode_output[57]), (data_t[48] | decode_output[56]), (data_t[47] | decode_output[55]), (data_t[46] | decode_output[54]), (data_t[45] | decode_output[53]), (data_t[44] | decode_output[52]), (data_t[43] | decode_output[51]), (data_t[42] | decode_output[50]), (data_t[41] | decode_output[49]), (data_t[40] | decode_output[48]), (data_t[39] | decode_output[47]), (data_t[38] | decode_output[46]), (data_t[37] | decode_output[45]), (data_t[36] | decode_output[44]), (data_t[35] | decode_output[43]), (data_t[34] | decode_output[42]), (data_t[33] | decode_output[41]), (data_t[32] | decode_output[40]), (data_t[31] | decode_output[39]), (data_t[30] | decode_output[38]), (data_t[29] | decode_output[37]), (data_t[28] | decode_output[36]), (data_t[27] | decode_output[35]), (data_t[26] | decode_output[34]), (data_t[25] | decode_output[33]), (data_t[24] | decode_output[31]), (data_t[23] | decode_output[30]), (data_t[22] | decode_output[29]), (data_t[21] | decode_output[28]), (data_t[20] | decode_output[27]), (data_t[19] | decode_output[26]), (data_t[18] | decode_output[25]), (data_t[17] | decode_output[24]), (data_t[16] | decode_output[23]), (data_t[15] | decode_output[22]), (data_t[14] | decode_output[21]), (data_t[13] | decode_output[20]), (data_t[12] | decode_output[19]), (data_t[11] | decode_output[18]), (data_t[10] | decode_output[17]), (data_t[9] | decode_output[15]), (data_t[8] | decode_output[14]), (data_t[7] | decode_output[13]), (data_t[6] | decode_output[12]), (data_t[5] | decode_output[11]), (data_t[4] | decode_output[10]), (data_t[3] | decode_output[9]), (data_t[2]
 | decode_output[7]), (data_t[1] | decode_output[6]), (data_t[0] | decode_output[5]), decode_output[3]},
		data_wire = data,
		decode_output = wire_error_bit_decoder_eq,
		err_corrected = err_corrected_wire,
		err_corrected_wire = ((syn_bit & syn_e) & data_bit),
		err_detected = err_detected_wire,
		err_detected_wire = (syn_bit & (~ (syn_e & parity_bit))),
		err_fatal = err_fatal_wire,
		err_fatal_wire = (err_detected_wire & (~ err_corrected_wire)),
		err_sbe = syn_e,
		parity_01_wire = {(data_wire[63] ^ parity_01_wire[34]), (data_wire[61] ^ parity_01_wire[33]), (data_wire[59] ^ parity_01_wire[32]), (data_wire[57] ^ parity_01_wire[31]), (data_wire[56] ^ parity_01_wire[30]), (data_wire[54] ^ parity_01_wire[29]), (data_wire[52] ^ parity_01_wire[28]), (data_wire[50] ^ parity_01_wire[27]), (data_wire[48] ^ parity_01_wire[26]), (data_wire[46] ^ parity_01_wire[25]), (data_wire[44] ^ parity_01_wire[24]), (data_wire[42] ^ parity_01_wire[23]), (data_wire[40] ^ parity_01_wire[22]), (data_wire[38] ^ parity_01_wire[21]), (data_wire[36] ^ parity_01_wire[20]), (data_wire[34] ^ parity_01_wire[19]), (data_wire[32] ^ parity_01_wire[18]), (data_wire[30] ^ parity_01_wire[17]), (data_wire[28] ^ parity_01_wire[16]), (data_wire[26] ^ parity_01_wire[15]), (data_wire[25] ^ parity_01_wire[14]), (data_wire[23] ^ parity_01_wire[13]), (data_wire[21] ^ parity_01_wire[12]), (data_wire[19] ^ parity_01_wire[11]), (data_wire[17] ^ parity_01_wire[10]), (data_wire[15] ^ parity_01_wire[9]), (data_wire[13] ^ parity_01_wire[8]), (data_wire[11] ^ parity_01_wire[7]), (data_wire[10] ^ parity_01_wire[6]), (data_wire[8] ^ parity_01_wire[5]), (data_wire[6] ^ parity_01_wire[4]), (data_wire[4] ^ parity_01_wire[3]), (data_wire[3] ^ parity_01_wire[2]), (data_wire[1] ^ parity_01_wire[1]), (data_wire[0] ^ parity_01_wire[0]), data_wire[64]},
		parity_02_wire = {((data_wire[62] ^ data_wire[63]) ^ parity_02_wire[16]), ((data_wire[58] ^ data_wire[59]) ^ parity_02_wire[15]), ((data_wire[55] ^ data_wire[56]) ^ parity_02_wire[14]), ((data_wire[51] ^ data_wire[52]) ^ parity_02_wire[13]), ((data_wire[47] ^ data_wire[48]) ^ parity_02_wire[12]), ((data_wire[43] ^ data_wire[44]) ^ parity_02_wire[11]), ((data_wire[39] ^ data_wire[40]) ^ parity_02_wire[10]), ((data_wire[35] ^ data_wire[36]) ^ parity_02_wire[9]), ((data_wire[31] ^ data_wire[32]) ^ parity_02_wire[8]), ((data_wire[27] ^ data_wire[28]) ^ parity_02_wire[7]), ((data_wire[24] ^ data_wire[25]) ^ parity_02_wire[6]), ((data_wire[20] ^ data_wire[21]) ^ parity_02_wire[5]), ((data_wire[16] ^ data_wire[17]) ^ parity_02_wire[4]), ((data_wire[12] ^ data_wire[13]) ^ parity_02_wire[3]), ((data_wire[9] ^ data_wire[10]) ^ parity_02_wire[2]), ((data_wire[5] ^ data_wire[6]) ^ parity_02_wire[1]), ((data_wire[2] ^ data_wire[3]) ^ parity_02_wire[0]), (data_wire[65] ^ data_wire[0])},
		parity_03_wire = {((((data_wire[60] ^ data_wire[61]) ^ data_wire[62]) ^ data_wire[63]) ^ parity_03_wire[7]), ((((data_wire[53] ^ data_wire[54]) ^ data_wire[55]) ^ data_wire[56]) ^ parity_03_wire[6]), ((((data_wire[45] ^ data_wire[46]) ^ data_wire[47]) ^ data_wire[48]) ^ parity_03_wire[5]), ((((data_wire[37] ^ data_wire[38]) ^ data_wire[39]) ^ data_wire[40]) ^ parity_03_wire[4]), ((((data_wire[29] ^ data_wire[30]) ^ data_wire[31]) ^ data_wire[32]) ^ parity_03_wire[3]), ((((data_wire[22] ^ data_wire[23]) ^ data_wire[24]) ^ data_wire[25]) ^ parity_03_wire[2]), ((((data_wire[14] ^ data_wire[15]) ^ data_wire[16]) ^ data_wire[17]) ^ parity_03_wire[1]), ((((data_wire[7] ^ data_wire[8]) ^ data_wire[9]) ^ data_wire[10]) ^ parity_03_wire[0]), (((data_wire[66] ^ data_wire[1]) ^ data_wire[2]) ^ data_wire[3])},
		parity_04_wire = {((((((((data_wire[49] ^ data_wire[50]) ^ data_wire[51]) ^ data_wire[52]) ^ data_wire[53]) ^ data_wire[54]) ^ data_wire[55]) ^ data_wire[56]) ^ parity_04_wire[2]), ((((((((data_wire[33] ^ data_wire[34]) ^ data_wire[35]) ^ data_wire[36]) ^ data_wire[37]) ^ data_wire[38]) ^ data_wire[39]) ^ data_wire[40]) ^ parity_04_wire[1]), ((((((((data_wire[18] ^ data_wire[19]) ^ data_wire[20]) ^ data_wire[21]) ^ data_wire[22]) ^ data_wire[23]) ^ data_wire[24]) ^ data_wire[25]) ^ parity_04_wire[0]), (((((((data_wire[67] ^ data_wire[4]) ^ data_wire[5]) ^ data_wire[6]) ^ data_wire[7]) ^ data_wire[8]) ^ data_wire[9]) ^ data_wire[10])},
		parity_05_wire = {((((((((((((((((data_wire[41] ^ data_wire[42]) ^ data_wire[43]) ^ data_wire[44]) ^ data_wire[45]) ^ data_wire[46]) ^ data_wire[47]) ^ data_wire[48]) ^ data_wire[49]) ^ data_wire[50]) ^ data_wire[51]) ^ data_wire[52]) ^ data_wire[53]) ^ data_wire[54]) ^ data_wire[55]) ^ data_wire[56]) ^ parity_05_wire[0]), (((((((((((((((data_wire[68] ^ data_wire[11]) ^ data_wire[12]) ^ data_wire[13]) ^ data_wire[14]) ^ data_wire[15]) ^ data_wire[16]) ^ data_wire[17]) ^ data_wire[18]) ^ data_wire[19]) ^ data_wire[20]) ^ data_wire[21]) ^ data_wire[22]) ^ data_wire[23]) ^ data_wire[24]) ^ data_wire[25])},
		parity_06_wire = {(data_wire[56] ^ parity_06_wire[29]), (data_wire[55] ^ parity_06_wire[28]), (data_wire[54] ^ parity_06_wire[27]), (data_wire[53] ^ parity_06_wire[26]), (data_wire[52] ^ parity_06_wire[25]), (data_wire[51] ^ parity_06_wire[24]), (data_wire[50] ^ parity_06_wire[23]), (data_wire[49] ^ parity_06_wire[22]), (data_wire[48] ^ parity_06_wire[21]), (data_wire[47] ^ parity_06_wire[20]), (data_wire[46] ^ parity_06_wire[19]), (data_wire[45] ^ parity_06_wire[18]), (data_wire[44] ^ parity_06_wire[17]), (data_wire[43] ^ parity_06_wire[16]), (data_wire[42] ^ parity_06_wire[15]), (data_wire[41] ^ parity_06_wire[14]), (data_wire[40] ^ parity_06_wire[13]), (data_wire[39] ^ parity_06_wire[12]), (data_wire[38] ^ parity_06_wire[11]), (data_wire[37] ^ parity_06_wire[10]), (data_wire[36] ^ parity_06_wire[9]), (data_wire[35] ^ parity_06_wire[8]), (data_wire[34] ^ parity_06_wire[7]), (data_wire[33] ^ parity_06_wire[6]), (data_wire[32] ^ parity_06_wire[5]), (data_wire[31] ^ parity_06_wire[4]), (data_wire[30] ^ parity_06_wire[3]), (data_wire[29] ^ parity_06_wire[2]), (data_wire[28] ^ parity_06_wire[1]), (data_wire[27] ^ parity_06_wire[0]), (data_wire[69] ^ data_wire[26])},
		parity_07_wire = {(data_wire[63] ^ parity_07_wire[5]), (data_wire[62] ^ parity_07_wire[4]), (data_wire[61] ^ parity_07_wire[3]), (data_wire[60] ^ parity_07_wire[2]), (data_wire[59] ^ parity_07_wire[1]), (data_wire[58] ^ parity_07_wire[0]), (data_wire[70] ^ data_wire[57])},
		parity_bit = parity_t[6],
		parity_final_wire = {(data_wire[70] ^ parity_final_wire[69]), (data_wire[69] ^ parity_final_wire[68]), (data_wire[68] ^ parity_final_wire[67]), (data_wire[67] ^ parity_final_wire[66]), (data_wire[66] ^ parity_final_wire[65]), (data_wire[65] ^ parity_final_wire[64]), (data_wire[64] ^ parity_final_wire[63]), (data_wire[63] ^ parity_final_wire[62]), (data_wire[62] ^ parity_final_wire[61]), (data_wire[61] ^ parity_final_wire[60]), (data_wire[60] ^ parity_final_wire[59]), (data_wire[59] ^ parity_final_wire[58]), (data_wire[58] ^ parity_final_wire[57]), (data_wire[57] ^ parity_final_wire[56]), (data_wire[56] ^ parity_final_wire[55]), (data_wire[55] ^ parity_final_wire[54]), (data_wire[54] ^ parity_final_wire[53]), (data_wire[53] ^ parity_final_wire[52]), (data_wire[52] ^ parity_final_wire[51]), (data_wire[51] ^ parity_final_wire[50]), (data_wire[50] ^ parity_final_wire[49]), (data_wire[49] ^ parity_final_wire[48]), (data_wire[48] ^ parity_final_wire[47]), (data_wire[47] ^ parity_final_wire[46]), (data_wire[46] ^ parity_final_wire[45]), (data_wire[45] ^ parity_final_wire[44]), (data_wire[44] ^ parity_final_wire[43]), (data_wire[43] ^ parity_final_wire[42]), (data_wire[42] ^ parity_final_wire[41]), (data_wire[41] ^ parity_final_wire[40]), (data_wire[40] ^ parity_final_wire[39]), (data_wire[39] ^ parity_final_wire[38]), (data_wire[38] ^ parity_final_wire[37]), (data_wire[37] ^ parity_final_wire[36]), (data_wire[36] ^ parity_final_wire[35]), (data_wire[35] ^ parity_final_wire[34]), (data_wire[34] ^ parity_final_wire[33]), (data_wire[33] ^ parity_final_wire[32]), (data_wire[32] ^ parity_final_wire[31]), (data_wire[31] ^ parity_final_wire[30]), (data_wire[30] ^ parity_final_wire[29]), (data_wire[29] ^ parity_final_wire[28]), (data_wire[28] ^ parity_final_wire[27]), (data_wire[27] ^ parity_final_wire[26]), (data_wire[26] ^ parity_final_wire[25]), (data_wire[25] ^ parity_final_wire[24]), (data_wire[24] ^ parity_final_wire[23]), (data_wire[23] ^ parity_final_wire[22]), (data_wire[22] ^ parity_final_wire[21]), (data_wire[21] ^
 parity_final_wire[20]), (data_wire[20] ^ parity_final_wire[19]), (data_wire[19] ^ parity_final_wire[18]), (data_wire[18] ^ parity_final_wire[17]), (data_wire[17] ^ parity_final_wire[16]), (data_wire[16] ^ parity_final_wire[15]), (data_wire[15] ^ parity_final_wire[14]), (data_wire[14] ^ parity_final_wire[13]), (data_wire[13] ^ parity_final_wire[12]), (data_wire[12] ^ parity_final_wire[11]), (data_wire[11] ^ parity_final_wire[10]), (data_wire[10] ^ parity_final_wire[9]), (data_wire[9] ^ parity_final_wire[8]), (data_wire[8] ^ parity_final_wire[7]), (data_wire[7] ^ parity_final_wire[6]), (data_wire[6] ^ parity_final_wire[5]), (data_wire[5] ^ parity_final_wire[4]), (data_wire[4] ^ parity_final_wire[3]), (data_wire[3] ^ parity_final_wire[2]), (data_wire[2] ^ parity_final_wire[1]), (data_wire[1] ^ parity_final_wire[0]), (data_wire[71] ^ data_wire[0])},
		parity_t = {(parity_t[5] | decode_output[64]), (parity_t[4] | decode_output[32]), (parity_t[3] | decode_output[16]), (parity_t[2] | decode_output[8]), (parity_t[1] | decode_output[4]), (parity_t[0] | decode_output[2]), decode_output[1]},
		q = q_wire,
		q_wire = {wire_mux21_63_dataout, wire_mux21_62_dataout, wire_mux21_61_dataout, wire_mux21_60_dataout, wire_mux21_59_dataout, wire_mux21_58_dataout, wire_mux21_57_dataout, wire_mux21_56_dataout, wire_mux21_55_dataout, wire_mux21_54_dataout, wire_mux21_53_dataout, wire_mux21_52_dataout, wire_mux21_51_dataout, wire_mux21_50_dataout, wire_mux21_49_dataout, wire_mux21_48_dataout, wire_mux21_47_dataout, wire_mux21_46_dataout, wire_mux21_45_dataout, wire_mux21_44_dataout, wire_mux21_43_dataout, wire_mux21_42_dataout, wire_mux21_41_dataout, wire_mux21_40_dataout, wire_mux21_39_dataout, wire_mux21_38_dataout, wire_mux21_37_dataout, wire_mux21_36_dataout, wire_mux21_35_dataout, wire_mux21_34_dataout, wire_mux21_33_dataout, wire_mux21_32_dataout, wire_mux21_31_dataout, wire_mux21_30_dataout, wire_mux21_29_dataout, wire_mux21_28_dataout, wire_mux21_27_dataout, wire_mux21_26_dataout, wire_mux21_25_dataout, wire_mux21_24_dataout, wire_mux21_23_dataout, wire_mux21_22_dataout, wire_mux21_21_dataout, wire_mux21_20_dataout, wire_mux21_19_dataout, wire_mux21_18_dataout, wire_mux21_17_dataout, wire_mux21_16_dataout, wire_mux21_15_dataout, wire_mux21_14_dataout, wire_mux21_13_dataout, wire_mux21_12_dataout, wire_mux21_11_dataout, wire_mux21_10_dataout, wire_mux21_9_dataout, wire_mux21_8_dataout, wire_mux21_7_dataout, wire_mux21_6_dataout, wire_mux21_5_dataout, wire_mux21_4_dataout, wire_mux21_3_dataout, wire_mux21_2_dataout, wire_mux21_1_dataout, wire_mux21_0_dataout},
		syn_bit = syn_t[5],
		syn_e = syndrome[7],
		syn_t = {(syn_t[4] | syndrome[6]), (syn_t[3] | syndrome[5]), (syn_t[2] | syndrome[4]), (syn_t[1] | syndrome[3]), (syn_t[0] | syndrome[2]), (syndrome[0] | syndrome[1])},
		syndrome = {parity_final_wire[70], parity_07_wire[6], parity_06_wire[30], parity_05_wire[1], parity_04_wire[3], parity_03_wire[8], parity_02_wire[17], parity_01_wire[35]};
endmodule 


`ifdef QUESTA_INTEL_OEM
`pragma questa_oem_00 "sfv4CgBD2gRw66FfSic/D/DxyUF4ju6abSGjNZTz+XJ5wNcp1RmzgamT61rscvjMkkNKCYCGE4Hkry++3eL2fSJkmOtrYLQextJ2AFr2kX/6sa63SwNG1Dg8CndZgqHpcPsbI8J/52/6EA/5eQJiUNmwpEDzzugi2WpUBRBy4gGrSJ7A8zUzUrkHlWNSHE1mVOTkuXrL/BUqA6hBwwkS7qZD/J3TRyAu6L9p+9tB0EA73QiLCXgG0VHLIgrnIsEzGR4uJPhEW7R12DXbG11l/OuorSiIync0DJKc15XeAvkK4JvD/rDtt0gtd5NU7X8m9pryrQwQigZkDaPU3B0yNR4NXsQ1p1Jv4tIz4/BZPt9nw9+N7cB3CqfhBZK79r/BFe8xl2iFeeu5KH3AYOLb/CiSChpoSFaDkEXMk3WI5kQ1h7Iz7B6uWJQ+3TLblLgkALdK8UH79idI4I337luG09OzWrvwN/DIYy5IaZmXCx0jrQoSeNkDjZZKQn84tIXqWFYKU0D4vRazHQ0wMXgiKgJdYRVcBpFdlz0TZxwabIOHlyXsjnnjy33lAQCbOF8iyqoM3Ig6Wc7diFGor+qnJk1tDsxSi1pjD+YAdyAbntJnEdvgy6CusJmVnggBdSz6DyPdGUF0DJ797X83yVPXg2LKyEeeTFiJ9ZoOYprD/A4gFa8ud8JTRzkZN9IC5wmAx3iq3rkyMd50fDsjHVv9RIAinrlt/+J4FN+ZdiF2twE9apFvLD1oXaxcFP8cTjj7bvwqtvuk/zUCWZU+bvV2Sea3XFBwCuJ7EXW5qNnHBA3OBFI4ybmMiXWPhsVEmqGGj/z99gO1hnCopTN3d3yHXg4uc+ovMpB9lyfLTv3MoPHnbmZGSEu+mP2Hg9GpW68DZLgTyrTCzp8tay//yT43FU9SCFNz1g566gYpfuU69+u4nwfLvygtdELonmjM6JGRsDRUJs9mD7hLjLaDxJ+c/1IFXDqk2sMAZ0WuNKq8lYRI9jm7yNREB3ced/IVstrz"
`endif