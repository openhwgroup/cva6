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



`timescale 1 ps / 1 ps

module fmiohmc_ecc_pcm_112 (
  
  input  wire [111:0] di,         
  input  wire [7  :0] sb,         
  output wire [7  :0] dout        
  );


wire[111:0] din;

	fmiohmc_ecc_cb #(.DAT(57)) cb0 (.di({di[111],di[110],di[109],di[108],di[107],di[106],di[105],di[104],di[103],di[102],di[101],di[100],di[99],di[98],di[97],di[96],di[95],di[94],di[93],di[92],di[91],di[90],di[89],di[88],di[87],di[86],di[85],di[84],di[83],di[82],di[81],di[80],di[79],di[78],di[77],di[55],di[54],di[53],di[52],di[51],di[50],di[49],di[48],di[47],di[46],di[45],di[44],di[43],di[42],di[41],di[40],di[39],di[38],di[37],di[36],di[35],sb[0]}), .dout(dout[0]));
	fmiohmc_ecc_cb #(.DAT(57)) cb1 (.di({di[111],di[110],di[109],di[108],di[107],di[106],di[105],di[104],di[103],di[102],di[101],di[100],di[99],di[98],di[97],di[96],di[95],di[94],di[93],di[92],di[76],di[75],di[74],di[73],di[72],di[71],di[70],di[69],di[68],di[67],di[66],di[65],di[64],di[63],di[62],di[55],di[54],di[53],di[52],di[51],di[50],di[34],di[33],di[32],di[31],di[30],di[29],di[28],di[27],di[26],di[25],di[24],di[23],di[22],di[21],di[20],sb[1]}), .dout(dout[1]));
	fmiohmc_ecc_cb #(.DAT(57)) cb2 (.di({di[111],di[110],di[109],di[108],di[107],di[106],di[105],di[104],di[103],di[102],di[91],di[90],di[89],di[88],di[87],di[86],di[85],di[84],di[83],di[82],di[76],di[75],di[74],di[73],di[72],di[71],di[70],di[69],di[68],di[67],di[61],di[60],di[59],di[58],di[57],di[55],di[49],di[48],di[47],di[46],di[45],di[34],di[33],di[32],di[31],di[30],di[19],di[18],di[17],di[16],di[15],di[14],di[13],di[12],di[11],di[10],sb[2]}), .dout(dout[2]));
	fmiohmc_ecc_cb #(.DAT(57)) cb3 (.di({di[111],di[110],di[109],di[108],di[101],di[100],di[99],di[98],di[97],di[96],di[91],di[90],di[89],di[88],di[87],di[86],di[81],di[80],di[79],di[78],di[76],di[75],di[74],di[73],di[72],di[71],di[66],di[65],di[64],di[63],di[61],di[60],di[59],di[58],di[56],di[54],di[49],di[44],di[43],di[42],di[41],di[34],di[29],di[28],di[27],di[26],di[19],di[18],di[17],di[16],di[9],di[8],di[7],di[6],di[5],di[4],sb[3]}), .dout(dout[3]));
	fmiohmc_ecc_cb #(.DAT(57)) cb4 (.di({di[111],di[107],di[106],di[105],di[101],di[100],di[99],di[95],di[94],di[93],di[91],di[90],di[89],di[85],di[84],di[83],di[81],di[80],di[79],di[77],di[76],di[75],di[74],di[70],di[69],di[68],di[66],di[65],di[64],di[62],di[61],di[60],di[59],di[57],di[56],di[53],di[48],di[44],di[40],di[39],di[38],di[33],di[29],di[25],di[24],di[23],di[19],di[15],di[14],di[13],di[9],di[8],di[7],di[3],di[2],di[1],sb[4]}), .dout(dout[4]));
	fmiohmc_ecc_cb #(.DAT(57)) cb5 (.di({di[110],di[107],di[104],di[103],di[101],di[98],di[97],di[95],di[94],di[92],di[91],di[88],di[87],di[85],di[84],di[82],di[81],di[80],di[78],di[77],di[76],di[73],di[72],di[70],di[69],di[67],di[66],di[65],di[63],di[62],di[61],di[60],di[58],di[57],di[56],di[52],di[47],di[43],di[40],di[37],di[36],di[32],di[28],di[25],di[22],di[21],di[18],di[15],di[12],di[11],di[9],di[6],di[5],di[3],di[2],di[0],sb[5]}), .dout(dout[5]));
	fmiohmc_ecc_cb #(.DAT(57)) cb6 (.di({di[109],di[106],di[104],di[102],di[100],di[98],di[96],di[95],di[93],di[92],di[90],di[88],di[86],di[85],di[83],di[82],di[81],di[79],di[78],di[77],di[75],di[73],di[71],di[70],di[68],di[67],di[66],di[64],di[63],di[62],di[61],di[59],di[58],di[57],di[56],di[51],di[46],di[42],di[39],di[37],di[35],di[31],di[27],di[24],di[22],di[20],di[17],di[14],di[12],di[10],di[8],di[6],di[4],di[3],di[1],di[0],sb[6]}), .dout(dout[6]));
	fmiohmc_ecc_cb #(.DAT(57)) cb7 (.di({di[108],di[105],di[103],di[102],di[99],di[97],di[96],di[94],di[93],di[92],di[89],di[87],di[86],di[84],di[83],di[82],di[80],di[79],di[78],di[77],di[74],di[72],di[71],di[69],di[68],di[67],di[65],di[64],di[63],di[62],di[60],di[59],di[58],di[57],di[56],di[50],di[45],di[41],di[38],di[36],di[35],di[30],di[26],di[23],di[21],di[20],di[16],di[13],di[11],di[10],di[7],di[5],di[4],di[2],di[1],di[0],sb[7]}), .dout(dout[7]));

endmodule
`ifdef QUESTA_INTEL_OEM
`pragma questa_oem_00 "sfv4CgBD2gRw66FfSic/D/DxyUF4ju6abSGjNZTz+XJ5wNcp1RmzgamT61rscvjMkkNKCYCGE4Hkry++3eL2fSJkmOtrYLQextJ2AFr2kX/6sa63SwNG1Dg8CndZgqHpcPsbI8J/52/6EA/5eQJiUNmwpEDzzugi2WpUBRBy4gGrSJ7A8zUzUrkHlWNSHE1mVOTkuXrL/BUqA6hBwwkS7qZD/J3TRyAu6L9p+9tB0EBDSCNJSFcz15f84e4NsWbz107sdBGcWhLQV0Ft2ZdyzicBVXKFdbjAgBgiw4FypX/1FKdZYcvUJsS+w44c6tGaPCokgPdk0nmquTf1RXp0YHXVIHRHZ9+pFmIXYXbO5V/C5Fk2q3WXkRf3jaCNuBm7vX/CpJkUkUdfpHSx5zbyzPeLkQzdOQJ1ANb6OpMpuzSfmVWoG2ZI/XwpBO+J+UP74QWoxg9iKohMDyz79d6Q+iioHaxQqzA01s6wSIgM+wK9XL+YXchqw4kHBop5XVBV06a6kqMRRm7t8iAR+JgOefKUJv/pxEZsUuU3LHGVe9E39Bk2a07EhN7jmwXqDosDPZ3ErhKwNfALWPdEPGGgSNxgmS0u0WukrYYbVHdwI731W4BjQSwlQHN9Pyz/aFun0IZHuzTZNk1j7fSEWoYLYw/YkrMaPfaueSCcuavM8GMu316u7zeKDpBKgvGc0aI5mOJNO7hY/3DKiC6wBRc+6VStUFjAjUZwZnwjPjtVIv6fuI4mgqjyylZVmYez4zE903nAOjKOJ4CRFmT2y/GOhvzilXpTAqdD2jQsFEP+mDf4HV0iJ3YY1dN/oJpFFToaHz0PyeOI8MjeVO2Azwyiy4a/ZvP6M0Uzayl8WYQnSLXIqpqQsu2CZqQ2yFdZNTH1hD9A0q/hYgjAgRZmqzLQelEqoUfErC95RqHmoABV7WtF+Xt4QNTtOJap34TeewZIFhdSFnrgGyCy7vgmVDQiP6qqzHdgGJoe41RdorXqGi+O6GytViFeONxKLBiLJ84j"
`endif