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


// synthesis_resources = lut 144 
`timescale 1 ps / 1 ps
module  fmiohmc_ecc_decoder_64_decode
	( 
	data,
	eq) /* synthesis synthesis_clearbox=1 */;
	input   [6:0]  data;
	output   [127:0]  eq;
`ifndef ALTERA_RESERVED_QIS
`endif
`ifndef ALTERA_RESERVED_QIS
`endif

	wire  [5:0]  data_wire;
	wire  enable_wire1;
	wire  enable_wire2;
	wire  [127:0]  eq_node;
	wire  [63:0]  eq_wire1;
	wire  [63:0]  eq_wire2;
	wire  [3:0]  w_anode1006w;
	wire  [3:0]  w_anode1018w;
	wire  [3:0]  w_anode1029w;
	wire  [3:0]  w_anode1040w;
	wire  [3:0]  w_anode1050w;
	wire  [3:0]  w_anode1060w;
	wire  [3:0]  w_anode1070w;
	wire  [3:0]  w_anode1080w;
	wire  [3:0]  w_anode1090w;
	wire  [3:0]  w_anode1100w;
	wire  [3:0]  w_anode1111w;
	wire  [3:0]  w_anode1122w;
	wire  [3:0]  w_anode1133w;
	wire  [3:0]  w_anode1143w;
	wire  [3:0]  w_anode1153w;
	wire  [3:0]  w_anode1163w;
	wire  [3:0]  w_anode1173w;
	wire  [3:0]  w_anode1183w;
	wire  [3:0]  w_anode1193w;
	wire  [3:0]  w_anode1204w;
	wire  [3:0]  w_anode1215w;
	wire  [3:0]  w_anode1226w;
	wire  [3:0]  w_anode1236w;
	wire  [3:0]  w_anode1246w;
	wire  [3:0]  w_anode1256w;
	wire  [3:0]  w_anode1266w;
	wire  [3:0]  w_anode1276w;
	wire  [3:0]  w_anode1286w;
	wire  [3:0]  w_anode1297w;
	wire  [3:0]  w_anode1308w;
	wire  [3:0]  w_anode1319w;
	wire  [3:0]  w_anode1329w;
	wire  [3:0]  w_anode1339w;
	wire  [3:0]  w_anode1349w;
	wire  [3:0]  w_anode1359w;
	wire  [3:0]  w_anode1369w;
	wire  [3:0]  w_anode1379w;
	wire  [3:0]  w_anode1390w;
	wire  [3:0]  w_anode1401w;
	wire  [3:0]  w_anode1412w;
	wire  [3:0]  w_anode1422w;
	wire  [3:0]  w_anode1432w;
	wire  [3:0]  w_anode1442w;
	wire  [3:0]  w_anode1452w;
	wire  [3:0]  w_anode1462w;
	wire  [3:0]  w_anode1472w;
	wire  [3:0]  w_anode1483w;
	wire  [3:0]  w_anode1494w;
	wire  [3:0]  w_anode1505w;
	wire  [3:0]  w_anode1515w;
	wire  [3:0]  w_anode1525w;
	wire  [3:0]  w_anode1535w;
	wire  [3:0]  w_anode1545w;
	wire  [3:0]  w_anode1555w;
	wire  [3:0]  w_anode1565w;
	wire  [3:0]  w_anode1576w;
	wire  [3:0]  w_anode1587w;
	wire  [3:0]  w_anode1598w;
	wire  [3:0]  w_anode1608w;
	wire  [3:0]  w_anode1618w;
	wire  [3:0]  w_anode1628w;
	wire  [3:0]  w_anode1638w;
	wire  [3:0]  w_anode1648w;
	wire  [3:0]  w_anode1658w;
	wire  [3:0]  w_anode1670w;
	wire  [3:0]  w_anode1681w;
	wire  [3:0]  w_anode1698w;
	wire  [3:0]  w_anode1708w;
	wire  [3:0]  w_anode1718w;
	wire  [3:0]  w_anode1728w;
	wire  [3:0]  w_anode1738w;
	wire  [3:0]  w_anode1748w;
	wire  [3:0]  w_anode1758w;
	wire  [3:0]  w_anode1770w;
	wire  [3:0]  w_anode1781w;
	wire  [3:0]  w_anode1792w;
	wire  [3:0]  w_anode1802w;
	wire  [3:0]  w_anode1812w;
	wire  [3:0]  w_anode1822w;
	wire  [3:0]  w_anode1832w;
	wire  [3:0]  w_anode1842w;
	wire  [3:0]  w_anode1852w;
	wire  [3:0]  w_anode1863w;
	wire  [3:0]  w_anode1874w;
	wire  [3:0]  w_anode1885w;
	wire  [3:0]  w_anode1895w;
	wire  [3:0]  w_anode1905w;
	wire  [3:0]  w_anode1915w;
	wire  [3:0]  w_anode1925w;
	wire  [3:0]  w_anode1935w;
	wire  [3:0]  w_anode1945w;
	wire  [3:0]  w_anode1956w;
	wire  [3:0]  w_anode1967w;
	wire  [3:0]  w_anode1978w;
	wire  [3:0]  w_anode1988w;
	wire  [3:0]  w_anode1998w;
	wire  [3:0]  w_anode2008w;
	wire  [3:0]  w_anode2018w;
	wire  [3:0]  w_anode2028w;
	wire  [3:0]  w_anode2038w;
	wire  [3:0]  w_anode2049w;
	wire  [3:0]  w_anode2060w;
	wire  [3:0]  w_anode2071w;
	wire  [3:0]  w_anode2081w;
	wire  [3:0]  w_anode2091w;
	wire  [3:0]  w_anode2101w;
	wire  [3:0]  w_anode2111w;
	wire  [3:0]  w_anode2121w;
	wire  [3:0]  w_anode2131w;
	wire  [3:0]  w_anode2142w;
	wire  [3:0]  w_anode2153w;
	wire  [3:0]  w_anode2164w;
	wire  [3:0]  w_anode2174w;
	wire  [3:0]  w_anode2184w;
	wire  [3:0]  w_anode2194w;
	wire  [3:0]  w_anode2204w;
	wire  [3:0]  w_anode2214w;
	wire  [3:0]  w_anode2224w;
	wire  [3:0]  w_anode2235w;
	wire  [3:0]  w_anode2246w;
	wire  [3:0]  w_anode2257w;
	wire  [3:0]  w_anode2267w;
	wire  [3:0]  w_anode2277w;
	wire  [3:0]  w_anode2287w;
	wire  [3:0]  w_anode2297w;
	wire  [3:0]  w_anode2307w;
	wire  [3:0]  w_anode2317w;
	wire  [3:0]  w_anode2328w;
	wire  [3:0]  w_anode2339w;
	wire  [3:0]  w_anode2350w;
	wire  [3:0]  w_anode2360w;
	wire  [3:0]  w_anode2370w;
	wire  [3:0]  w_anode2380w;
	wire  [3:0]  w_anode2390w;
	wire  [3:0]  w_anode2400w;
	wire  [3:0]  w_anode2410w;
	wire  [3:0]  w_anode912w;
	wire  [3:0]  w_anode929w;
	wire  [3:0]  w_anode946w;
	wire  [3:0]  w_anode956w;
	wire  [3:0]  w_anode966w;
	wire  [3:0]  w_anode976w;
	wire  [3:0]  w_anode986w;
	wire  [3:0]  w_anode996w;
	wire  [2:0]  w_data1669w;
	wire  [2:0]  w_data910w;

	assign
		data_wire = data[5:0],
		enable_wire1 = (~ data[6]),
		enable_wire2 = data[6],
		eq = eq_node,
		eq_node = {eq_wire2[63:0], eq_wire1},
		eq_wire1 = {{w_anode1658w[3], w_anode1648w[3], w_anode1638w[3], w_anode1628w[3], w_anode1618w[3], w_anode1608w[3], w_anode1598w[3], w_anode1587w[3]}, {w_anode1565w[3], w_anode1555w[3], w_anode1545w[3], w_anode1535w[3], w_anode1525w[3], w_anode1515w[3], w_anode1505w[3], w_anode1494w[3]}, {w_anode1472w[3], w_anode1462w[3], w_anode1452w[3], w_anode1442w[3], w_anode1432w[3], w_anode1422w[3], w_anode1412w[3], w_anode1401w[3]}, {w_anode1379w[3], w_anode1369w[3], w_anode1359w[3], w_anode1349w[3], w_anode1339w[3], w_anode1329w[3], w_anode1319w[3], w_anode1308w[3]}, {w_anode1286w[3], w_anode1276w[3], w_anode1266w[3], w_anode1256w[3], w_anode1246w[3], w_anode1236w[3], w_anode1226w[3], w_anode1215w[3]}, {w_anode1193w[3], w_anode1183w[3], w_anode1173w[3], w_anode1163w[3], w_anode1153w[3], w_anode1143w[3], w_anode1133w[3], w_anode1122w[3]}, {w_anode1100w[3], w_anode1090w[3], w_anode1080w[3], w_anode1070w[3], w_anode1060w[3], w_anode1050w[3], w_anode1040w[3], w_anode1029w[3]}, {w_anode1006w[3], w_anode996w[3], w_anode986w[3], w_anode976w[3], w_anode966w[3], w_anode956w[3], w_anode946w[3], w_anode929w[3]}},
		eq_wire2 = {{w_anode2410w[3], w_anode2400w[3], w_anode2390w[3], w_anode2380w[3], w_anode2370w[3], w_anode2360w[3], w_anode2350w[3], w_anode2339w[3]}, {w_anode2317w[3], w_anode2307w[3], w_anode2297w[3], w_anode2287w[3], w_anode2277w[3], w_anode2267w[3], w_anode2257w[3], w_anode2246w[3]}, {w_anode2224w[3], w_anode2214w[3], w_anode2204w[3], w_anode2194w[3], w_anode2184w[3], w_anode2174w[3], w_anode2164w[3], w_anode2153w[3]}, {w_anode2131w[3], w_anode2121w[3], w_anode2111w[3], w_anode2101w[3], w_anode2091w[3], w_anode2081w[3], w_anode2071w[3], w_anode2060w[3]}, {w_anode2038w[3], w_anode2028w[3], w_anode2018w[3], w_anode2008w[3], w_anode1998w[3], w_anode1988w[3], w_anode1978w[3], w_anode1967w[3]}, {w_anode1945w[3], w_anode1935w[3], w_anode1925w[3], w_anode1915w[3], w_anode1905w[3], w_anode1895w[3], w_anode1885w[3], w_anode1874w[3]}, {w_anode1852w[3], w_anode1842w[3], w_anode1832w[3], w_anode1822w[3], w_anode1812w[3], w_anode1802w[3], w_anode1792w[3], w_anode1781w[3]}, {w_anode1758w[3], w_anode1748w[3], w_anode1738w[3], w_anode1728w[3], w_anode1718w[3], w_anode1708w[3], w_anode1698w[3], w_anode1681w[3]}},
		w_anode1006w = {(w_anode1006w[2] & w_data910w[2]), (w_anode1006w[1] & w_data910w[1]), (w_anode1006w[0] & w_data910w[0]), w_anode912w[3]},
		w_anode1018w = {(w_anode1018w[2] & (~ data_wire[5])), (w_anode1018w[1] & (~ data_wire[4])), (w_anode1018w[0] & data_wire[3]), enable_wire1},
		w_anode1029w = {(w_anode1029w[2] & (~ w_data910w[2])), (w_anode1029w[1] & (~ w_data910w[1])), (w_anode1029w[0] & (~ w_data910w[0])), w_anode1018w[3]},
		w_anode1040w = {(w_anode1040w[2] & (~ w_data910w[2])), (w_anode1040w[1] & (~ w_data910w[1])), (w_anode1040w[0] & w_data910w[0]), w_anode1018w[3]},
		w_anode1050w = {(w_anode1050w[2] & (~ w_data910w[2])), (w_anode1050w[1] & w_data910w[1]), (w_anode1050w[0] & (~ w_data910w[0])), w_anode1018w[3]},
		w_anode1060w = {(w_anode1060w[2] & (~ w_data910w[2])), (w_anode1060w[1] & w_data910w[1]), (w_anode1060w[0] & w_data910w[0]), w_anode1018w[3]},
		w_anode1070w = {(w_anode1070w[2] & w_data910w[2]), (w_anode1070w[1] & (~ w_data910w[1])), (w_anode1070w[0] & (~ w_data910w[0])), w_anode1018w[3]},
		w_anode1080w = {(w_anode1080w[2] & w_data910w[2]), (w_anode1080w[1] & (~ w_data910w[1])), (w_anode1080w[0] & w_data910w[0]), w_anode1018w[3]},
		w_anode1090w = {(w_anode1090w[2] & w_data910w[2]), (w_anode1090w[1] & w_data910w[1]), (w_anode1090w[0] & (~ w_data910w[0])), w_anode1018w[3]},
		w_anode1100w = {(w_anode1100w[2] & w_data910w[2]), (w_anode1100w[1] & w_data910w[1]), (w_anode1100w[0] & w_data910w[0]), w_anode1018w[3]},
		w_anode1111w = {(w_anode1111w[2] & (~ data_wire[5])), (w_anode1111w[1] & data_wire[4]), (w_anode1111w[0] & (~ data_wire[3])), enable_wire1},
		w_anode1122w = {(w_anode1122w[2] & (~ w_data910w[2])), (w_anode1122w[1] & (~ w_data910w[1])), (w_anode1122w[0] & (~ w_data910w[0])), w_anode1111w[3]},
		w_anode1133w = {(w_anode1133w[2] & (~ w_data910w[2])), (w_anode1133w[1] & (~ w_data910w[1])), (w_anode1133w[0] & w_data910w[0]), w_anode1111w[3]},
		w_anode1143w = {(w_anode1143w[2] & (~ w_data910w[2])), (w_anode1143w[1] & w_data910w[1]), (w_anode1143w[0] & (~ w_data910w[0])), w_anode1111w[3]},
		w_anode1153w = {(w_anode1153w[2] & (~ w_data910w[2])), (w_anode1153w[1] & w_data910w[1]), (w_anode1153w[0] & w_data910w[0]), w_anode1111w[3]},
		w_anode1163w = {(w_anode1163w[2] & w_data910w[2]), (w_anode1163w[1] & (~ w_data910w[1])), (w_anode1163w[0] & (~ w_data910w[0])), w_anode1111w[3]},
		w_anode1173w = {(w_anode1173w[2] & w_data910w[2]), (w_anode1173w[1] & (~ w_data910w[1])), (w_anode1173w[0] & w_data910w[0]), w_anode1111w[3]},
		w_anode1183w = {(w_anode1183w[2] & w_data910w[2]), (w_anode1183w[1] & w_data910w[1]), (w_anode1183w[0] & (~ w_data910w[0])), w_anode1111w[3]},
		w_anode1193w = {(w_anode1193w[2] & w_data910w[2]), (w_anode1193w[1] & w_data910w[1]), (w_anode1193w[0] & w_data910w[0]), w_anode1111w[3]},
		w_anode1204w = {(w_anode1204w[2] & (~ data_wire[5])), (w_anode1204w[1] & data_wire[4]), (w_anode1204w[0] & data_wire[3]), enable_wire1},
		w_anode1215w = {(w_anode1215w[2] & (~ w_data910w[2])), (w_anode1215w[1] & (~ w_data910w[1])), (w_anode1215w[0] & (~ w_data910w[0])), w_anode1204w[3]},
		w_anode1226w = {(w_anode1226w[2] & (~ w_data910w[2])), (w_anode1226w[1] & (~ w_data910w[1])), (w_anode1226w[0] & w_data910w[0]), w_anode1204w[3]},
		w_anode1236w = {(w_anode1236w[2] & (~ w_data910w[2])), (w_anode1236w[1] & w_data910w[1]), (w_anode1236w[0] & (~ w_data910w[0])), w_anode1204w[3]},
		w_anode1246w = {(w_anode1246w[2] & (~ w_data910w[2])), (w_anode1246w[1] & w_data910w[1]), (w_anode1246w[0] & w_data910w[0]), w_anode1204w[3]},
		w_anode1256w = {(w_anode1256w[2] & w_data910w[2]), (w_anode1256w[1] & (~ w_data910w[1])), (w_anode1256w[0] & (~ w_data910w[0])), w_anode1204w[3]},
		w_anode1266w = {(w_anode1266w[2] & w_data910w[2]), (w_anode1266w[1] & (~ w_data910w[1])), (w_anode1266w[0] & w_data910w[0]), w_anode1204w[3]},
		w_anode1276w = {(w_anode1276w[2] & w_data910w[2]), (w_anode1276w[1] & w_data910w[1]), (w_anode1276w[0] & (~ w_data910w[0])), w_anode1204w[3]},
		w_anode1286w = {(w_anode1286w[2] & w_data910w[2]), (w_anode1286w[1] & w_data910w[1]), (w_anode1286w[0] & w_data910w[0]), w_anode1204w[3]},
		w_anode1297w = {(w_anode1297w[2] & data_wire[5]), (w_anode1297w[1] & (~ data_wire[4])), (w_anode1297w[0] & (~ data_wire[3])), enable_wire1},
		w_anode1308w = {(w_anode1308w[2] & (~ w_data910w[2])), (w_anode1308w[1] & (~ w_data910w[1])), (w_anode1308w[0] & (~ w_data910w[0])), w_anode1297w[3]},
		w_anode1319w = {(w_anode1319w[2] & (~ w_data910w[2])), (w_anode1319w[1] & (~ w_data910w[1])), (w_anode1319w[0] & w_data910w[0]), w_anode1297w[3]},
		w_anode1329w = {(w_anode1329w[2] & (~ w_data910w[2])), (w_anode1329w[1] & w_data910w[1]), (w_anode1329w[0] & (~ w_data910w[0])), w_anode1297w[3]},
		w_anode1339w = {(w_anode1339w[2] & (~ w_data910w[2])), (w_anode1339w[1] & w_data910w[1]), (w_anode1339w[0] & w_data910w[0]), w_anode1297w[3]},
		w_anode1349w = {(w_anode1349w[2] & w_data910w[2]), (w_anode1349w[1] & (~ w_data910w[1])), (w_anode1349w[0] & (~ w_data910w[0])), w_anode1297w[3]},
		w_anode1359w = {(w_anode1359w[2] & w_data910w[2]), (w_anode1359w[1] & (~ w_data910w[1])), (w_anode1359w[0] & w_data910w[0]), w_anode1297w[3]},
		w_anode1369w = {(w_anode1369w[2] & w_data910w[2]), (w_anode1369w[1] & w_data910w[1]), (w_anode1369w[0] & (~ w_data910w[0])), w_anode1297w[3]},
		w_anode1379w = {(w_anode1379w[2] & w_data910w[2]), (w_anode1379w[1] & w_data910w[1]), (w_anode1379w[0] & w_data910w[0]), w_anode1297w[3]},
		w_anode1390w = {(w_anode1390w[2] & data_wire[5]), (w_anode1390w[1] & (~ data_wire[4])), (w_anode1390w[0] & data_wire[3]), enable_wire1},
		w_anode1401w = {(w_anode1401w[2] & (~ w_data910w[2])), (w_anode1401w[1] & (~ w_data910w[1])), (w_anode1401w[0] & (~ w_data910w[0])), w_anode1390w[3]},
		w_anode1412w = {(w_anode1412w[2] & (~ w_data910w[2])), (w_anode1412w[1] & (~ w_data910w[1])), (w_anode1412w[0] & w_data910w[0]), w_anode1390w[3]},
		w_anode1422w = {(w_anode1422w[2] & (~ w_data910w[2])), (w_anode1422w[1] & w_data910w[1]), (w_anode1422w[0] & (~ w_data910w[0])), w_anode1390w[3]},
		w_anode1432w = {(w_anode1432w[2] & (~ w_data910w[2])), (w_anode1432w[1] & w_data910w[1]), (w_anode1432w[0] & w_data910w[0]), w_anode1390w[3]},
		w_anode1442w = {(w_anode1442w[2] & w_data910w[2]), (w_anode1442w[1] & (~ w_data910w[1])), (w_anode1442w[0] & (~ w_data910w[0])), w_anode1390w[3]},
		w_anode1452w = {(w_anode1452w[2] & w_data910w[2]), (w_anode1452w[1] & (~ w_data910w[1])), (w_anode1452w[0] & w_data910w[0]), w_anode1390w[3]},
		w_anode1462w = {(w_anode1462w[2] & w_data910w[2]), (w_anode1462w[1] & w_data910w[1]), (w_anode1462w[0] & (~ w_data910w[0])), w_anode1390w[3]},
		w_anode1472w = {(w_anode1472w[2] & w_data910w[2]), (w_anode1472w[1] & w_data910w[1]), (w_anode1472w[0] & w_data910w[0]), w_anode1390w[3]},
		w_anode1483w = {(w_anode1483w[2] & data_wire[5]), (w_anode1483w[1] & data_wire[4]), (w_anode1483w[0] & (~ data_wire[3])), enable_wire1},
		w_anode1494w = {(w_anode1494w[2] & (~ w_data910w[2])), (w_anode1494w[1] & (~ w_data910w[1])), (w_anode1494w[0] & (~ w_data910w[0])), w_anode1483w[3]},
		w_anode1505w = {(w_anode1505w[2] & (~ w_data910w[2])), (w_anode1505w[1] & (~ w_data910w[1])), (w_anode1505w[0] & w_data910w[0]), w_anode1483w[3]},
		w_anode1515w = {(w_anode1515w[2] & (~ w_data910w[2])), (w_anode1515w[1] & w_data910w[1]), (w_anode1515w[0] & (~ w_data910w[0])), w_anode1483w[3]},
		w_anode1525w = {(w_anode1525w[2] & (~ w_data910w[2])), (w_anode1525w[1] & w_data910w[1]), (w_anode1525w[0] & w_data910w[0]), w_anode1483w[3]},
		w_anode1535w = {(w_anode1535w[2] & w_data910w[2]), (w_anode1535w[1] & (~ w_data910w[1])), (w_anode1535w[0] & (~ w_data910w[0])), w_anode1483w[3]},
		w_anode1545w = {(w_anode1545w[2] & w_data910w[2]), (w_anode1545w[1] & (~ w_data910w[1])), (w_anode1545w[0] & w_data910w[0]), w_anode1483w[3]},
		w_anode1555w = {(w_anode1555w[2] & w_data910w[2]), (w_anode1555w[1] & w_data910w[1]), (w_anode1555w[0] & (~ w_data910w[0])), w_anode1483w[3]},
		w_anode1565w = {(w_anode1565w[2] & w_data910w[2]), (w_anode1565w[1] & w_data910w[1]), (w_anode1565w[0] & w_data910w[0]), w_anode1483w[3]},
		w_anode1576w = {(w_anode1576w[2] & data_wire[5]), (w_anode1576w[1] & data_wire[4]), (w_anode1576w[0] & data_wire[3]), enable_wire1},
		w_anode1587w = {(w_anode1587w[2] & (~ w_data910w[2])), (w_anode1587w[1] & (~ w_data910w[1])), (w_anode1587w[0] & (~ w_data910w[0])), w_anode1576w[3]},
		w_anode1598w = {(w_anode1598w[2] & (~ w_data910w[2])), (w_anode1598w[1] & (~ w_data910w[1])), (w_anode1598w[0] & w_data910w[0]), w_anode1576w[3]},
		w_anode1608w = {(w_anode1608w[2] & (~ w_data910w[2])), (w_anode1608w[1] & w_data910w[1]), (w_anode1608w[0] & (~ w_data910w[0])), w_anode1576w[3]},
		w_anode1618w = {(w_anode1618w[2] & (~ w_data910w[2])), (w_anode1618w[1] & w_data910w[1]), (w_anode1618w[0] & w_data910w[0]), w_anode1576w[3]},
		w_anode1628w = {(w_anode1628w[2] & w_data910w[2]), (w_anode1628w[1] & (~ w_data910w[1])), (w_anode1628w[0] & (~ w_data910w[0])), w_anode1576w[3]},
		w_anode1638w = {(w_anode1638w[2] & w_data910w[2]), (w_anode1638w[1] & (~ w_data910w[1])), (w_anode1638w[0] & w_data910w[0]), w_anode1576w[3]},
		w_anode1648w = {(w_anode1648w[2] & w_data910w[2]), (w_anode1648w[1] & w_data910w[1]), (w_anode1648w[0] & (~ w_data910w[0])), w_anode1576w[3]},
		w_anode1658w = {(w_anode1658w[2] & w_data910w[2]), (w_anode1658w[1] & w_data910w[1]), (w_anode1658w[0] & w_data910w[0]), w_anode1576w[3]},
		w_anode1670w = {(w_anode1670w[2] & (~ data_wire[5])), (w_anode1670w[1] & (~ data_wire[4])), (w_anode1670w[0] & (~ data_wire[3])), enable_wire2},
		w_anode1681w = {(w_anode1681w[2] & (~ w_data1669w[2])), (w_anode1681w[1] & (~ w_data1669w[1])), (w_anode1681w[0] & (~ w_data1669w[0])), w_anode1670w[3]},
		w_anode1698w = {(w_anode1698w[2] & (~ w_data1669w[2])), (w_anode1698w[1] & (~ w_data1669w[1])), (w_anode1698w[0] & w_data1669w[0]), w_anode1670w[3]},
		w_anode1708w = {(w_anode1708w[2] & (~ w_data1669w[2])), (w_anode1708w[1] & w_data1669w[1]), (w_anode1708w[0] & (~ w_data1669w[0])), w_anode1670w[3]},
		w_anode1718w = {(w_anode1718w[2] & (~ w_data1669w[2])), (w_anode1718w[1] & w_data1669w[1]), (w_anode1718w[0] & w_data1669w[0]), w_anode1670w[3]},
		w_anode1728w = {(w_anode1728w[2] & w_data1669w[2]), (w_anode1728w[1] & (~ w_data1669w[1])), (w_anode1728w[0] & (~ w_data1669w[0])), w_anode1670w[3]},
		w_anode1738w = {(w_anode1738w[2] & w_data1669w[2]), (w_anode1738w[1] & (~ w_data1669w[1])), (w_anode1738w[0] & w_data1669w[0]), w_anode1670w[3]},
		w_anode1748w = {(w_anode1748w[2] & w_data1669w[2]), (w_anode1748w[1] & w_data1669w[1]), (w_anode1748w[0] & (~ w_data1669w[0])), w_anode1670w[3]},
		w_anode1758w = {(w_anode1758w[2] & w_data1669w[2]), (w_anode1758w[1] & w_data1669w[1]), (w_anode1758w[0] & w_data1669w[0]), w_anode1670w[3]},
		w_anode1770w = {(w_anode1770w[2] & (~ data_wire[5])), (w_anode1770w[1] & (~ data_wire[4])), (w_anode1770w[0] & data_wire[3]), enable_wire2},
		w_anode1781w = {(w_anode1781w[2] & (~ w_data1669w[2])), (w_anode1781w[1] & (~ w_data1669w[1])), (w_anode1781w[0] & (~ w_data1669w[0])), w_anode1770w[3]},
		w_anode1792w = {(w_anode1792w[2] & (~ w_data1669w[2])), (w_anode1792w[1] & (~ w_data1669w[1])), (w_anode1792w[0] & w_data1669w[0]), w_anode1770w[3]},
		w_anode1802w = {(w_anode1802w[2] & (~ w_data1669w[2])), (w_anode1802w[1] & w_data1669w[1]), (w_anode1802w[0] & (~ w_data1669w[0])), w_anode1770w[3]},
		w_anode1812w = {(w_anode1812w[2] & (~ w_data1669w[2])), (w_anode1812w[1] & w_data1669w[1]), (w_anode1812w[0] & w_data1669w[0]), w_anode1770w[3]},
		w_anode1822w = {(w_anode1822w[2] & w_data1669w[2]), (w_anode1822w[1] & (~ w_data1669w[1])), (w_anode1822w[0] & (~ w_data1669w[0])), w_anode1770w[3]},
		w_anode1832w = {(w_anode1832w[2] & w_data1669w[2]), (w_anode1832w[1] & (~ w_data1669w[1])), (w_anode1832w[0] & w_data1669w[0]), w_anode1770w[3]},
		w_anode1842w = {(w_anode1842w[2] & w_data1669w[2]), (w_anode1842w[1] & w_data1669w[1]), (w_anode1842w[0] & (~ w_data1669w[0])), w_anode1770w[3]},
		w_anode1852w = {(w_anode1852w[2] & w_data1669w[2]), (w_anode1852w[1] & w_data1669w[1]), (w_anode1852w[0] & w_data1669w[0]), w_anode1770w[3]},
		w_anode1863w = {(w_anode1863w[2] & (~ data_wire[5])), (w_anode1863w[1] & data_wire[4]), (w_anode1863w[0] & (~ data_wire[3])), enable_wire2},
		w_anode1874w = {(w_anode1874w[2] & (~ w_data1669w[2])), (w_anode1874w[1] & (~ w_data1669w[1])), (w_anode1874w[0] & (~ w_data1669w[0])), w_anode1863w[3]},
		w_anode1885w = {(w_anode1885w[2] & (~ w_data1669w[2])), (w_anode1885w[1] & (~ w_data1669w[1])), (w_anode1885w[0] & w_data1669w[0]), w_anode1863w[3]},
		w_anode1895w = {(w_anode1895w[2] & (~ w_data1669w[2])), (w_anode1895w[1] & w_data1669w[1]), (w_anode1895w[0] & (~ w_data1669w[0])), w_anode1863w[3]},
		w_anode1905w = {(w_anode1905w[2] & (~ w_data1669w[2])), (w_anode1905w[1] & w_data1669w[1]), (w_anode1905w[0] & w_data1669w[0]), w_anode1863w[3]},
		w_anode1915w = {(w_anode1915w[2] & w_data1669w[2]), (w_anode1915w[1] & (~ w_data1669w[1])), (w_anode1915w[0] & (~ w_data1669w[0])), w_anode1863w[3]},
		w_anode1925w = {(w_anode1925w[2] & w_data1669w[2]), (w_anode1925w[1] & (~ w_data1669w[1])), (w_anode1925w[0] & w_data1669w[0]), w_anode1863w[3]},
		w_anode1935w = {(w_anode1935w[2] & w_data1669w[2]), (w_anode1935w[1] & w_data1669w[1]), (w_anode1935w[0] & (~ w_data1669w[0])), w_anode1863w[3]},
		w_anode1945w = {(w_anode1945w[2] & w_data1669w[2]), (w_anode1945w[1] & w_data1669w[1]), (w_anode1945w[0] & w_data1669w[0]), w_anode1863w[3]},
		w_anode1956w = {(w_anode1956w[2] & (~ data_wire[5])), (w_anode1956w[1] & data_wire[4]), (w_anode1956w[0] & data_wire[3]), enable_wire2},
		w_anode1967w = {(w_anode1967w[2] & (~ w_data1669w[2])), (w_anode1967w[1] & (~ w_data1669w[1])), (w_anode1967w[0] & (~ w_data1669w[0])), w_anode1956w[3]},
		w_anode1978w = {(w_anode1978w[2] & (~ w_data1669w[2])), (w_anode1978w[1] & (~ w_data1669w[1])), (w_anode1978w[0] & w_data1669w[0]), w_anode1956w[3]},
		w_anode1988w = {(w_anode1988w[2] & (~ w_data1669w[2])), (w_anode1988w[1] & w_data1669w[1]), (w_anode1988w[0] & (~ w_data1669w[0])), w_anode1956w[3]},
		w_anode1998w = {(w_anode1998w[2] & (~ w_data1669w[2])), (w_anode1998w[1] & w_data1669w[1]), (w_anode1998w[0] & w_data1669w[0]), w_anode1956w[3]},
		w_anode2008w = {(w_anode2008w[2] & w_data1669w[2]), (w_anode2008w[1] & (~ w_data1669w[1])), (w_anode2008w[0] & (~ w_data1669w[0])), w_anode1956w[3]},
		w_anode2018w = {(w_anode2018w[2] & w_data1669w[2]), (w_anode2018w[1] & (~ w_data1669w[1])), (w_anode2018w[0] & w_data1669w[0]), w_anode1956w[3]},
		w_anode2028w = {(w_anode2028w[2] & w_data1669w[2]), (w_anode2028w[1] & w_data1669w[1]), (w_anode2028w[0] & (~ w_data1669w[0])), w_anode1956w[3]},
		w_anode2038w = {(w_anode2038w[2] & w_data1669w[2]), (w_anode2038w[1] & w_data1669w[1]), (w_anode2038w[0] & w_data1669w[0]), w_anode1956w[3]},
		w_anode2049w = {(w_anode2049w[2] & data_wire[5]), (w_anode2049w[1] & (~ data_wire[4])), (w_anode2049w[0] & (~ data_wire[3])), enable_wire2},
		w_anode2060w = {(w_anode2060w[2] & (~ w_data1669w[2])), (w_anode2060w[1] & (~ w_data1669w[1])), (w_anode2060w[0] & (~ w_data1669w[0])), w_anode2049w[3]},
		w_anode2071w = {(w_anode2071w[2] & (~ w_data1669w[2])), (w_anode2071w[1] & (~ w_data1669w[1])), (w_anode2071w[0] & w_data1669w[0]), w_anode2049w[3]},
		w_anode2081w = {(w_anode2081w[2] & (~ w_data1669w[2])), (w_anode2081w[1] & w_data1669w[1]), (w_anode2081w[0] & (~ w_data1669w[0])), w_anode2049w[3]},
		w_anode2091w = {(w_anode2091w[2] & (~ w_data1669w[2])), (w_anode2091w[1] & w_data1669w[1]), (w_anode2091w[0] & w_data1669w[0]), w_anode2049w[3]},
		w_anode2101w = {(w_anode2101w[2] & w_data1669w[2]), (w_anode2101w[1] & (~ w_data1669w[1])), (w_anode2101w[0] & (~ w_data1669w[0])), w_anode2049w[3]},
		w_anode2111w = {(w_anode2111w[2] & w_data1669w[2]), (w_anode2111w[1] & (~ w_data1669w[1])), (w_anode2111w[0] & w_data1669w[0]), w_anode2049w[3]},
		w_anode2121w = {(w_anode2121w[2] & w_data1669w[2]), (w_anode2121w[1] & w_data1669w[1]), (w_anode2121w[0] & (~ w_data1669w[0])), w_anode2049w[3]},
		w_anode2131w = {(w_anode2131w[2] & w_data1669w[2]), (w_anode2131w[1] & w_data1669w[1]), (w_anode2131w[0] & w_data1669w[0]), w_anode2049w[3]},
		w_anode2142w = {(w_anode2142w[2] & data_wire[5]), (w_anode2142w[1] & (~ data_wire[4])), (w_anode2142w[0] & data_wire[3]), enable_wire2},
		w_anode2153w = {(w_anode2153w[2] & (~ w_data1669w[2])), (w_anode2153w[1] & (~ w_data1669w[1])), (w_anode2153w[0] & (~ w_data1669w[0])), w_anode2142w[3]},
		w_anode2164w = {(w_anode2164w[2] & (~ w_data1669w[2])), (w_anode2164w[1] & (~ w_data1669w[1])), (w_anode2164w[0] & w_data1669w[0]), w_anode2142w[3]},
		w_anode2174w = {(w_anode2174w[2] & (~ w_data1669w[2])), (w_anode2174w[1] & w_data1669w[1]), (w_anode2174w[0] & (~ w_data1669w[0])), w_anode2142w[3]},
		w_anode2184w = {(w_anode2184w[2] & (~ w_data1669w[2])), (w_anode2184w[1] & w_data1669w[1]), (w_anode2184w[0] & w_data1669w[0]), w_anode2142w[3]},
		w_anode2194w = {(w_anode2194w[2] & w_data1669w[2]), (w_anode2194w[1] & (~ w_data1669w[1])), (w_anode2194w[0] & (~ w_data1669w[0])), w_anode2142w[3]},
		w_anode2204w = {(w_anode2204w[2] & w_data1669w[2]), (w_anode2204w[1] & (~ w_data1669w[1])), (w_anode2204w[0] & w_data1669w[0]), w_anode2142w[3]},
		w_anode2214w = {(w_anode2214w[2] & w_data1669w[2]), (w_anode2214w[1] & w_data1669w[1]), (w_anode2214w[0] & (~ w_data1669w[0])), w_anode2142w[3]},
		w_anode2224w = {(w_anode2224w[2] & w_data1669w[2]), (w_anode2224w[1] & w_data1669w[1]), (w_anode2224w[0] & w_data1669w[0]), w_anode2142w[3]},
		w_anode2235w = {(w_anode2235w[2] & data_wire[5]), (w_anode2235w[1] & data_wire[4]), (w_anode2235w[0] & (~ data_wire[3])), enable_wire2},
		w_anode2246w = {(w_anode2246w[2] & (~ w_data1669w[2])), (w_anode2246w[1] & (~ w_data1669w[1])), (w_anode2246w[0] & (~ w_data1669w[0])), w_anode2235w[3]},
		w_anode2257w = {(w_anode2257w[2] & (~ w_data1669w[2])), (w_anode2257w[1] & (~ w_data1669w[1])), (w_anode2257w[0] & w_data1669w[0]), w_anode2235w[3]},
		w_anode2267w = {(w_anode2267w[2] & (~ w_data1669w[2])), (w_anode2267w[1] & w_data1669w[1]), (w_anode2267w[0] & (~ w_data1669w[0])), w_anode2235w[3]},
		w_anode2277w = {(w_anode2277w[2] & (~ w_data1669w[2])), (w_anode2277w[1] & w_data1669w[1]), (w_anode2277w[0] & w_data1669w[0]), w_anode2235w[3]},
		w_anode2287w = {(w_anode2287w[2] & w_data1669w[2]), (w_anode2287w[1] & (~ w_data1669w[1])), (w_anode2287w[0] & (~ w_data1669w[0])), w_anode2235w[3]},
		w_anode2297w = {(w_anode2297w[2] & w_data1669w[2]), (w_anode2297w[1] & (~ w_data1669w[1])), (w_anode2297w[0] & w_data1669w[0]), w_anode2235w[3]},
		w_anode2307w = {(w_anode2307w[2] & w_data1669w[2]), (w_anode2307w[1] & w_data1669w[1]), (w_anode2307w[0] & (~ w_data1669w[0])), w_anode2235w[3]},
		w_anode2317w = {(w_anode2317w[2] & w_data1669w[2]), (w_anode2317w[1] & w_data1669w[1]), (w_anode2317w[0] & w_data1669w[0]), w_anode2235w[3]},
		w_anode2328w = {(w_anode2328w[2] & data_wire[5]), (w_anode2328w[1] & data_wire[4]), (w_anode2328w[0] & data_wire[3]), enable_wire2},
		w_anode2339w = {(w_anode2339w[2] & (~ w_data1669w[2])), (w_anode2339w[1] & (~ w_data1669w[1])), (w_anode2339w[0] & (~ w_data1669w[0])), w_anode2328w[3]},
		w_anode2350w = {(w_anode2350w[2] & (~ w_data1669w[2])), (w_anode2350w[1] & (~ w_data1669w[1])), (w_anode2350w[0] & w_data1669w[0]), w_anode2328w[3]},
		w_anode2360w = {(w_anode2360w[2] & (~ w_data1669w[2])), (w_anode2360w[1] & w_data1669w[1]), (w_anode2360w[0] & (~ w_data1669w[0])), w_anode2328w[3]},
		w_anode2370w = {(w_anode2370w[2] & (~ w_data1669w[2])), (w_anode2370w[1] & w_data1669w[1]), (w_anode2370w[0] & w_data1669w[0]), w_anode2328w[3]},
		w_anode2380w = {(w_anode2380w[2] & w_data1669w[2]), (w_anode2380w[1] & (~ w_data1669w[1])), (w_anode2380w[0] & (~ w_data1669w[0])), w_anode2328w[3]},
		w_anode2390w = {(w_anode2390w[2] & w_data1669w[2]), (w_anode2390w[1] & (~ w_data1669w[1])), (w_anode2390w[0] & w_data1669w[0]), w_anode2328w[3]},
		w_anode2400w = {(w_anode2400w[2] & w_data1669w[2]), (w_anode2400w[1] & w_data1669w[1]), (w_anode2400w[0] & (~ w_data1669w[0])), w_anode2328w[3]},
		w_anode2410w = {(w_anode2410w[2] & w_data1669w[2]), (w_anode2410w[1] & w_data1669w[1]), (w_anode2410w[0] & w_data1669w[0]), w_anode2328w[3]},
		w_anode912w = {(w_anode912w[2] & (~ data_wire[5])), (w_anode912w[1] & (~ data_wire[4])), (w_anode912w[0] & (~ data_wire[3])), enable_wire1},
		w_anode929w = {(w_anode929w[2] & (~ w_data910w[2])), (w_anode929w[1] & (~ w_data910w[1])), (w_anode929w[0] & (~ w_data910w[0])), w_anode912w[3]},
		w_anode946w = {(w_anode946w[2] & (~ w_data910w[2])), (w_anode946w[1] & (~ w_data910w[1])), (w_anode946w[0] & w_data910w[0]), w_anode912w[3]},
		w_anode956w = {(w_anode956w[2] & (~ w_data910w[2])), (w_anode956w[1] & w_data910w[1]), (w_anode956w[0] & (~ w_data910w[0])), w_anode912w[3]},
		w_anode966w = {(w_anode966w[2] & (~ w_data910w[2])), (w_anode966w[1] & w_data910w[1]), (w_anode966w[0] & w_data910w[0]), w_anode912w[3]},
		w_anode976w = {(w_anode976w[2] & w_data910w[2]), (w_anode976w[1] & (~ w_data910w[1])), (w_anode976w[0] & (~ w_data910w[0])), w_anode912w[3]},
		w_anode986w = {(w_anode986w[2] & w_data910w[2]), (w_anode986w[1] & (~ w_data910w[1])), (w_anode986w[0] & w_data910w[0]), w_anode912w[3]},
		w_anode996w = {(w_anode996w[2] & w_data910w[2]), (w_anode996w[1] & w_data910w[1]), (w_anode996w[0] & (~ w_data910w[0])), w_anode912w[3]},
		w_data1669w = data_wire[2:0],
		w_data910w = data_wire[2:0];
endmodule 
`ifdef QUESTA_INTEL_OEM
`pragma questa_oem_00 "sfv4CgBD2gRw66FfSic/D/DxyUF4ju6abSGjNZTz+XJ5wNcp1RmzgamT61rscvjMkkNKCYCGE4Hkry++3eL2fSJkmOtrYLQextJ2AFr2kX/6sa63SwNG1Dg8CndZgqHpcPsbI8J/52/6EA/5eQJiUNmwpEDzzugi2WpUBRBy4gGrSJ7A8zUzUrkHlWNSHE1mVOTkuXrL/BUqA6hBwwkS7qZD/J3TRyAu6L9p+9tB0EDQ3V5dS+haV2o+7y3pkcZ84vOnh7eIuMPAAHx2IRU5qV/ure+8eKMDJURDpxTVVVF6EXaMED6dq1DoiAPXdmpFK5YM+6zqv5a29dSzCNtwRFTNA+gmVjFUjXk2WTce/cAihtcfy0Qaxoq2DzNKfJMoo9ZAwL3FgR6EdMW3OAY+o5LRNSgWt6unDPUtdw5YmTbLu1wKNbraH1EaNqhTnH1YviSLcGz+72vN/pmoXrRuwSrrkJiMtu2r8c/v1DYD1neUvRSw2slhTX/Wq4cB8od3bveWltCckWmFSQ9V4k8ECbS9XwYKGhDLFQT8r98+dFI261Z1HvOHGkm4hDPvgdmM1UsW9FJN05dXZffw71hPGNfGbfMPouWr4Dnmz1kMTJVdX30XcqeQyU3SL4HbsA0wrnL8E3S1zDLiUalYjUaT8G0JxoWGVqDEdr1iAh0UMQpNMiqtB/QvtnYi43iqiXUlhN7YnPBl2yIm1idpQVjGOrDGrQorq9cIiLgohD/pR4b1JgHFR5/AfNOkjOhin6b1Y+GBpNdSFm6cVf5xIIYcFzmXopJ5KCqz/XxCKRdnoy++BAMGW2Kkr80teVOb4I4RcSo/e8d3fUjna3kLyuLHx5hzHg5Do81OzM7LSDxJ0SUvHY0L3LXNdIszC7WHGjsmVbUXHq7az0PJwmwz3CMnK9cC0UQXOqMyru0PFyW/IyIA+NQm6+hl6Id7/4RAog4+W7ddt4dK50Mj/ldRdce8nEXeZsBxrgBP3VnyNm2EZtiNipdyBrm9wBGkO0p8MO6s"
`endif