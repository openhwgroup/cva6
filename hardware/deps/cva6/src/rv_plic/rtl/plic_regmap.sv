// Do not edit - auto-generated
module plic_regs (
  input logic [255:0][2:0] prio_i,
  output logic [255:0][2:0] prio_o,
  output logic [255:0] prio_we_o,
  output logic [255:0] prio_re_o,
  input logic [0:0][255:0] ip_i,
  output logic [0:0] ip_re_o,
  input logic [1:0][255:0] ie_i,
  output logic [1:0][255:0] ie_o,
  output logic [1:0] ie_we_o,
  output logic [1:0] ie_re_o,
  input logic [1:0][2:0] threshold_i,
  output logic [1:0][2:0] threshold_o,
  output logic [1:0] threshold_we_o,
  output logic [1:0] threshold_re_o,
  input logic [1:0][7:0] cc_i,
  output logic [1:0][7:0] cc_o,
  output logic [1:0] cc_we_o,
  output logic [1:0] cc_re_o,
  // Bus Interface
  input  reg_intf::reg_intf_req_a32_d32 req_i,
  output reg_intf::reg_intf_resp_d32    resp_o
);
always_comb begin
  resp_o.ready = 1'b1;
  resp_o.rdata = '0;
  resp_o.error = '0;
  prio_o = '0;
  prio_we_o = '0;
  prio_re_o = '0;
  ie_o = '0;
  ie_we_o = '0;
  ie_re_o = '0;
  ip_re_o = '0;   
  threshold_o = '0;
  threshold_we_o = '0;
  threshold_re_o = '0;
  cc_o = '0;
  cc_we_o = '0;
  cc_re_o = '0;
  if (req_i.valid) begin
    if (req_i.write) begin
      unique case(req_i.addr)
        32'hc000000: begin
          prio_o[0][2:0] = req_i.wdata[2:0];
          prio_we_o[0] = 1'b1;
        end
        32'hc000004: begin
          prio_o[1][2:0] = req_i.wdata[2:0];
          prio_we_o[1] = 1'b1;
        end
        32'hc000008: begin
          prio_o[2][2:0] = req_i.wdata[2:0];
          prio_we_o[2] = 1'b1;
        end
        32'hc00000c: begin
          prio_o[3][2:0] = req_i.wdata[2:0];
          prio_we_o[3] = 1'b1;
        end
        32'hc000010: begin
          prio_o[4][2:0] = req_i.wdata[2:0];
          prio_we_o[4] = 1'b1;
        end
        32'hc000014: begin
          prio_o[5][2:0] = req_i.wdata[2:0];
          prio_we_o[5] = 1'b1;
        end
        32'hc000018: begin
          prio_o[6][2:0] = req_i.wdata[2:0];
          prio_we_o[6] = 1'b1;
        end
        32'hc00001c: begin
          prio_o[7][2:0] = req_i.wdata[2:0];
          prio_we_o[7] = 1'b1;
        end
        32'hc000020: begin
          prio_o[8][2:0] = req_i.wdata[2:0];
          prio_we_o[8] = 1'b1;
        end
        32'hc000024: begin
          prio_o[9][2:0] = req_i.wdata[2:0];
          prio_we_o[9] = 1'b1;
        end
        32'hc000028: begin
          prio_o[10][2:0] = req_i.wdata[2:0];
          prio_we_o[10] = 1'b1;
        end
        32'hc00002c: begin
          prio_o[11][2:0] = req_i.wdata[2:0];
          prio_we_o[11] = 1'b1;
        end
        32'hc000030: begin
          prio_o[12][2:0] = req_i.wdata[2:0];
          prio_we_o[12] = 1'b1;
        end
        32'hc000034: begin
          prio_o[13][2:0] = req_i.wdata[2:0];
          prio_we_o[13] = 1'b1;
        end
        32'hc000038: begin
          prio_o[14][2:0] = req_i.wdata[2:0];
          prio_we_o[14] = 1'b1;
        end
        32'hc00003c: begin
          prio_o[15][2:0] = req_i.wdata[2:0];
          prio_we_o[15] = 1'b1;
        end
        32'hc000040: begin
          prio_o[16][2:0] = req_i.wdata[2:0];
          prio_we_o[16] = 1'b1;
        end
        32'hc000044: begin
          prio_o[17][2:0] = req_i.wdata[2:0];
          prio_we_o[17] = 1'b1;
        end
        32'hc000048: begin
          prio_o[18][2:0] = req_i.wdata[2:0];
          prio_we_o[18] = 1'b1;
        end
        32'hc00004c: begin
          prio_o[19][2:0] = req_i.wdata[2:0];
          prio_we_o[19] = 1'b1;
        end
        32'hc000050: begin
          prio_o[20][2:0] = req_i.wdata[2:0];
          prio_we_o[20] = 1'b1;
        end
        32'hc000054: begin
          prio_o[21][2:0] = req_i.wdata[2:0];
          prio_we_o[21] = 1'b1;
        end
        32'hc000058: begin
          prio_o[22][2:0] = req_i.wdata[2:0];
          prio_we_o[22] = 1'b1;
        end
        32'hc00005c: begin
          prio_o[23][2:0] = req_i.wdata[2:0];
          prio_we_o[23] = 1'b1;
        end
        32'hc000060: begin
          prio_o[24][2:0] = req_i.wdata[2:0];
          prio_we_o[24] = 1'b1;
        end
        32'hc000064: begin
          prio_o[25][2:0] = req_i.wdata[2:0];
          prio_we_o[25] = 1'b1;
        end
        32'hc000068: begin
          prio_o[26][2:0] = req_i.wdata[2:0];
          prio_we_o[26] = 1'b1;
        end
        32'hc00006c: begin
          prio_o[27][2:0] = req_i.wdata[2:0];
          prio_we_o[27] = 1'b1;
        end
        32'hc000070: begin
          prio_o[28][2:0] = req_i.wdata[2:0];
          prio_we_o[28] = 1'b1;
        end
        32'hc000074: begin
          prio_o[29][2:0] = req_i.wdata[2:0];
          prio_we_o[29] = 1'b1;
        end
        32'hc000078: begin
          prio_o[30][2:0] = req_i.wdata[2:0];
          prio_we_o[30] = 1'b1;
        end
        32'hc00007c: begin
          prio_o[31][2:0] = req_i.wdata[2:0];
          prio_we_o[31] = 1'b1;
        end
        32'hc000080: begin
          prio_o[32][2:0] = req_i.wdata[2:0];
          prio_we_o[32] = 1'b1;
        end
        32'hc000084: begin
          prio_o[33][2:0] = req_i.wdata[2:0];
          prio_we_o[33] = 1'b1;
        end
        32'hc000088: begin
          prio_o[34][2:0] = req_i.wdata[2:0];
          prio_we_o[34] = 1'b1;
        end
        32'hc00008c: begin
          prio_o[35][2:0] = req_i.wdata[2:0];
          prio_we_o[35] = 1'b1;
        end
        32'hc000090: begin
          prio_o[36][2:0] = req_i.wdata[2:0];
          prio_we_o[36] = 1'b1;
        end
        32'hc000094: begin
          prio_o[37][2:0] = req_i.wdata[2:0];
          prio_we_o[37] = 1'b1;
        end
        32'hc000098: begin
          prio_o[38][2:0] = req_i.wdata[2:0];
          prio_we_o[38] = 1'b1;
        end
        32'hc00009c: begin
          prio_o[39][2:0] = req_i.wdata[2:0];
          prio_we_o[39] = 1'b1;
        end
        32'hc0000a0: begin
          prio_o[40][2:0] = req_i.wdata[2:0];
          prio_we_o[40] = 1'b1;
        end
        32'hc0000a4: begin
          prio_o[41][2:0] = req_i.wdata[2:0];
          prio_we_o[41] = 1'b1;
        end
        32'hc0000a8: begin
          prio_o[42][2:0] = req_i.wdata[2:0];
          prio_we_o[42] = 1'b1;
        end
        32'hc0000ac: begin
          prio_o[43][2:0] = req_i.wdata[2:0];
          prio_we_o[43] = 1'b1;
        end
        32'hc0000b0: begin
          prio_o[44][2:0] = req_i.wdata[2:0];
          prio_we_o[44] = 1'b1;
        end
        32'hc0000b4: begin
          prio_o[45][2:0] = req_i.wdata[2:0];
          prio_we_o[45] = 1'b1;
        end
        32'hc0000b8: begin
          prio_o[46][2:0] = req_i.wdata[2:0];
          prio_we_o[46] = 1'b1;
        end
        32'hc0000bc: begin
          prio_o[47][2:0] = req_i.wdata[2:0];
          prio_we_o[47] = 1'b1;
        end
        32'hc0000c0: begin
          prio_o[48][2:0] = req_i.wdata[2:0];
          prio_we_o[48] = 1'b1;
        end
        32'hc0000c4: begin
          prio_o[49][2:0] = req_i.wdata[2:0];
          prio_we_o[49] = 1'b1;
        end
        32'hc0000c8: begin
          prio_o[50][2:0] = req_i.wdata[2:0];
          prio_we_o[50] = 1'b1;
        end
        32'hc0000cc: begin
          prio_o[51][2:0] = req_i.wdata[2:0];
          prio_we_o[51] = 1'b1;
        end
        32'hc0000d0: begin
          prio_o[52][2:0] = req_i.wdata[2:0];
          prio_we_o[52] = 1'b1;
        end
        32'hc0000d4: begin
          prio_o[53][2:0] = req_i.wdata[2:0];
          prio_we_o[53] = 1'b1;
        end
        32'hc0000d8: begin
          prio_o[54][2:0] = req_i.wdata[2:0];
          prio_we_o[54] = 1'b1;
        end
        32'hc0000dc: begin
          prio_o[55][2:0] = req_i.wdata[2:0];
          prio_we_o[55] = 1'b1;
        end
        32'hc0000e0: begin
          prio_o[56][2:0] = req_i.wdata[2:0];
          prio_we_o[56] = 1'b1;
        end
        32'hc0000e4: begin
          prio_o[57][2:0] = req_i.wdata[2:0];
          prio_we_o[57] = 1'b1;
        end
        32'hc0000e8: begin
          prio_o[58][2:0] = req_i.wdata[2:0];
          prio_we_o[58] = 1'b1;
        end
        32'hc0000ec: begin
          prio_o[59][2:0] = req_i.wdata[2:0];
          prio_we_o[59] = 1'b1;
        end
        32'hc0000f0: begin
          prio_o[60][2:0] = req_i.wdata[2:0];
          prio_we_o[60] = 1'b1;
        end
        32'hc0000f4: begin
          prio_o[61][2:0] = req_i.wdata[2:0];
          prio_we_o[61] = 1'b1;
        end
        32'hc0000f8: begin
          prio_o[62][2:0] = req_i.wdata[2:0];
          prio_we_o[62] = 1'b1;
        end
        32'hc0000fc: begin
          prio_o[63][2:0] = req_i.wdata[2:0];
          prio_we_o[63] = 1'b1;
        end
        32'hc000100: begin
          prio_o[64][2:0] = req_i.wdata[2:0];
          prio_we_o[64] = 1'b1;
        end
        32'hc000104: begin
          prio_o[65][2:0] = req_i.wdata[2:0];
          prio_we_o[65] = 1'b1;
        end
        32'hc000108: begin
          prio_o[66][2:0] = req_i.wdata[2:0];
          prio_we_o[66] = 1'b1;
        end
        32'hc00010c: begin
          prio_o[67][2:0] = req_i.wdata[2:0];
          prio_we_o[67] = 1'b1;
        end
        32'hc000110: begin
          prio_o[68][2:0] = req_i.wdata[2:0];
          prio_we_o[68] = 1'b1;
        end
        32'hc000114: begin
          prio_o[69][2:0] = req_i.wdata[2:0];
          prio_we_o[69] = 1'b1;
        end
        32'hc000118: begin
          prio_o[70][2:0] = req_i.wdata[2:0];
          prio_we_o[70] = 1'b1;
        end
        32'hc00011c: begin
          prio_o[71][2:0] = req_i.wdata[2:0];
          prio_we_o[71] = 1'b1;
        end
        32'hc000120: begin
          prio_o[72][2:0] = req_i.wdata[2:0];
          prio_we_o[72] = 1'b1;
        end
        32'hc000124: begin
          prio_o[73][2:0] = req_i.wdata[2:0];
          prio_we_o[73] = 1'b1;
        end
        32'hc000128: begin
          prio_o[74][2:0] = req_i.wdata[2:0];
          prio_we_o[74] = 1'b1;
        end
        32'hc00012c: begin
          prio_o[75][2:0] = req_i.wdata[2:0];
          prio_we_o[75] = 1'b1;
        end
        32'hc000130: begin
          prio_o[76][2:0] = req_i.wdata[2:0];
          prio_we_o[76] = 1'b1;
        end
        32'hc000134: begin
          prio_o[77][2:0] = req_i.wdata[2:0];
          prio_we_o[77] = 1'b1;
        end
        32'hc000138: begin
          prio_o[78][2:0] = req_i.wdata[2:0];
          prio_we_o[78] = 1'b1;
        end
        32'hc00013c: begin
          prio_o[79][2:0] = req_i.wdata[2:0];
          prio_we_o[79] = 1'b1;
        end
        32'hc000140: begin
          prio_o[80][2:0] = req_i.wdata[2:0];
          prio_we_o[80] = 1'b1;
        end
        32'hc000144: begin
          prio_o[81][2:0] = req_i.wdata[2:0];
          prio_we_o[81] = 1'b1;
        end
        32'hc000148: begin
          prio_o[82][2:0] = req_i.wdata[2:0];
          prio_we_o[82] = 1'b1;
        end
        32'hc00014c: begin
          prio_o[83][2:0] = req_i.wdata[2:0];
          prio_we_o[83] = 1'b1;
        end
        32'hc000150: begin
          prio_o[84][2:0] = req_i.wdata[2:0];
          prio_we_o[84] = 1'b1;
        end
        32'hc000154: begin
          prio_o[85][2:0] = req_i.wdata[2:0];
          prio_we_o[85] = 1'b1;
        end
        32'hc000158: begin
          prio_o[86][2:0] = req_i.wdata[2:0];
          prio_we_o[86] = 1'b1;
        end
        32'hc00015c: begin
          prio_o[87][2:0] = req_i.wdata[2:0];
          prio_we_o[87] = 1'b1;
        end
        32'hc000160: begin
          prio_o[88][2:0] = req_i.wdata[2:0];
          prio_we_o[88] = 1'b1;
        end
        32'hc000164: begin
          prio_o[89][2:0] = req_i.wdata[2:0];
          prio_we_o[89] = 1'b1;
        end
        32'hc000168: begin
          prio_o[90][2:0] = req_i.wdata[2:0];
          prio_we_o[90] = 1'b1;
        end
        32'hc00016c: begin
          prio_o[91][2:0] = req_i.wdata[2:0];
          prio_we_o[91] = 1'b1;
        end
        32'hc000170: begin
          prio_o[92][2:0] = req_i.wdata[2:0];
          prio_we_o[92] = 1'b1;
        end
        32'hc000174: begin
          prio_o[93][2:0] = req_i.wdata[2:0];
          prio_we_o[93] = 1'b1;
        end
        32'hc000178: begin
          prio_o[94][2:0] = req_i.wdata[2:0];
          prio_we_o[94] = 1'b1;
        end
        32'hc00017c: begin
          prio_o[95][2:0] = req_i.wdata[2:0];
          prio_we_o[95] = 1'b1;
        end
        32'hc000180: begin
          prio_o[96][2:0] = req_i.wdata[2:0];
          prio_we_o[96] = 1'b1;
        end
        32'hc000184: begin
          prio_o[97][2:0] = req_i.wdata[2:0];
          prio_we_o[97] = 1'b1;
        end
        32'hc000188: begin
          prio_o[98][2:0] = req_i.wdata[2:0];
          prio_we_o[98] = 1'b1;
        end
        32'hc00018c: begin
          prio_o[99][2:0] = req_i.wdata[2:0];
          prio_we_o[99] = 1'b1;
        end
        32'hc000190: begin
          prio_o[100][2:0] = req_i.wdata[2:0];
          prio_we_o[100] = 1'b1;
        end
        32'hc000194: begin
          prio_o[101][2:0] = req_i.wdata[2:0];
          prio_we_o[101] = 1'b1;
        end
        32'hc000198: begin
          prio_o[102][2:0] = req_i.wdata[2:0];
          prio_we_o[102] = 1'b1;
        end
        32'hc00019c: begin
          prio_o[103][2:0] = req_i.wdata[2:0];
          prio_we_o[103] = 1'b1;
        end
        32'hc0001a0: begin
          prio_o[104][2:0] = req_i.wdata[2:0];
          prio_we_o[104] = 1'b1;
        end
        32'hc0001a4: begin
          prio_o[105][2:0] = req_i.wdata[2:0];
          prio_we_o[105] = 1'b1;
        end
        32'hc0001a8: begin
          prio_o[106][2:0] = req_i.wdata[2:0];
          prio_we_o[106] = 1'b1;
        end
        32'hc0001ac: begin
          prio_o[107][2:0] = req_i.wdata[2:0];
          prio_we_o[107] = 1'b1;
        end
        32'hc0001b0: begin
          prio_o[108][2:0] = req_i.wdata[2:0];
          prio_we_o[108] = 1'b1;
        end
        32'hc0001b4: begin
          prio_o[109][2:0] = req_i.wdata[2:0];
          prio_we_o[109] = 1'b1;
        end
        32'hc0001b8: begin
          prio_o[110][2:0] = req_i.wdata[2:0];
          prio_we_o[110] = 1'b1;
        end
        32'hc0001bc: begin
          prio_o[111][2:0] = req_i.wdata[2:0];
          prio_we_o[111] = 1'b1;
        end
        32'hc0001c0: begin
          prio_o[112][2:0] = req_i.wdata[2:0];
          prio_we_o[112] = 1'b1;
        end
        32'hc0001c4: begin
          prio_o[113][2:0] = req_i.wdata[2:0];
          prio_we_o[113] = 1'b1;
        end
        32'hc0001c8: begin
          prio_o[114][2:0] = req_i.wdata[2:0];
          prio_we_o[114] = 1'b1;
        end
        32'hc0001cc: begin
          prio_o[115][2:0] = req_i.wdata[2:0];
          prio_we_o[115] = 1'b1;
        end
        32'hc0001d0: begin
          prio_o[116][2:0] = req_i.wdata[2:0];
          prio_we_o[116] = 1'b1;
        end
        32'hc0001d4: begin
          prio_o[117][2:0] = req_i.wdata[2:0];
          prio_we_o[117] = 1'b1;
        end
        32'hc0001d8: begin
          prio_o[118][2:0] = req_i.wdata[2:0];
          prio_we_o[118] = 1'b1;
        end
        32'hc0001dc: begin
          prio_o[119][2:0] = req_i.wdata[2:0];
          prio_we_o[119] = 1'b1;
        end
        32'hc0001e0: begin
          prio_o[120][2:0] = req_i.wdata[2:0];
          prio_we_o[120] = 1'b1;
        end
        32'hc0001e4: begin
          prio_o[121][2:0] = req_i.wdata[2:0];
          prio_we_o[121] = 1'b1;
        end
        32'hc0001e8: begin
          prio_o[122][2:0] = req_i.wdata[2:0];
          prio_we_o[122] = 1'b1;
        end
        32'hc0001ec: begin
          prio_o[123][2:0] = req_i.wdata[2:0];
          prio_we_o[123] = 1'b1;
        end
        32'hc0001f0: begin
          prio_o[124][2:0] = req_i.wdata[2:0];
          prio_we_o[124] = 1'b1;
        end
        32'hc0001f4: begin
          prio_o[125][2:0] = req_i.wdata[2:0];
          prio_we_o[125] = 1'b1;
        end
        32'hc0001f8: begin
          prio_o[126][2:0] = req_i.wdata[2:0];
          prio_we_o[126] = 1'b1;
        end
        32'hc0001fc: begin
          prio_o[127][2:0] = req_i.wdata[2:0];
          prio_we_o[127] = 1'b1;
        end
        32'hc000200: begin
          prio_o[128][2:0] = req_i.wdata[2:0];
          prio_we_o[128] = 1'b1;
        end
        32'hc000204: begin
          prio_o[129][2:0] = req_i.wdata[2:0];
          prio_we_o[129] = 1'b1;
        end
        32'hc000208: begin
          prio_o[130][2:0] = req_i.wdata[2:0];
          prio_we_o[130] = 1'b1;
        end
        32'hc00020c: begin
          prio_o[131][2:0] = req_i.wdata[2:0];
          prio_we_o[131] = 1'b1;
        end
        32'hc000210: begin
          prio_o[132][2:0] = req_i.wdata[2:0];
          prio_we_o[132] = 1'b1;
        end
        32'hc000214: begin
          prio_o[133][2:0] = req_i.wdata[2:0];
          prio_we_o[133] = 1'b1;
        end
        32'hc000218: begin
          prio_o[134][2:0] = req_i.wdata[2:0];
          prio_we_o[134] = 1'b1;
        end
        32'hc00021c: begin
          prio_o[135][2:0] = req_i.wdata[2:0];
          prio_we_o[135] = 1'b1;
        end
        32'hc000220: begin
          prio_o[136][2:0] = req_i.wdata[2:0];
          prio_we_o[136] = 1'b1;
        end
        32'hc000224: begin
          prio_o[137][2:0] = req_i.wdata[2:0];
          prio_we_o[137] = 1'b1;
        end
        32'hc000228: begin
          prio_o[138][2:0] = req_i.wdata[2:0];
          prio_we_o[138] = 1'b1;
        end
        32'hc00022c: begin
          prio_o[139][2:0] = req_i.wdata[2:0];
          prio_we_o[139] = 1'b1;
        end
        32'hc000230: begin
          prio_o[140][2:0] = req_i.wdata[2:0];
          prio_we_o[140] = 1'b1;
        end
        32'hc000234: begin
          prio_o[141][2:0] = req_i.wdata[2:0];
          prio_we_o[141] = 1'b1;
        end
        32'hc000238: begin
          prio_o[142][2:0] = req_i.wdata[2:0];
          prio_we_o[142] = 1'b1;
        end
        32'hc00023c: begin
          prio_o[143][2:0] = req_i.wdata[2:0];
          prio_we_o[143] = 1'b1;
        end
        32'hc000240: begin
          prio_o[144][2:0] = req_i.wdata[2:0];
          prio_we_o[144] = 1'b1;
        end
        32'hc000244: begin
          prio_o[145][2:0] = req_i.wdata[2:0];
          prio_we_o[145] = 1'b1;
        end
        32'hc000248: begin
          prio_o[146][2:0] = req_i.wdata[2:0];
          prio_we_o[146] = 1'b1;
        end
        32'hc00024c: begin
          prio_o[147][2:0] = req_i.wdata[2:0];
          prio_we_o[147] = 1'b1;
        end
        32'hc000250: begin
          prio_o[148][2:0] = req_i.wdata[2:0];
          prio_we_o[148] = 1'b1;
        end
        32'hc000254: begin
          prio_o[149][2:0] = req_i.wdata[2:0];
          prio_we_o[149] = 1'b1;
        end
        32'hc000258: begin
          prio_o[150][2:0] = req_i.wdata[2:0];
          prio_we_o[150] = 1'b1;
        end
        32'hc00025c: begin
          prio_o[151][2:0] = req_i.wdata[2:0];
          prio_we_o[151] = 1'b1;
        end
        32'hc000260: begin
          prio_o[152][2:0] = req_i.wdata[2:0];
          prio_we_o[152] = 1'b1;
        end
        32'hc000264: begin
          prio_o[153][2:0] = req_i.wdata[2:0];
          prio_we_o[153] = 1'b1;
        end
        32'hc000268: begin
          prio_o[154][2:0] = req_i.wdata[2:0];
          prio_we_o[154] = 1'b1;
        end
        32'hc00026c: begin
          prio_o[155][2:0] = req_i.wdata[2:0];
          prio_we_o[155] = 1'b1;
        end
        32'hc000270: begin
          prio_o[156][2:0] = req_i.wdata[2:0];
          prio_we_o[156] = 1'b1;
        end
        32'hc000274: begin
          prio_o[157][2:0] = req_i.wdata[2:0];
          prio_we_o[157] = 1'b1;
        end
        32'hc000278: begin
          prio_o[158][2:0] = req_i.wdata[2:0];
          prio_we_o[158] = 1'b1;
        end
        32'hc00027c: begin
          prio_o[159][2:0] = req_i.wdata[2:0];
          prio_we_o[159] = 1'b1;
        end
        32'hc000280: begin
          prio_o[160][2:0] = req_i.wdata[2:0];
          prio_we_o[160] = 1'b1;
        end
        32'hc000284: begin
          prio_o[161][2:0] = req_i.wdata[2:0];
          prio_we_o[161] = 1'b1;
        end
        32'hc000288: begin
          prio_o[162][2:0] = req_i.wdata[2:0];
          prio_we_o[162] = 1'b1;
        end
        32'hc00028c: begin
          prio_o[163][2:0] = req_i.wdata[2:0];
          prio_we_o[163] = 1'b1;
        end
        32'hc000290: begin
          prio_o[164][2:0] = req_i.wdata[2:0];
          prio_we_o[164] = 1'b1;
        end
        32'hc000294: begin
          prio_o[165][2:0] = req_i.wdata[2:0];
          prio_we_o[165] = 1'b1;
        end
        32'hc000298: begin
          prio_o[166][2:0] = req_i.wdata[2:0];
          prio_we_o[166] = 1'b1;
        end
        32'hc00029c: begin
          prio_o[167][2:0] = req_i.wdata[2:0];
          prio_we_o[167] = 1'b1;
        end
        32'hc0002a0: begin
          prio_o[168][2:0] = req_i.wdata[2:0];
          prio_we_o[168] = 1'b1;
        end
        32'hc0002a4: begin
          prio_o[169][2:0] = req_i.wdata[2:0];
          prio_we_o[169] = 1'b1;
        end
        32'hc0002a8: begin
          prio_o[170][2:0] = req_i.wdata[2:0];
          prio_we_o[170] = 1'b1;
        end
        32'hc0002ac: begin
          prio_o[171][2:0] = req_i.wdata[2:0];
          prio_we_o[171] = 1'b1;
        end
        32'hc0002b0: begin
          prio_o[172][2:0] = req_i.wdata[2:0];
          prio_we_o[172] = 1'b1;
        end
        32'hc0002b4: begin
          prio_o[173][2:0] = req_i.wdata[2:0];
          prio_we_o[173] = 1'b1;
        end
        32'hc0002b8: begin
          prio_o[174][2:0] = req_i.wdata[2:0];
          prio_we_o[174] = 1'b1;
        end
        32'hc0002bc: begin
          prio_o[175][2:0] = req_i.wdata[2:0];
          prio_we_o[175] = 1'b1;
        end
        32'hc0002c0: begin
          prio_o[176][2:0] = req_i.wdata[2:0];
          prio_we_o[176] = 1'b1;
        end
        32'hc0002c4: begin
          prio_o[177][2:0] = req_i.wdata[2:0];
          prio_we_o[177] = 1'b1;
        end
        32'hc0002c8: begin
          prio_o[178][2:0] = req_i.wdata[2:0];
          prio_we_o[178] = 1'b1;
        end
        32'hc0002cc: begin
          prio_o[179][2:0] = req_i.wdata[2:0];
          prio_we_o[179] = 1'b1;
        end
        32'hc0002d0: begin
          prio_o[180][2:0] = req_i.wdata[2:0];
          prio_we_o[180] = 1'b1;
        end
        32'hc0002d4: begin
          prio_o[181][2:0] = req_i.wdata[2:0];
          prio_we_o[181] = 1'b1;
        end
        32'hc0002d8: begin
          prio_o[182][2:0] = req_i.wdata[2:0];
          prio_we_o[182] = 1'b1;
        end
        32'hc0002dc: begin
          prio_o[183][2:0] = req_i.wdata[2:0];
          prio_we_o[183] = 1'b1;
        end
        32'hc0002e0: begin
          prio_o[184][2:0] = req_i.wdata[2:0];
          prio_we_o[184] = 1'b1;
        end
        32'hc0002e4: begin
          prio_o[185][2:0] = req_i.wdata[2:0];
          prio_we_o[185] = 1'b1;
        end
        32'hc0002e8: begin
          prio_o[186][2:0] = req_i.wdata[2:0];
          prio_we_o[186] = 1'b1;
        end
        32'hc0002ec: begin
          prio_o[187][2:0] = req_i.wdata[2:0];
          prio_we_o[187] = 1'b1;
        end
        32'hc0002f0: begin
          prio_o[188][2:0] = req_i.wdata[2:0];
          prio_we_o[188] = 1'b1;
        end
        32'hc0002f4: begin
          prio_o[189][2:0] = req_i.wdata[2:0];
          prio_we_o[189] = 1'b1;
        end
        32'hc0002f8: begin
          prio_o[190][2:0] = req_i.wdata[2:0];
          prio_we_o[190] = 1'b1;
        end
        32'hc0002fc: begin
          prio_o[191][2:0] = req_i.wdata[2:0];
          prio_we_o[191] = 1'b1;
        end
        32'hc000300: begin
          prio_o[192][2:0] = req_i.wdata[2:0];
          prio_we_o[192] = 1'b1;
        end
        32'hc000304: begin
          prio_o[193][2:0] = req_i.wdata[2:0];
          prio_we_o[193] = 1'b1;
        end
        32'hc000308: begin
          prio_o[194][2:0] = req_i.wdata[2:0];
          prio_we_o[194] = 1'b1;
        end
        32'hc00030c: begin
          prio_o[195][2:0] = req_i.wdata[2:0];
          prio_we_o[195] = 1'b1;
        end
        32'hc000310: begin
          prio_o[196][2:0] = req_i.wdata[2:0];
          prio_we_o[196] = 1'b1;
        end
        32'hc000314: begin
          prio_o[197][2:0] = req_i.wdata[2:0];
          prio_we_o[197] = 1'b1;
        end
        32'hc000318: begin
          prio_o[198][2:0] = req_i.wdata[2:0];
          prio_we_o[198] = 1'b1;
        end
        32'hc00031c: begin
          prio_o[199][2:0] = req_i.wdata[2:0];
          prio_we_o[199] = 1'b1;
        end
        32'hc000320: begin
          prio_o[200][2:0] = req_i.wdata[2:0];
          prio_we_o[200] = 1'b1;
        end
        32'hc000324: begin
          prio_o[201][2:0] = req_i.wdata[2:0];
          prio_we_o[201] = 1'b1;
        end
        32'hc000328: begin
          prio_o[202][2:0] = req_i.wdata[2:0];
          prio_we_o[202] = 1'b1;
        end
        32'hc00032c: begin
          prio_o[203][2:0] = req_i.wdata[2:0];
          prio_we_o[203] = 1'b1;
        end
        32'hc000330: begin
          prio_o[204][2:0] = req_i.wdata[2:0];
          prio_we_o[204] = 1'b1;
        end
        32'hc000334: begin
          prio_o[205][2:0] = req_i.wdata[2:0];
          prio_we_o[205] = 1'b1;
        end
        32'hc000338: begin
          prio_o[206][2:0] = req_i.wdata[2:0];
          prio_we_o[206] = 1'b1;
        end
        32'hc00033c: begin
          prio_o[207][2:0] = req_i.wdata[2:0];
          prio_we_o[207] = 1'b1;
        end
        32'hc000340: begin
          prio_o[208][2:0] = req_i.wdata[2:0];
          prio_we_o[208] = 1'b1;
        end
        32'hc000344: begin
          prio_o[209][2:0] = req_i.wdata[2:0];
          prio_we_o[209] = 1'b1;
        end
        32'hc000348: begin
          prio_o[210][2:0] = req_i.wdata[2:0];
          prio_we_o[210] = 1'b1;
        end
        32'hc00034c: begin
          prio_o[211][2:0] = req_i.wdata[2:0];
          prio_we_o[211] = 1'b1;
        end
        32'hc000350: begin
          prio_o[212][2:0] = req_i.wdata[2:0];
          prio_we_o[212] = 1'b1;
        end
        32'hc000354: begin
          prio_o[213][2:0] = req_i.wdata[2:0];
          prio_we_o[213] = 1'b1;
        end
        32'hc000358: begin
          prio_o[214][2:0] = req_i.wdata[2:0];
          prio_we_o[214] = 1'b1;
        end
        32'hc00035c: begin
          prio_o[215][2:0] = req_i.wdata[2:0];
          prio_we_o[215] = 1'b1;
        end
        32'hc000360: begin
          prio_o[216][2:0] = req_i.wdata[2:0];
          prio_we_o[216] = 1'b1;
        end
        32'hc000364: begin
          prio_o[217][2:0] = req_i.wdata[2:0];
          prio_we_o[217] = 1'b1;
        end
        32'hc000368: begin
          prio_o[218][2:0] = req_i.wdata[2:0];
          prio_we_o[218] = 1'b1;
        end
        32'hc00036c: begin
          prio_o[219][2:0] = req_i.wdata[2:0];
          prio_we_o[219] = 1'b1;
        end
        32'hc000370: begin
          prio_o[220][2:0] = req_i.wdata[2:0];
          prio_we_o[220] = 1'b1;
        end
        32'hc000374: begin
          prio_o[221][2:0] = req_i.wdata[2:0];
          prio_we_o[221] = 1'b1;
        end
        32'hc000378: begin
          prio_o[222][2:0] = req_i.wdata[2:0];
          prio_we_o[222] = 1'b1;
        end
        32'hc00037c: begin
          prio_o[223][2:0] = req_i.wdata[2:0];
          prio_we_o[223] = 1'b1;
        end
        32'hc000380: begin
          prio_o[224][2:0] = req_i.wdata[2:0];
          prio_we_o[224] = 1'b1;
        end
        32'hc000384: begin
          prio_o[225][2:0] = req_i.wdata[2:0];
          prio_we_o[225] = 1'b1;
        end
        32'hc000388: begin
          prio_o[226][2:0] = req_i.wdata[2:0];
          prio_we_o[226] = 1'b1;
        end
        32'hc00038c: begin
          prio_o[227][2:0] = req_i.wdata[2:0];
          prio_we_o[227] = 1'b1;
        end
        32'hc000390: begin
          prio_o[228][2:0] = req_i.wdata[2:0];
          prio_we_o[228] = 1'b1;
        end
        32'hc000394: begin
          prio_o[229][2:0] = req_i.wdata[2:0];
          prio_we_o[229] = 1'b1;
        end
        32'hc000398: begin
          prio_o[230][2:0] = req_i.wdata[2:0];
          prio_we_o[230] = 1'b1;
        end
        32'hc00039c: begin
          prio_o[231][2:0] = req_i.wdata[2:0];
          prio_we_o[231] = 1'b1;
        end
        32'hc0003a0: begin
          prio_o[232][2:0] = req_i.wdata[2:0];
          prio_we_o[232] = 1'b1;
        end
        32'hc0003a4: begin
          prio_o[233][2:0] = req_i.wdata[2:0];
          prio_we_o[233] = 1'b1;
        end
        32'hc0003a8: begin
          prio_o[234][2:0] = req_i.wdata[2:0];
          prio_we_o[234] = 1'b1;
        end
        32'hc0003ac: begin
          prio_o[235][2:0] = req_i.wdata[2:0];
          prio_we_o[235] = 1'b1;
        end
        32'hc0003b0: begin
          prio_o[236][2:0] = req_i.wdata[2:0];
          prio_we_o[236] = 1'b1;
        end
        32'hc0003b4: begin
          prio_o[237][2:0] = req_i.wdata[2:0];
          prio_we_o[237] = 1'b1;
        end
        32'hc0003b8: begin
          prio_o[238][2:0] = req_i.wdata[2:0];
          prio_we_o[238] = 1'b1;
        end
        32'hc0003bc: begin
          prio_o[239][2:0] = req_i.wdata[2:0];
          prio_we_o[239] = 1'b1;
        end
        32'hc0003c0: begin
          prio_o[240][2:0] = req_i.wdata[2:0];
          prio_we_o[240] = 1'b1;
        end
        32'hc0003c4: begin
          prio_o[241][2:0] = req_i.wdata[2:0];
          prio_we_o[241] = 1'b1;
        end
        32'hc0003c8: begin
          prio_o[242][2:0] = req_i.wdata[2:0];
          prio_we_o[242] = 1'b1;
        end
        32'hc0003cc: begin
          prio_o[243][2:0] = req_i.wdata[2:0];
          prio_we_o[243] = 1'b1;
        end
        32'hc0003d0: begin
          prio_o[244][2:0] = req_i.wdata[2:0];
          prio_we_o[244] = 1'b1;
        end
        32'hc0003d4: begin
          prio_o[245][2:0] = req_i.wdata[2:0];
          prio_we_o[245] = 1'b1;
        end
        32'hc0003d8: begin
          prio_o[246][2:0] = req_i.wdata[2:0];
          prio_we_o[246] = 1'b1;
        end
        32'hc0003dc: begin
          prio_o[247][2:0] = req_i.wdata[2:0];
          prio_we_o[247] = 1'b1;
        end
        32'hc0003e0: begin
          prio_o[248][2:0] = req_i.wdata[2:0];
          prio_we_o[248] = 1'b1;
        end
        32'hc0003e4: begin
          prio_o[249][2:0] = req_i.wdata[2:0];
          prio_we_o[249] = 1'b1;
        end
        32'hc0003e8: begin
          prio_o[250][2:0] = req_i.wdata[2:0];
          prio_we_o[250] = 1'b1;
        end
        32'hc0003ec: begin
          prio_o[251][2:0] = req_i.wdata[2:0];
          prio_we_o[251] = 1'b1;
        end
        32'hc0003f0: begin
          prio_o[252][2:0] = req_i.wdata[2:0];
          prio_we_o[252] = 1'b1;
        end
        32'hc0003f4: begin
          prio_o[253][2:0] = req_i.wdata[2:0];
          prio_we_o[253] = 1'b1;
        end
        32'hc0003f8: begin
          prio_o[254][2:0] = req_i.wdata[2:0];
          prio_we_o[254] = 1'b1;
        end
        32'hc0003fc: begin
          prio_o[255][2:0] = req_i.wdata[2:0];
          prio_we_o[255] = 1'b1;
        end
        32'hc002000: begin
          ie_o[0][31:0] = req_i.wdata[31:0];
          ie_we_o[0] = 1'b1;
        end
        32'hc002004: begin
          ie_o[0][63:32] = req_i.wdata[31:0];
          ie_we_o[0] = 1'b1;
        end
        32'hc002008: begin
          ie_o[0][95:64] = req_i.wdata[31:0];
          ie_we_o[0] = 1'b1;
        end
        32'hc00200c: begin
          ie_o[0][127:96] = req_i.wdata[31:0];
          ie_we_o[0] = 1'b1;
        end
        32'hc002010: begin
          ie_o[0][159:128] = req_i.wdata[31:0];
          ie_we_o[0] = 1'b1;
        end
        32'hc002014: begin
          ie_o[0][191:160] = req_i.wdata[31:0];
          ie_we_o[0] = 1'b1;
        end
        32'hc002018: begin
          ie_o[0][223:192] = req_i.wdata[31:0];
          ie_we_o[0] = 1'b1;
        end
        32'hc00201c: begin
          ie_o[0][255:224] = req_i.wdata[31:0];
          ie_we_o[0] = 1'b1;
        end
        32'hc002080: begin
          ie_o[1][31:0] = req_i.wdata[31:0];
          ie_we_o[1] = 1'b1;
        end
        32'hc002084: begin
          ie_o[1][63:32] = req_i.wdata[31:0];
          ie_we_o[1] = 1'b1;
        end
        32'hc002088: begin
          ie_o[1][95:64] = req_i.wdata[31:0];
          ie_we_o[1] = 1'b1;
        end
        32'hc00208c: begin
          ie_o[1][127:96] = req_i.wdata[31:0];
          ie_we_o[1] = 1'b1;
        end
        32'hc002090: begin
          ie_o[1][159:128] = req_i.wdata[31:0];
          ie_we_o[1] = 1'b1;
        end
        32'hc002094: begin
          ie_o[1][191:160] = req_i.wdata[31:0];
          ie_we_o[1] = 1'b1;
        end
        32'hc002098: begin
          ie_o[1][223:192] = req_i.wdata[31:0];
          ie_we_o[1] = 1'b1;
        end
        32'hc00209c: begin
          ie_o[1][255:224] = req_i.wdata[31:0];
          ie_we_o[1] = 1'b1;
        end
        32'hc200000: begin
          threshold_o[0][2:0] = req_i.wdata[2:0];
          threshold_we_o[0] = 1'b1;
        end
        32'hc201000: begin
          threshold_o[1][2:0] = req_i.wdata[2:0];
          threshold_we_o[1] = 1'b1;
        end
        32'hc200004: begin
          cc_o[0][7:0] = req_i.wdata[7:0];
          cc_we_o[0] = 1'b1;
        end
        32'hc201004: begin
          cc_o[1][7:0] = req_i.wdata[7:0];
          cc_we_o[1] = 1'b1;
        end
        default: resp_o.error = 1'b1;
      endcase
    end else begin
      unique case(req_i.addr)
        32'hc000000: begin
          resp_o.rdata[2:0] = prio_i[0][2:0];
          prio_re_o[0] = 1'b1;
        end
        32'hc000004: begin
          resp_o.rdata[2:0] = prio_i[1][2:0];
          prio_re_o[1] = 1'b1;
        end
        32'hc000008: begin
          resp_o.rdata[2:0] = prio_i[2][2:0];
          prio_re_o[2] = 1'b1;
        end
        32'hc00000c: begin
          resp_o.rdata[2:0] = prio_i[3][2:0];
          prio_re_o[3] = 1'b1;
        end
        32'hc000010: begin
          resp_o.rdata[2:0] = prio_i[4][2:0];
          prio_re_o[4] = 1'b1;
        end
        32'hc000014: begin
          resp_o.rdata[2:0] = prio_i[5][2:0];
          prio_re_o[5] = 1'b1;
        end
        32'hc000018: begin
          resp_o.rdata[2:0] = prio_i[6][2:0];
          prio_re_o[6] = 1'b1;
        end
        32'hc00001c: begin
          resp_o.rdata[2:0] = prio_i[7][2:0];
          prio_re_o[7] = 1'b1;
        end
        32'hc000020: begin
          resp_o.rdata[2:0] = prio_i[8][2:0];
          prio_re_o[8] = 1'b1;
        end
        32'hc000024: begin
          resp_o.rdata[2:0] = prio_i[9][2:0];
          prio_re_o[9] = 1'b1;
        end
        32'hc000028: begin
          resp_o.rdata[2:0] = prio_i[10][2:0];
          prio_re_o[10] = 1'b1;
        end
        32'hc00002c: begin
          resp_o.rdata[2:0] = prio_i[11][2:0];
          prio_re_o[11] = 1'b1;
        end
        32'hc000030: begin
          resp_o.rdata[2:0] = prio_i[12][2:0];
          prio_re_o[12] = 1'b1;
        end
        32'hc000034: begin
          resp_o.rdata[2:0] = prio_i[13][2:0];
          prio_re_o[13] = 1'b1;
        end
        32'hc000038: begin
          resp_o.rdata[2:0] = prio_i[14][2:0];
          prio_re_o[14] = 1'b1;
        end
        32'hc00003c: begin
          resp_o.rdata[2:0] = prio_i[15][2:0];
          prio_re_o[15] = 1'b1;
        end
        32'hc000040: begin
          resp_o.rdata[2:0] = prio_i[16][2:0];
          prio_re_o[16] = 1'b1;
        end
        32'hc000044: begin
          resp_o.rdata[2:0] = prio_i[17][2:0];
          prio_re_o[17] = 1'b1;
        end
        32'hc000048: begin
          resp_o.rdata[2:0] = prio_i[18][2:0];
          prio_re_o[18] = 1'b1;
        end
        32'hc00004c: begin
          resp_o.rdata[2:0] = prio_i[19][2:0];
          prio_re_o[19] = 1'b1;
        end
        32'hc000050: begin
          resp_o.rdata[2:0] = prio_i[20][2:0];
          prio_re_o[20] = 1'b1;
        end
        32'hc000054: begin
          resp_o.rdata[2:0] = prio_i[21][2:0];
          prio_re_o[21] = 1'b1;
        end
        32'hc000058: begin
          resp_o.rdata[2:0] = prio_i[22][2:0];
          prio_re_o[22] = 1'b1;
        end
        32'hc00005c: begin
          resp_o.rdata[2:0] = prio_i[23][2:0];
          prio_re_o[23] = 1'b1;
        end
        32'hc000060: begin
          resp_o.rdata[2:0] = prio_i[24][2:0];
          prio_re_o[24] = 1'b1;
        end
        32'hc000064: begin
          resp_o.rdata[2:0] = prio_i[25][2:0];
          prio_re_o[25] = 1'b1;
        end
        32'hc000068: begin
          resp_o.rdata[2:0] = prio_i[26][2:0];
          prio_re_o[26] = 1'b1;
        end
        32'hc00006c: begin
          resp_o.rdata[2:0] = prio_i[27][2:0];
          prio_re_o[27] = 1'b1;
        end
        32'hc000070: begin
          resp_o.rdata[2:0] = prio_i[28][2:0];
          prio_re_o[28] = 1'b1;
        end
        32'hc000074: begin
          resp_o.rdata[2:0] = prio_i[29][2:0];
          prio_re_o[29] = 1'b1;
        end
        32'hc000078: begin
          resp_o.rdata[2:0] = prio_i[30][2:0];
          prio_re_o[30] = 1'b1;
        end
        32'hc00007c: begin
          resp_o.rdata[2:0] = prio_i[31][2:0];
          prio_re_o[31] = 1'b1;
        end
        32'hc000080: begin
          resp_o.rdata[2:0] = prio_i[32][2:0];
          prio_re_o[32] = 1'b1;
        end
        32'hc000084: begin
          resp_o.rdata[2:0] = prio_i[33][2:0];
          prio_re_o[33] = 1'b1;
        end
        32'hc000088: begin
          resp_o.rdata[2:0] = prio_i[34][2:0];
          prio_re_o[34] = 1'b1;
        end
        32'hc00008c: begin
          resp_o.rdata[2:0] = prio_i[35][2:0];
          prio_re_o[35] = 1'b1;
        end
        32'hc000090: begin
          resp_o.rdata[2:0] = prio_i[36][2:0];
          prio_re_o[36] = 1'b1;
        end
        32'hc000094: begin
          resp_o.rdata[2:0] = prio_i[37][2:0];
          prio_re_o[37] = 1'b1;
        end
        32'hc000098: begin
          resp_o.rdata[2:0] = prio_i[38][2:0];
          prio_re_o[38] = 1'b1;
        end
        32'hc00009c: begin
          resp_o.rdata[2:0] = prio_i[39][2:0];
          prio_re_o[39] = 1'b1;
        end
        32'hc0000a0: begin
          resp_o.rdata[2:0] = prio_i[40][2:0];
          prio_re_o[40] = 1'b1;
        end
        32'hc0000a4: begin
          resp_o.rdata[2:0] = prio_i[41][2:0];
          prio_re_o[41] = 1'b1;
        end
        32'hc0000a8: begin
          resp_o.rdata[2:0] = prio_i[42][2:0];
          prio_re_o[42] = 1'b1;
        end
        32'hc0000ac: begin
          resp_o.rdata[2:0] = prio_i[43][2:0];
          prio_re_o[43] = 1'b1;
        end
        32'hc0000b0: begin
          resp_o.rdata[2:0] = prio_i[44][2:0];
          prio_re_o[44] = 1'b1;
        end
        32'hc0000b4: begin
          resp_o.rdata[2:0] = prio_i[45][2:0];
          prio_re_o[45] = 1'b1;
        end
        32'hc0000b8: begin
          resp_o.rdata[2:0] = prio_i[46][2:0];
          prio_re_o[46] = 1'b1;
        end
        32'hc0000bc: begin
          resp_o.rdata[2:0] = prio_i[47][2:0];
          prio_re_o[47] = 1'b1;
        end
        32'hc0000c0: begin
          resp_o.rdata[2:0] = prio_i[48][2:0];
          prio_re_o[48] = 1'b1;
        end
        32'hc0000c4: begin
          resp_o.rdata[2:0] = prio_i[49][2:0];
          prio_re_o[49] = 1'b1;
        end
        32'hc0000c8: begin
          resp_o.rdata[2:0] = prio_i[50][2:0];
          prio_re_o[50] = 1'b1;
        end
        32'hc0000cc: begin
          resp_o.rdata[2:0] = prio_i[51][2:0];
          prio_re_o[51] = 1'b1;
        end
        32'hc0000d0: begin
          resp_o.rdata[2:0] = prio_i[52][2:0];
          prio_re_o[52] = 1'b1;
        end
        32'hc0000d4: begin
          resp_o.rdata[2:0] = prio_i[53][2:0];
          prio_re_o[53] = 1'b1;
        end
        32'hc0000d8: begin
          resp_o.rdata[2:0] = prio_i[54][2:0];
          prio_re_o[54] = 1'b1;
        end
        32'hc0000dc: begin
          resp_o.rdata[2:0] = prio_i[55][2:0];
          prio_re_o[55] = 1'b1;
        end
        32'hc0000e0: begin
          resp_o.rdata[2:0] = prio_i[56][2:0];
          prio_re_o[56] = 1'b1;
        end
        32'hc0000e4: begin
          resp_o.rdata[2:0] = prio_i[57][2:0];
          prio_re_o[57] = 1'b1;
        end
        32'hc0000e8: begin
          resp_o.rdata[2:0] = prio_i[58][2:0];
          prio_re_o[58] = 1'b1;
        end
        32'hc0000ec: begin
          resp_o.rdata[2:0] = prio_i[59][2:0];
          prio_re_o[59] = 1'b1;
        end
        32'hc0000f0: begin
          resp_o.rdata[2:0] = prio_i[60][2:0];
          prio_re_o[60] = 1'b1;
        end
        32'hc0000f4: begin
          resp_o.rdata[2:0] = prio_i[61][2:0];
          prio_re_o[61] = 1'b1;
        end
        32'hc0000f8: begin
          resp_o.rdata[2:0] = prio_i[62][2:0];
          prio_re_o[62] = 1'b1;
        end
        32'hc0000fc: begin
          resp_o.rdata[2:0] = prio_i[63][2:0];
          prio_re_o[63] = 1'b1;
        end
        32'hc000100: begin
          resp_o.rdata[2:0] = prio_i[64][2:0];
          prio_re_o[64] = 1'b1;
        end
        32'hc000104: begin
          resp_o.rdata[2:0] = prio_i[65][2:0];
          prio_re_o[65] = 1'b1;
        end
        32'hc000108: begin
          resp_o.rdata[2:0] = prio_i[66][2:0];
          prio_re_o[66] = 1'b1;
        end
        32'hc00010c: begin
          resp_o.rdata[2:0] = prio_i[67][2:0];
          prio_re_o[67] = 1'b1;
        end
        32'hc000110: begin
          resp_o.rdata[2:0] = prio_i[68][2:0];
          prio_re_o[68] = 1'b1;
        end
        32'hc000114: begin
          resp_o.rdata[2:0] = prio_i[69][2:0];
          prio_re_o[69] = 1'b1;
        end
        32'hc000118: begin
          resp_o.rdata[2:0] = prio_i[70][2:0];
          prio_re_o[70] = 1'b1;
        end
        32'hc00011c: begin
          resp_o.rdata[2:0] = prio_i[71][2:0];
          prio_re_o[71] = 1'b1;
        end
        32'hc000120: begin
          resp_o.rdata[2:0] = prio_i[72][2:0];
          prio_re_o[72] = 1'b1;
        end
        32'hc000124: begin
          resp_o.rdata[2:0] = prio_i[73][2:0];
          prio_re_o[73] = 1'b1;
        end
        32'hc000128: begin
          resp_o.rdata[2:0] = prio_i[74][2:0];
          prio_re_o[74] = 1'b1;
        end
        32'hc00012c: begin
          resp_o.rdata[2:0] = prio_i[75][2:0];
          prio_re_o[75] = 1'b1;
        end
        32'hc000130: begin
          resp_o.rdata[2:0] = prio_i[76][2:0];
          prio_re_o[76] = 1'b1;
        end
        32'hc000134: begin
          resp_o.rdata[2:0] = prio_i[77][2:0];
          prio_re_o[77] = 1'b1;
        end
        32'hc000138: begin
          resp_o.rdata[2:0] = prio_i[78][2:0];
          prio_re_o[78] = 1'b1;
        end
        32'hc00013c: begin
          resp_o.rdata[2:0] = prio_i[79][2:0];
          prio_re_o[79] = 1'b1;
        end
        32'hc000140: begin
          resp_o.rdata[2:0] = prio_i[80][2:0];
          prio_re_o[80] = 1'b1;
        end
        32'hc000144: begin
          resp_o.rdata[2:0] = prio_i[81][2:0];
          prio_re_o[81] = 1'b1;
        end
        32'hc000148: begin
          resp_o.rdata[2:0] = prio_i[82][2:0];
          prio_re_o[82] = 1'b1;
        end
        32'hc00014c: begin
          resp_o.rdata[2:0] = prio_i[83][2:0];
          prio_re_o[83] = 1'b1;
        end
        32'hc000150: begin
          resp_o.rdata[2:0] = prio_i[84][2:0];
          prio_re_o[84] = 1'b1;
        end
        32'hc000154: begin
          resp_o.rdata[2:0] = prio_i[85][2:0];
          prio_re_o[85] = 1'b1;
        end
        32'hc000158: begin
          resp_o.rdata[2:0] = prio_i[86][2:0];
          prio_re_o[86] = 1'b1;
        end
        32'hc00015c: begin
          resp_o.rdata[2:0] = prio_i[87][2:0];
          prio_re_o[87] = 1'b1;
        end
        32'hc000160: begin
          resp_o.rdata[2:0] = prio_i[88][2:0];
          prio_re_o[88] = 1'b1;
        end
        32'hc000164: begin
          resp_o.rdata[2:0] = prio_i[89][2:0];
          prio_re_o[89] = 1'b1;
        end
        32'hc000168: begin
          resp_o.rdata[2:0] = prio_i[90][2:0];
          prio_re_o[90] = 1'b1;
        end
        32'hc00016c: begin
          resp_o.rdata[2:0] = prio_i[91][2:0];
          prio_re_o[91] = 1'b1;
        end
        32'hc000170: begin
          resp_o.rdata[2:0] = prio_i[92][2:0];
          prio_re_o[92] = 1'b1;
        end
        32'hc000174: begin
          resp_o.rdata[2:0] = prio_i[93][2:0];
          prio_re_o[93] = 1'b1;
        end
        32'hc000178: begin
          resp_o.rdata[2:0] = prio_i[94][2:0];
          prio_re_o[94] = 1'b1;
        end
        32'hc00017c: begin
          resp_o.rdata[2:0] = prio_i[95][2:0];
          prio_re_o[95] = 1'b1;
        end
        32'hc000180: begin
          resp_o.rdata[2:0] = prio_i[96][2:0];
          prio_re_o[96] = 1'b1;
        end
        32'hc000184: begin
          resp_o.rdata[2:0] = prio_i[97][2:0];
          prio_re_o[97] = 1'b1;
        end
        32'hc000188: begin
          resp_o.rdata[2:0] = prio_i[98][2:0];
          prio_re_o[98] = 1'b1;
        end
        32'hc00018c: begin
          resp_o.rdata[2:0] = prio_i[99][2:0];
          prio_re_o[99] = 1'b1;
        end
        32'hc000190: begin
          resp_o.rdata[2:0] = prio_i[100][2:0];
          prio_re_o[100] = 1'b1;
        end
        32'hc000194: begin
          resp_o.rdata[2:0] = prio_i[101][2:0];
          prio_re_o[101] = 1'b1;
        end
        32'hc000198: begin
          resp_o.rdata[2:0] = prio_i[102][2:0];
          prio_re_o[102] = 1'b1;
        end
        32'hc00019c: begin
          resp_o.rdata[2:0] = prio_i[103][2:0];
          prio_re_o[103] = 1'b1;
        end
        32'hc0001a0: begin
          resp_o.rdata[2:0] = prio_i[104][2:0];
          prio_re_o[104] = 1'b1;
        end
        32'hc0001a4: begin
          resp_o.rdata[2:0] = prio_i[105][2:0];
          prio_re_o[105] = 1'b1;
        end
        32'hc0001a8: begin
          resp_o.rdata[2:0] = prio_i[106][2:0];
          prio_re_o[106] = 1'b1;
        end
        32'hc0001ac: begin
          resp_o.rdata[2:0] = prio_i[107][2:0];
          prio_re_o[107] = 1'b1;
        end
        32'hc0001b0: begin
          resp_o.rdata[2:0] = prio_i[108][2:0];
          prio_re_o[108] = 1'b1;
        end
        32'hc0001b4: begin
          resp_o.rdata[2:0] = prio_i[109][2:0];
          prio_re_o[109] = 1'b1;
        end
        32'hc0001b8: begin
          resp_o.rdata[2:0] = prio_i[110][2:0];
          prio_re_o[110] = 1'b1;
        end
        32'hc0001bc: begin
          resp_o.rdata[2:0] = prio_i[111][2:0];
          prio_re_o[111] = 1'b1;
        end
        32'hc0001c0: begin
          resp_o.rdata[2:0] = prio_i[112][2:0];
          prio_re_o[112] = 1'b1;
        end
        32'hc0001c4: begin
          resp_o.rdata[2:0] = prio_i[113][2:0];
          prio_re_o[113] = 1'b1;
        end
        32'hc0001c8: begin
          resp_o.rdata[2:0] = prio_i[114][2:0];
          prio_re_o[114] = 1'b1;
        end
        32'hc0001cc: begin
          resp_o.rdata[2:0] = prio_i[115][2:0];
          prio_re_o[115] = 1'b1;
        end
        32'hc0001d0: begin
          resp_o.rdata[2:0] = prio_i[116][2:0];
          prio_re_o[116] = 1'b1;
        end
        32'hc0001d4: begin
          resp_o.rdata[2:0] = prio_i[117][2:0];
          prio_re_o[117] = 1'b1;
        end
        32'hc0001d8: begin
          resp_o.rdata[2:0] = prio_i[118][2:0];
          prio_re_o[118] = 1'b1;
        end
        32'hc0001dc: begin
          resp_o.rdata[2:0] = prio_i[119][2:0];
          prio_re_o[119] = 1'b1;
        end
        32'hc0001e0: begin
          resp_o.rdata[2:0] = prio_i[120][2:0];
          prio_re_o[120] = 1'b1;
        end
        32'hc0001e4: begin
          resp_o.rdata[2:0] = prio_i[121][2:0];
          prio_re_o[121] = 1'b1;
        end
        32'hc0001e8: begin
          resp_o.rdata[2:0] = prio_i[122][2:0];
          prio_re_o[122] = 1'b1;
        end
        32'hc0001ec: begin
          resp_o.rdata[2:0] = prio_i[123][2:0];
          prio_re_o[123] = 1'b1;
        end
        32'hc0001f0: begin
          resp_o.rdata[2:0] = prio_i[124][2:0];
          prio_re_o[124] = 1'b1;
        end
        32'hc0001f4: begin
          resp_o.rdata[2:0] = prio_i[125][2:0];
          prio_re_o[125] = 1'b1;
        end
        32'hc0001f8: begin
          resp_o.rdata[2:0] = prio_i[126][2:0];
          prio_re_o[126] = 1'b1;
        end
        32'hc0001fc: begin
          resp_o.rdata[2:0] = prio_i[127][2:0];
          prio_re_o[127] = 1'b1;
        end
        32'hc000200: begin
          resp_o.rdata[2:0] = prio_i[128][2:0];
          prio_re_o[128] = 1'b1;
        end
        32'hc000204: begin
          resp_o.rdata[2:0] = prio_i[129][2:0];
          prio_re_o[129] = 1'b1;
        end
        32'hc000208: begin
          resp_o.rdata[2:0] = prio_i[130][2:0];
          prio_re_o[130] = 1'b1;
        end
        32'hc00020c: begin
          resp_o.rdata[2:0] = prio_i[131][2:0];
          prio_re_o[131] = 1'b1;
        end
        32'hc000210: begin
          resp_o.rdata[2:0] = prio_i[132][2:0];
          prio_re_o[132] = 1'b1;
        end
        32'hc000214: begin
          resp_o.rdata[2:0] = prio_i[133][2:0];
          prio_re_o[133] = 1'b1;
        end
        32'hc000218: begin
          resp_o.rdata[2:0] = prio_i[134][2:0];
          prio_re_o[134] = 1'b1;
        end
        32'hc00021c: begin
          resp_o.rdata[2:0] = prio_i[135][2:0];
          prio_re_o[135] = 1'b1;
        end
        32'hc000220: begin
          resp_o.rdata[2:0] = prio_i[136][2:0];
          prio_re_o[136] = 1'b1;
        end
        32'hc000224: begin
          resp_o.rdata[2:0] = prio_i[137][2:0];
          prio_re_o[137] = 1'b1;
        end
        32'hc000228: begin
          resp_o.rdata[2:0] = prio_i[138][2:0];
          prio_re_o[138] = 1'b1;
        end
        32'hc00022c: begin
          resp_o.rdata[2:0] = prio_i[139][2:0];
          prio_re_o[139] = 1'b1;
        end
        32'hc000230: begin
          resp_o.rdata[2:0] = prio_i[140][2:0];
          prio_re_o[140] = 1'b1;
        end
        32'hc000234: begin
          resp_o.rdata[2:0] = prio_i[141][2:0];
          prio_re_o[141] = 1'b1;
        end
        32'hc000238: begin
          resp_o.rdata[2:0] = prio_i[142][2:0];
          prio_re_o[142] = 1'b1;
        end
        32'hc00023c: begin
          resp_o.rdata[2:0] = prio_i[143][2:0];
          prio_re_o[143] = 1'b1;
        end
        32'hc000240: begin
          resp_o.rdata[2:0] = prio_i[144][2:0];
          prio_re_o[144] = 1'b1;
        end
        32'hc000244: begin
          resp_o.rdata[2:0] = prio_i[145][2:0];
          prio_re_o[145] = 1'b1;
        end
        32'hc000248: begin
          resp_o.rdata[2:0] = prio_i[146][2:0];
          prio_re_o[146] = 1'b1;
        end
        32'hc00024c: begin
          resp_o.rdata[2:0] = prio_i[147][2:0];
          prio_re_o[147] = 1'b1;
        end
        32'hc000250: begin
          resp_o.rdata[2:0] = prio_i[148][2:0];
          prio_re_o[148] = 1'b1;
        end
        32'hc000254: begin
          resp_o.rdata[2:0] = prio_i[149][2:0];
          prio_re_o[149] = 1'b1;
        end
        32'hc000258: begin
          resp_o.rdata[2:0] = prio_i[150][2:0];
          prio_re_o[150] = 1'b1;
        end
        32'hc00025c: begin
          resp_o.rdata[2:0] = prio_i[151][2:0];
          prio_re_o[151] = 1'b1;
        end
        32'hc000260: begin
          resp_o.rdata[2:0] = prio_i[152][2:0];
          prio_re_o[152] = 1'b1;
        end
        32'hc000264: begin
          resp_o.rdata[2:0] = prio_i[153][2:0];
          prio_re_o[153] = 1'b1;
        end
        32'hc000268: begin
          resp_o.rdata[2:0] = prio_i[154][2:0];
          prio_re_o[154] = 1'b1;
        end
        32'hc00026c: begin
          resp_o.rdata[2:0] = prio_i[155][2:0];
          prio_re_o[155] = 1'b1;
        end
        32'hc000270: begin
          resp_o.rdata[2:0] = prio_i[156][2:0];
          prio_re_o[156] = 1'b1;
        end
        32'hc000274: begin
          resp_o.rdata[2:0] = prio_i[157][2:0];
          prio_re_o[157] = 1'b1;
        end
        32'hc000278: begin
          resp_o.rdata[2:0] = prio_i[158][2:0];
          prio_re_o[158] = 1'b1;
        end
        32'hc00027c: begin
          resp_o.rdata[2:0] = prio_i[159][2:0];
          prio_re_o[159] = 1'b1;
        end
        32'hc000280: begin
          resp_o.rdata[2:0] = prio_i[160][2:0];
          prio_re_o[160] = 1'b1;
        end
        32'hc000284: begin
          resp_o.rdata[2:0] = prio_i[161][2:0];
          prio_re_o[161] = 1'b1;
        end
        32'hc000288: begin
          resp_o.rdata[2:0] = prio_i[162][2:0];
          prio_re_o[162] = 1'b1;
        end
        32'hc00028c: begin
          resp_o.rdata[2:0] = prio_i[163][2:0];
          prio_re_o[163] = 1'b1;
        end
        32'hc000290: begin
          resp_o.rdata[2:0] = prio_i[164][2:0];
          prio_re_o[164] = 1'b1;
        end
        32'hc000294: begin
          resp_o.rdata[2:0] = prio_i[165][2:0];
          prio_re_o[165] = 1'b1;
        end
        32'hc000298: begin
          resp_o.rdata[2:0] = prio_i[166][2:0];
          prio_re_o[166] = 1'b1;
        end
        32'hc00029c: begin
          resp_o.rdata[2:0] = prio_i[167][2:0];
          prio_re_o[167] = 1'b1;
        end
        32'hc0002a0: begin
          resp_o.rdata[2:0] = prio_i[168][2:0];
          prio_re_o[168] = 1'b1;
        end
        32'hc0002a4: begin
          resp_o.rdata[2:0] = prio_i[169][2:0];
          prio_re_o[169] = 1'b1;
        end
        32'hc0002a8: begin
          resp_o.rdata[2:0] = prio_i[170][2:0];
          prio_re_o[170] = 1'b1;
        end
        32'hc0002ac: begin
          resp_o.rdata[2:0] = prio_i[171][2:0];
          prio_re_o[171] = 1'b1;
        end
        32'hc0002b0: begin
          resp_o.rdata[2:0] = prio_i[172][2:0];
          prio_re_o[172] = 1'b1;
        end
        32'hc0002b4: begin
          resp_o.rdata[2:0] = prio_i[173][2:0];
          prio_re_o[173] = 1'b1;
        end
        32'hc0002b8: begin
          resp_o.rdata[2:0] = prio_i[174][2:0];
          prio_re_o[174] = 1'b1;
        end
        32'hc0002bc: begin
          resp_o.rdata[2:0] = prio_i[175][2:0];
          prio_re_o[175] = 1'b1;
        end
        32'hc0002c0: begin
          resp_o.rdata[2:0] = prio_i[176][2:0];
          prio_re_o[176] = 1'b1;
        end
        32'hc0002c4: begin
          resp_o.rdata[2:0] = prio_i[177][2:0];
          prio_re_o[177] = 1'b1;
        end
        32'hc0002c8: begin
          resp_o.rdata[2:0] = prio_i[178][2:0];
          prio_re_o[178] = 1'b1;
        end
        32'hc0002cc: begin
          resp_o.rdata[2:0] = prio_i[179][2:0];
          prio_re_o[179] = 1'b1;
        end
        32'hc0002d0: begin
          resp_o.rdata[2:0] = prio_i[180][2:0];
          prio_re_o[180] = 1'b1;
        end
        32'hc0002d4: begin
          resp_o.rdata[2:0] = prio_i[181][2:0];
          prio_re_o[181] = 1'b1;
        end
        32'hc0002d8: begin
          resp_o.rdata[2:0] = prio_i[182][2:0];
          prio_re_o[182] = 1'b1;
        end
        32'hc0002dc: begin
          resp_o.rdata[2:0] = prio_i[183][2:0];
          prio_re_o[183] = 1'b1;
        end
        32'hc0002e0: begin
          resp_o.rdata[2:0] = prio_i[184][2:0];
          prio_re_o[184] = 1'b1;
        end
        32'hc0002e4: begin
          resp_o.rdata[2:0] = prio_i[185][2:0];
          prio_re_o[185] = 1'b1;
        end
        32'hc0002e8: begin
          resp_o.rdata[2:0] = prio_i[186][2:0];
          prio_re_o[186] = 1'b1;
        end
        32'hc0002ec: begin
          resp_o.rdata[2:0] = prio_i[187][2:0];
          prio_re_o[187] = 1'b1;
        end
        32'hc0002f0: begin
          resp_o.rdata[2:0] = prio_i[188][2:0];
          prio_re_o[188] = 1'b1;
        end
        32'hc0002f4: begin
          resp_o.rdata[2:0] = prio_i[189][2:0];
          prio_re_o[189] = 1'b1;
        end
        32'hc0002f8: begin
          resp_o.rdata[2:0] = prio_i[190][2:0];
          prio_re_o[190] = 1'b1;
        end
        32'hc0002fc: begin
          resp_o.rdata[2:0] = prio_i[191][2:0];
          prio_re_o[191] = 1'b1;
        end
        32'hc000300: begin
          resp_o.rdata[2:0] = prio_i[192][2:0];
          prio_re_o[192] = 1'b1;
        end
        32'hc000304: begin
          resp_o.rdata[2:0] = prio_i[193][2:0];
          prio_re_o[193] = 1'b1;
        end
        32'hc000308: begin
          resp_o.rdata[2:0] = prio_i[194][2:0];
          prio_re_o[194] = 1'b1;
        end
        32'hc00030c: begin
          resp_o.rdata[2:0] = prio_i[195][2:0];
          prio_re_o[195] = 1'b1;
        end
        32'hc000310: begin
          resp_o.rdata[2:0] = prio_i[196][2:0];
          prio_re_o[196] = 1'b1;
        end
        32'hc000314: begin
          resp_o.rdata[2:0] = prio_i[197][2:0];
          prio_re_o[197] = 1'b1;
        end
        32'hc000318: begin
          resp_o.rdata[2:0] = prio_i[198][2:0];
          prio_re_o[198] = 1'b1;
        end
        32'hc00031c: begin
          resp_o.rdata[2:0] = prio_i[199][2:0];
          prio_re_o[199] = 1'b1;
        end
        32'hc000320: begin
          resp_o.rdata[2:0] = prio_i[200][2:0];
          prio_re_o[200] = 1'b1;
        end
        32'hc000324: begin
          resp_o.rdata[2:0] = prio_i[201][2:0];
          prio_re_o[201] = 1'b1;
        end
        32'hc000328: begin
          resp_o.rdata[2:0] = prio_i[202][2:0];
          prio_re_o[202] = 1'b1;
        end
        32'hc00032c: begin
          resp_o.rdata[2:0] = prio_i[203][2:0];
          prio_re_o[203] = 1'b1;
        end
        32'hc000330: begin
          resp_o.rdata[2:0] = prio_i[204][2:0];
          prio_re_o[204] = 1'b1;
        end
        32'hc000334: begin
          resp_o.rdata[2:0] = prio_i[205][2:0];
          prio_re_o[205] = 1'b1;
        end
        32'hc000338: begin
          resp_o.rdata[2:0] = prio_i[206][2:0];
          prio_re_o[206] = 1'b1;
        end
        32'hc00033c: begin
          resp_o.rdata[2:0] = prio_i[207][2:0];
          prio_re_o[207] = 1'b1;
        end
        32'hc000340: begin
          resp_o.rdata[2:0] = prio_i[208][2:0];
          prio_re_o[208] = 1'b1;
        end
        32'hc000344: begin
          resp_o.rdata[2:0] = prio_i[209][2:0];
          prio_re_o[209] = 1'b1;
        end
        32'hc000348: begin
          resp_o.rdata[2:0] = prio_i[210][2:0];
          prio_re_o[210] = 1'b1;
        end
        32'hc00034c: begin
          resp_o.rdata[2:0] = prio_i[211][2:0];
          prio_re_o[211] = 1'b1;
        end
        32'hc000350: begin
          resp_o.rdata[2:0] = prio_i[212][2:0];
          prio_re_o[212] = 1'b1;
        end
        32'hc000354: begin
          resp_o.rdata[2:0] = prio_i[213][2:0];
          prio_re_o[213] = 1'b1;
        end
        32'hc000358: begin
          resp_o.rdata[2:0] = prio_i[214][2:0];
          prio_re_o[214] = 1'b1;
        end
        32'hc00035c: begin
          resp_o.rdata[2:0] = prio_i[215][2:0];
          prio_re_o[215] = 1'b1;
        end
        32'hc000360: begin
          resp_o.rdata[2:0] = prio_i[216][2:0];
          prio_re_o[216] = 1'b1;
        end
        32'hc000364: begin
          resp_o.rdata[2:0] = prio_i[217][2:0];
          prio_re_o[217] = 1'b1;
        end
        32'hc000368: begin
          resp_o.rdata[2:0] = prio_i[218][2:0];
          prio_re_o[218] = 1'b1;
        end
        32'hc00036c: begin
          resp_o.rdata[2:0] = prio_i[219][2:0];
          prio_re_o[219] = 1'b1;
        end
        32'hc000370: begin
          resp_o.rdata[2:0] = prio_i[220][2:0];
          prio_re_o[220] = 1'b1;
        end
        32'hc000374: begin
          resp_o.rdata[2:0] = prio_i[221][2:0];
          prio_re_o[221] = 1'b1;
        end
        32'hc000378: begin
          resp_o.rdata[2:0] = prio_i[222][2:0];
          prio_re_o[222] = 1'b1;
        end
        32'hc00037c: begin
          resp_o.rdata[2:0] = prio_i[223][2:0];
          prio_re_o[223] = 1'b1;
        end
        32'hc000380: begin
          resp_o.rdata[2:0] = prio_i[224][2:0];
          prio_re_o[224] = 1'b1;
        end
        32'hc000384: begin
          resp_o.rdata[2:0] = prio_i[225][2:0];
          prio_re_o[225] = 1'b1;
        end
        32'hc000388: begin
          resp_o.rdata[2:0] = prio_i[226][2:0];
          prio_re_o[226] = 1'b1;
        end
        32'hc00038c: begin
          resp_o.rdata[2:0] = prio_i[227][2:0];
          prio_re_o[227] = 1'b1;
        end
        32'hc000390: begin
          resp_o.rdata[2:0] = prio_i[228][2:0];
          prio_re_o[228] = 1'b1;
        end
        32'hc000394: begin
          resp_o.rdata[2:0] = prio_i[229][2:0];
          prio_re_o[229] = 1'b1;
        end
        32'hc000398: begin
          resp_o.rdata[2:0] = prio_i[230][2:0];
          prio_re_o[230] = 1'b1;
        end
        32'hc00039c: begin
          resp_o.rdata[2:0] = prio_i[231][2:0];
          prio_re_o[231] = 1'b1;
        end
        32'hc0003a0: begin
          resp_o.rdata[2:0] = prio_i[232][2:0];
          prio_re_o[232] = 1'b1;
        end
        32'hc0003a4: begin
          resp_o.rdata[2:0] = prio_i[233][2:0];
          prio_re_o[233] = 1'b1;
        end
        32'hc0003a8: begin
          resp_o.rdata[2:0] = prio_i[234][2:0];
          prio_re_o[234] = 1'b1;
        end
        32'hc0003ac: begin
          resp_o.rdata[2:0] = prio_i[235][2:0];
          prio_re_o[235] = 1'b1;
        end
        32'hc0003b0: begin
          resp_o.rdata[2:0] = prio_i[236][2:0];
          prio_re_o[236] = 1'b1;
        end
        32'hc0003b4: begin
          resp_o.rdata[2:0] = prio_i[237][2:0];
          prio_re_o[237] = 1'b1;
        end
        32'hc0003b8: begin
          resp_o.rdata[2:0] = prio_i[238][2:0];
          prio_re_o[238] = 1'b1;
        end
        32'hc0003bc: begin
          resp_o.rdata[2:0] = prio_i[239][2:0];
          prio_re_o[239] = 1'b1;
        end
        32'hc0003c0: begin
          resp_o.rdata[2:0] = prio_i[240][2:0];
          prio_re_o[240] = 1'b1;
        end
        32'hc0003c4: begin
          resp_o.rdata[2:0] = prio_i[241][2:0];
          prio_re_o[241] = 1'b1;
        end
        32'hc0003c8: begin
          resp_o.rdata[2:0] = prio_i[242][2:0];
          prio_re_o[242] = 1'b1;
        end
        32'hc0003cc: begin
          resp_o.rdata[2:0] = prio_i[243][2:0];
          prio_re_o[243] = 1'b1;
        end
        32'hc0003d0: begin
          resp_o.rdata[2:0] = prio_i[244][2:0];
          prio_re_o[244] = 1'b1;
        end
        32'hc0003d4: begin
          resp_o.rdata[2:0] = prio_i[245][2:0];
          prio_re_o[245] = 1'b1;
        end
        32'hc0003d8: begin
          resp_o.rdata[2:0] = prio_i[246][2:0];
          prio_re_o[246] = 1'b1;
        end
        32'hc0003dc: begin
          resp_o.rdata[2:0] = prio_i[247][2:0];
          prio_re_o[247] = 1'b1;
        end
        32'hc0003e0: begin
          resp_o.rdata[2:0] = prio_i[248][2:0];
          prio_re_o[248] = 1'b1;
        end
        32'hc0003e4: begin
          resp_o.rdata[2:0] = prio_i[249][2:0];
          prio_re_o[249] = 1'b1;
        end
        32'hc0003e8: begin
          resp_o.rdata[2:0] = prio_i[250][2:0];
          prio_re_o[250] = 1'b1;
        end
        32'hc0003ec: begin
          resp_o.rdata[2:0] = prio_i[251][2:0];
          prio_re_o[251] = 1'b1;
        end
        32'hc0003f0: begin
          resp_o.rdata[2:0] = prio_i[252][2:0];
          prio_re_o[252] = 1'b1;
        end
        32'hc0003f4: begin
          resp_o.rdata[2:0] = prio_i[253][2:0];
          prio_re_o[253] = 1'b1;
        end
        32'hc0003f8: begin
          resp_o.rdata[2:0] = prio_i[254][2:0];
          prio_re_o[254] = 1'b1;
        end
        32'hc0003fc: begin
          resp_o.rdata[2:0] = prio_i[255][2:0];
          prio_re_o[255] = 1'b1;
        end
        32'hc001000: begin
          resp_o.rdata[31:0] = ip_i[0][31:0];
          ip_re_o[0] = 1'b1;
        end
        32'hc001004: begin
          resp_o.rdata[31:0] = ip_i[0][63:32];
          ip_re_o[0] = 1'b1;
        end
        32'hc001008: begin
          resp_o.rdata[31:0] = ip_i[0][95:63];
          ip_re_o[0] = 1'b1;
        end
        32'hc00100c: begin
          resp_o.rdata[31:0] = ip_i[0][127:96];
          ip_re_o[0] = 1'b1;
        end
        32'hc001010: begin
          resp_o.rdata[31:0] = ip_i[0][159:128];
          ip_re_o[0] = 1'b1;
        end
        32'hc001014: begin
          resp_o.rdata[31:0] = ip_i[0][191:160];
          ip_re_o[0] = 1'b1;
        end
        32'hc001018: begin
          resp_o.rdata[31:0] = ip_i[0][223:192];
          ip_re_o[0] = 1'b1;
        end
        32'hc00101c: begin
          resp_o.rdata[31:0] = ip_i[0][255:224];
          ip_re_o[0] = 1'b1;
        end
        32'hc002000: begin
          resp_o.rdata[31:0] = ie_i[0][31:0];
          ie_re_o[0] = 1'b1;
        end
        32'hc002004: begin
          resp_o.rdata[31:0] = ie_i[0][63:32];
          ie_re_o[0] = 1'b1;
        end
        32'hc002008: begin
          resp_o.rdata[31:0] = ie_i[0][95:64];
          ie_re_o[0] = 1'b1;
        end
        32'hc00200c: begin
          resp_o.rdata[31:0] = ie_i[0][127:96];
          ie_re_o[0] = 1'b1;
        end
        32'hc002010: begin
          resp_o.rdata[31:0] = ie_i[0][159:128];
          ie_re_o[0] = 1'b1;
        end
        32'hc002014: begin
          resp_o.rdata[31:0] = ie_i[0][191:160];
          ie_re_o[0] = 1'b1;
        end
        32'hc002018: begin
          resp_o.rdata[31:0] = ie_i[0][223:192];
          ie_re_o[0] = 1'b1;
        end
        32'hc00201c: begin
          resp_o.rdata[31:0] = ie_i[0][255:224];
          ie_re_o[0] = 1'b1;
        end
        32'hc002080: begin
          resp_o.rdata[31:0] = ie_i[1][31:0];
          ie_re_o[1] = 1'b1;
        end
        32'hc002084: begin
          resp_o.rdata[31:0] = ie_i[1][63:32];
          ie_re_o[1] = 1'b1;
        end
        32'hc002088: begin
          resp_o.rdata[31:0] = ie_i[1][95:64];
          ie_re_o[1] = 1'b1;
        end
        32'hc00208c: begin
          resp_o.rdata[31:0] = ie_i[1][127:96];
          ie_re_o[1] = 1'b1;
        end
        32'hc002090: begin
          resp_o.rdata[31:0] = ie_i[1][159:128];
          ie_re_o[1] = 1'b1;
        end
        32'hc002094: begin
          resp_o.rdata[31:0] = ie_i[1][191:160];
          ie_re_o[1] = 1'b1;
        end
        32'hc002098: begin
          resp_o.rdata[31:0] = ie_i[1][223:192];
          ie_re_o[1] = 1'b1;
        end
        32'hc00209c: begin
          resp_o.rdata[31:0] = ie_i[1][255:224];
          ie_re_o[1] = 1'b1;
        end
        32'hc200000: begin
          resp_o.rdata[2:0] = threshold_i[0][2:0];
          threshold_re_o[0] = 1'b1;
        end
        32'hc201000: begin
          resp_o.rdata[2:0] = threshold_i[1][2:0];
          threshold_re_o[1] = 1'b1;
        end
        32'hc200004: begin
          resp_o.rdata[7:0] = cc_i[0][7:0];
          cc_re_o[0] = 1'b1;
        end
        32'hc201004: begin
          resp_o.rdata[7:0] = cc_i[1][7:0];
          cc_re_o[1] = 1'b1;
        end
        default: resp_o.error = 1'b1;
      endcase
    end
  end
end
endmodule

