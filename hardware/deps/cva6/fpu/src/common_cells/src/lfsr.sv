// Copyright 2019 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Author: Michael Schaffner <schaffner@iis.ee.ethz.ch>, ETH Zurich
// Date: 26.04.2019
//
// Description: This is a parametric LFSR with precomputed coefficients for
// LFSR lengths from 4 to 64bit.

// Additional block cipher layers can be instantiated to non-linearly transform
// the pseudo-random LFSR sequence at the output, and hence break the shifting
// patterns. The additional cipher layers can only be used for an LFSR width
// of 64bit, since the block cipher has been designed for that block length.

module lfsr #(
  parameter int unsigned          LfsrWidth     = 64,   // [4,64]
  parameter int unsigned          OutWidth      = 8,    // [1,LfsrWidth]
  parameter logic [LfsrWidth-1:0] RstVal        = '1,   // [1,2^LfsrWidth-1]
  // 0: disabled, the present cipher uses 31, but just a few layers (1-3) are enough
  // to break linear shifting patterns
  parameter int unsigned          CipherLayers  = 0,
  parameter bit                   CipherReg     = 1'b1  // additional output reg after cipher
) (
  input  logic                 clk_i,
  input  logic                 rst_ni,
  input  logic                 en_i,
  output logic [OutWidth-1:0]  out_o
);

// Galois LFSR feedback masks
// Automatically generated with get_lfsr_masks.py
// Masks are from https://users.ece.cmu.edu/~koopman/lfsr/
localparam logic [63:0] masks [4:64] = '{64'hC,
                                         64'h1E,
                                         64'h39,
                                         64'h7E,
                                         64'hFA,
                                         64'h1FD,
                                         64'h3FC,
                                         64'h64B,
                                         64'hD8F,
                                         64'h1296,
                                         64'h2496,
                                         64'h4357,
                                         64'h8679,
                                         64'h1030E,
                                         64'h206CD,
                                         64'h403FE,
                                         64'h807B8,
                                         64'h1004B2,
                                         64'h2006A8,
                                         64'h4004B2,
                                         64'h800B87,
                                         64'h10004F3,
                                         64'h200072D,
                                         64'h40006AE,
                                         64'h80009E3,
                                         64'h10000583,
                                         64'h20000C92,
                                         64'h400005B6,
                                         64'h80000EA6,
                                         64'h1000007A3,
                                         64'h200000ABF,
                                         64'h400000842,
                                         64'h80000123E,
                                         64'h100000074E,
                                         64'h2000000AE9,
                                         64'h400000086A,
                                         64'h8000001213,
                                         64'h1000000077E,
                                         64'h2000000123B,
                                         64'h40000000877,
                                         64'h8000000108D,
                                         64'h100000000AE9,
                                         64'h200000000E9F,
                                         64'h4000000008A6,
                                         64'h80000000191E,
                                         64'h100000000090E,
                                         64'h2000000000FB3,
                                         64'h4000000000D7D,
                                         64'h80000000016A5,
                                         64'h10000000000B4B,
                                         64'h200000000010AF,
                                         64'h40000000000DDE,
                                         64'h8000000000181A,
                                         64'h100000000000B65,
                                         64'h20000000000102D,
                                         64'h400000000000CD5,
                                         64'h8000000000024C1,
                                         64'h1000000000000EF6,
                                         64'h2000000000001363,
                                         64'h4000000000000FCD,
                                         64'h80000000000019E2};

// this S-box and permutation P has been taken from the Present Cipher,
// a super lightweight block cipher. use the cipher layers to add additional
// non-linearity to the LFSR output. note one layer does not fully correspond
// to the present cipher round, since the key and rekeying function is not applied here.
//
// See also:
// "PRESENT: An Ultra-Lightweight Block Cipher", A. Bogdanov et al., Ches 2007
// http://www.lightweightcrypto.org/present/present_ches2007.pdf

// this is the sbox from the present cipher
localparam logic[15:0][3:0] sbox4 = {4'h2, 4'h1, 4'h7, 4'h4,
                                     4'h8, 4'hF, 4'hE, 4'h3,
                                     4'hD, 4'hA, 4'h0, 4'h9,
                                     4'hB, 4'h6, 4'h5, 4'hC };

// these are the permutation indices of the present cipher
localparam logic[63:0][5:0] perm = {6'd63, 6'd47, 6'd31, 6'd15, 6'd62, 6'd46, 6'd30, 6'd14, 6'd61, 6'd45, 6'd29, 6'd13, 6'd60, 6'd44, 6'd28, 6'd12,
                                    6'd59, 6'd43, 6'd27, 6'd11, 6'd58, 6'd42, 6'd26, 6'd10, 6'd57, 6'd41, 6'd25, 6'd09, 6'd56, 6'd40, 6'd24, 6'd08,
                                    6'd55, 6'd39, 6'd23, 6'd07, 6'd54, 6'd38, 6'd22, 6'd06, 6'd53, 6'd37, 6'd21, 6'd05, 6'd52, 6'd36, 6'd20, 6'd04,
                                    6'd51, 6'd35, 6'd19, 6'd03, 6'd50, 6'd34, 6'd18, 6'd02, 6'd49, 6'd33, 6'd17, 6'd01, 6'd48, 6'd32, 6'd16, 6'd00};


function automatic logic [63:0] sbox4_layer(logic [63:0] in);
  logic [63:0] out;
  //for (logic [4:0] j = '0; j<16; j++) out[j*4 +: 4] = sbox4[in[j*4 +: 4]];
  // this simulates much faster than the loop
  out[0*4  +: 4] = sbox4[in[0*4  +: 4]];
  out[1*4  +: 4] = sbox4[in[1*4  +: 4]];
  out[2*4  +: 4] = sbox4[in[2*4  +: 4]];
  out[3*4  +: 4] = sbox4[in[3*4  +: 4]];

  out[4*4  +: 4] = sbox4[in[4*4  +: 4]];
  out[5*4  +: 4] = sbox4[in[5*4  +: 4]];
  out[6*4  +: 4] = sbox4[in[6*4  +: 4]];
  out[7*4  +: 4] = sbox4[in[7*4  +: 4]];

  out[8*4  +: 4] = sbox4[in[8*4  +: 4]];
  out[9*4  +: 4] = sbox4[in[9*4  +: 4]];
  out[10*4 +: 4] = sbox4[in[10*4 +: 4]];
  out[11*4 +: 4] = sbox4[in[11*4 +: 4]];

  out[12*4 +: 4] = sbox4[in[12*4 +: 4]];
  out[13*4 +: 4] = sbox4[in[13*4 +: 4]];
  out[14*4 +: 4] = sbox4[in[14*4 +: 4]];
  out[15*4 +: 4] = sbox4[in[15*4 +: 4]];
  return out;
endfunction : sbox4_layer

function automatic logic [63:0] perm_layer(logic [63:0] in);
  logic [63:0] out;
  // for (logic [7:0] j = '0; j<64; j++) out[perm[j]] = in[j];
  // this simulates much faster than the loop
  out[perm[0]] = in[0];
  out[perm[1]] = in[1];
  out[perm[2]] = in[2];
  out[perm[3]] = in[3];
  out[perm[4]] = in[4];
  out[perm[5]] = in[5];
  out[perm[6]] = in[6];
  out[perm[7]] = in[7];
  out[perm[8]] = in[8];
  out[perm[9]] = in[9];

  out[perm[10]] = in[10];
  out[perm[11]] = in[11];
  out[perm[12]] = in[12];
  out[perm[13]] = in[13];
  out[perm[14]] = in[14];
  out[perm[15]] = in[15];
  out[perm[16]] = in[16];
  out[perm[17]] = in[17];
  out[perm[18]] = in[18];
  out[perm[19]] = in[19];

  out[perm[20]] = in[20];
  out[perm[21]] = in[21];
  out[perm[22]] = in[22];
  out[perm[23]] = in[23];
  out[perm[24]] = in[24];
  out[perm[25]] = in[25];
  out[perm[26]] = in[26];
  out[perm[27]] = in[27];
  out[perm[28]] = in[28];
  out[perm[29]] = in[29];

  out[perm[30]] = in[30];
  out[perm[31]] = in[31];
  out[perm[32]] = in[32];
  out[perm[33]] = in[33];
  out[perm[34]] = in[34];
  out[perm[35]] = in[35];
  out[perm[36]] = in[36];
  out[perm[37]] = in[37];
  out[perm[38]] = in[38];
  out[perm[39]] = in[39];

  out[perm[40]] = in[40];
  out[perm[41]] = in[41];
  out[perm[42]] = in[42];
  out[perm[43]] = in[43];
  out[perm[44]] = in[44];
  out[perm[45]] = in[45];
  out[perm[46]] = in[46];
  out[perm[47]] = in[47];
  out[perm[48]] = in[48];
  out[perm[49]] = in[49];

  out[perm[50]] = in[50];
  out[perm[51]] = in[51];
  out[perm[52]] = in[52];
  out[perm[53]] = in[53];
  out[perm[54]] = in[54];
  out[perm[55]] = in[55];
  out[perm[56]] = in[56];
  out[perm[57]] = in[57];
  out[perm[58]] = in[58];
  out[perm[59]] = in[59];

  out[perm[60]] = in[60];
  out[perm[61]] = in[61];
  out[perm[62]] = in[62];
  out[perm[63]] = in[63];
  return out;
endfunction : perm_layer

////////////////////////////////////////////////////////////////////////
// lfsr
////////////////////////////////////////////////////////////////////////

logic [LfsrWidth-1:0] lfsr_d, lfsr_q;
assign lfsr_d = (en_i) ? (lfsr_q>>1) ^ ({LfsrWidth{lfsr_q[0]}} & masks[LfsrWidth][LfsrWidth-1:0]) : lfsr_q;

always_ff @(posedge clk_i or negedge rst_ni) begin : p_regs
  //$display("%b %h", en_i, lfsr_d);
  if (!rst_ni) begin
    lfsr_q <= LfsrWidth'(RstVal);
  end else begin
    lfsr_q <= lfsr_d;
  end
end

////////////////////////////////////////////////////////////////////////
// block cipher layers
////////////////////////////////////////////////////////////////////////

if (CipherLayers > unsigned'(0)) begin : g_cipher_layers
  logic [63:0] ciph_layer;
  localparam int unsigned NumRepl = ((64+LfsrWidth)/LfsrWidth);

  always_comb begin : p_ciph_layer
    automatic logic [63:0] tmp;
    tmp = 64'({NumRepl{lfsr_q}});
    for(int unsigned k = 0; k < CipherLayers; k++) begin
      tmp = perm_layer(sbox4_layer(tmp));
    end
    ciph_layer = tmp;
  end

  // additiona output reg after cipher
  if (CipherReg) begin : g_cipher_reg
    logic [OutWidth-1:0] out_d, out_q;

    assign out_d = (en_i) ? ciph_layer[OutWidth-1:0] : out_q;
    assign out_o = out_q[OutWidth-1:0];

    always_ff @(posedge clk_i or negedge rst_ni) begin : p_regs
      if (!rst_ni) begin
        out_q <= '0;
      end else begin
        out_q <= out_d;
      end
    end
  // no outreg
  end else begin : g_no_out_reg
    assign out_o  = ciph_layer[OutWidth-1:0];
  end

// no block cipher
end else begin : g_no_cipher_layers
  assign out_o    = lfsr_q[OutWidth-1:0];
end

////////////////////////////////////////////////////////////////////////
// assertions
////////////////////////////////////////////////////////////////////////

// pragma translate_off
initial begin
  // these are the LUT limits
  assert(OutWidth <= LfsrWidth) else
    $fatal(1,"OutWidth must be smaller equal the LfsrWidth.");
  assert(RstVal > unsigned'(0)) else
    $fatal(1,"RstVal must be nonzero.");
  assert((LfsrWidth >= $low(masks)) && (LfsrWidth <= $high(masks))) else
    $fatal(1,"Unsupported LfsrWidth.");
  assert(masks[LfsrWidth][LfsrWidth-1]) else
    $fatal(1, "LFSR mask is not correct. The MSB must be 1." );
  assert((CipherLayers > 0) && (LfsrWidth == 64) || (CipherLayers == 0)) else
    $fatal(1, "Use additional cipher layers only in conjunction with an LFSR width of 64 bit." );
end

`ifndef VERILATOR
  all_zero: assert property (
    @(posedge clk_i) disable iff (!rst_ni) en_i |-> lfsr_d)
      else $fatal(1,"Lfsr must not be all-zero.");
`endif
// pragma translate_on

endmodule // lfsr
