// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the “License”); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an “AS IS” BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// This file contains all div_sqrt_top_mvp parameters
// Authors    : Lei Li  (lile@iis.ee.ethz.ch)

package defs_div_sqrt_mvp;

   // op command
   localparam C_RM                  = 3;
   localparam C_RM_NEAREST          = 3'h0;
   localparam C_RM_TRUNC            = 3'h1;
   localparam C_RM_PLUSINF          = 3'h2;
   localparam C_RM_MINUSINF         = 3'h3;
   localparam C_PC                  = 6; // Precision Control
   localparam C_FS                  = 2; // Format Selection
   localparam C_IUNC                = 2; // Iteration Unit Number Control
   localparam Iteration_unit_num_S  = 2'b10;

   // FP64
   localparam C_OP_FP64             = 64;
   localparam C_MANT_FP64           = 52;
   localparam C_EXP_FP64            = 11;
   localparam C_BIAS_FP64           = 1023;
   localparam C_BIAS_AONE_FP64      = 11'h400;
   localparam C_HALF_BIAS_FP64      = 511;
   localparam C_EXP_ZERO_FP64       = 11'h000;
   localparam C_EXP_ONE_FP64        = 13'h001; // Bit width is in agreement with in norm
   localparam C_EXP_INF_FP64        = 11'h7FF;
   localparam C_MANT_ZERO_FP64      = 52'h0;
   localparam C_MANT_NAN_FP64       = 52'h8_0000_0000_0000;
   localparam C_PZERO_FP64          = 64'h0000_0000_0000_0000;
   localparam C_MZERO_FP64          = 64'h8000_0000_0000_0000;
   localparam C_QNAN_FP64           = 64'h7FF8_0000_0000_0000;

   // FP32
   localparam C_OP_FP32             = 32;
   localparam C_MANT_FP32           = 23;
   localparam C_EXP_FP32            = 8;
   localparam C_BIAS_FP32           = 127;
   localparam C_BIAS_AONE_FP32      = 8'h80;
   localparam C_HALF_BIAS_FP32      = 63;
   localparam C_EXP_ZERO_FP32       = 8'h00;
   localparam C_EXP_INF_FP32        = 8'hFF;
   localparam C_MANT_ZERO_FP32      = 23'h0;
   localparam C_PZERO_FP32          = 32'h0000_0000;
   localparam C_MZERO_FP32          = 32'h8000_0000;
   localparam C_QNAN_FP32           = 32'h7FC0_0000;

   // FP16
   localparam C_OP_FP16             = 16;
   localparam C_MANT_FP16           = 10;
   localparam C_EXP_FP16            = 5;
   localparam C_BIAS_FP16           = 15;
   localparam C_BIAS_AONE_FP16      = 5'h10;
   localparam C_HALF_BIAS_FP16      = 7;
   localparam C_EXP_ZERO_FP16       = 5'h00;
   localparam C_EXP_INF_FP16        = 5'h1F;
   localparam C_MANT_ZERO_FP16      = 10'h0;
   localparam C_PZERO_FP16          = 16'h0000;
   localparam C_MZERO_FP16          = 16'h8000;
   localparam C_QNAN_FP16           = 16'h7E00;

   // FP16alt
   localparam C_OP_FP16ALT           = 16;
   localparam C_MANT_FP16ALT         = 7;
   localparam C_EXP_FP16ALT          = 8;
   localparam C_BIAS_FP16ALT         = 127;
   localparam C_BIAS_AONE_FP16ALT    = 8'h80;
   localparam C_HALF_BIAS_FP16ALT    = 63;
   localparam C_EXP_ZERO_FP16ALT     = 8'h00;
   localparam C_EXP_INF_FP16ALT      = 8'hFF;
   localparam C_MANT_ZERO_FP16ALT    = 7'h0;
   localparam C_QNAN_FP16ALT         = 16'h7FC0;

endpackage : defs_div_sqrt_mvp
