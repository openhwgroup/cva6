// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

////////////////////////////////////////////////////////////////////////////////
// Engineer:       Igor Loi - igor.loi@unibo.it                               //
//                                                                            //
// Additional contributions by:                                               //
//                 Davide Schiavone - pschiavo@iis.ee.ethz.ch                 //
//                                                                            //
// Design Name:    BASIC MPU                                                  //
// Project Name:   RISCV                                                      //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    BASIC MPU: it suppoerts NA4, DIS, NAPOT and TOR            //
//                 NAPOT can be configured from 8B to 4GB                     //
//                 Number of RULES is parametric, and TOR and NAPOT can be    //
//                 disabled.                                                  //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////



`define RULE_0  32'bxxxxxxxx_xxxxxxxx_xxxxxxxx_xxxxxxx0
`define RULE_1  32'bxxxxxxxx_xxxxxxxx_xxxxxxxx_xxxxxx01
`define RULE_2  32'bxxxxxxxx_xxxxxxxx_xxxxxxxx_xxxxx011
`define RULE_3  32'bxxxxxxxx_xxxxxxxx_xxxxxxxx_xxxx0111
`define RULE_4  32'bxxxxxxxx_xxxxxxxx_xxxxxxxx_xxx01111
`define RULE_5  32'bxxxxxxxx_xxxxxxxx_xxxxxxxx_xx011111
`define RULE_6  32'bxxxxxxxx_xxxxxxxx_xxxxxxxx_x0111111
`define RULE_7  32'bxxxxxxxx_xxxxxxxx_xxxxxxxx_01111111
`define RULE_8  32'bxxxxxxxx_xxxxxxxx_xxxxxxx0_11111111
`define RULE_9  32'bxxxxxxxx_xxxxxxxx_xxxxxx01_11111111
`define RULE_10 32'bxxxxxxxx_xxxxxxxx_xxxxx011_11111111
`define RULE_11 32'bxxxxxxxx_xxxxxxxx_xxxx0111_11111111
`define RULE_12 32'bxxxxxxxx_xxxxxxxx_xxx01111_11111111
`define RULE_13 32'bxxxxxxxx_xxxxxxxx_xx011111_11111111
`define RULE_14 32'bxxxxxxxx_xxxxxxxx_x0111111_11111111
`define RULE_15 32'bxxxxxxxx_xxxxxxxx_01111111_11111111
`define RULE_16 32'bxxxxxxxx_xxxxxxx0_11111111_11111111
`define RULE_17 32'bxxxxxxxx_xxxxxx01_11111111_11111111
`define RULE_18 32'bxxxxxxxx_xxxxx011_11111111_11111111
`define RULE_19 32'bxxxxxxxx_xxxx0111_11111111_11111111
`define RULE_20 32'bxxxxxxxx_xxx01111_11111111_11111111
`define RULE_21 32'bxxxxxxxx_xx011111_11111111_11111111
`define RULE_22 32'bxxxxxxxx_x0111111_11111111_11111111
`define RULE_23 32'bxxxxxxxx_01111111_11111111_11111111
`define RULE_24 32'bxxxxxxx0_11111111_11111111_11111111
`define RULE_25 32'bxxxxxx01_11111111_11111111_11111111
`define RULE_26 32'bxxxxx011_11111111_11111111_11111111
`define RULE_27 32'bxxxx0111_11111111_11111111_11111111
`define RULE_28 32'bxxx01111_11111111_11111111_11111111
`define RULE_29 32'bxx011111_11111111_11111111_11111111
`define RULE_30 32'bx0111111_11111111_11111111_11111111
`define RULE_31 32'b01111111_11111111_11111111_11111111



`define EN_NAPOT_RULE_8B       /* 0  */
`define EN_NAPOT_RULE_16B      /* 1  */
`define EN_NAPOT_RULE_32B      /* 2  */
`define EN_NAPOT_RULE_64B      /* 3  */
`define EN_NAPOT_RULE_128B     /* 4  */
`define EN_NAPOT_RULE_256B     /* 5  */
`define EN_NAPOT_RULE_512B     /* 6  */
`define EN_NAPOT_RULE_1KB      /* 7  */
`define EN_NAPOT_RULE_2KB      /* 8  */
`define EN_NAPOT_RULE_4KB      /* 9  */
`define EN_NAPOT_RULE_8KB      /* 10 */
`define EN_NAPOT_RULE_16KB     /* 11 */
`define EN_NAPOT_RULE_32KB     /* 12 */
`define EN_NAPOT_RULE_64KB     /* 13 */
`define EN_NAPOT_RULE_128KB    /* 14 */
`define EN_NAPOT_RULE_256KB    /* 15 */
//`define EN_NAPOT_RULE_512KB    /* 16 */
//`define EN_NAPOT_RULE_1MB      /* 17 */
//`define EN_NAPOT_RULE_2MB      /* 18 */
//`define EN_NAPOT_RULE_4MB      /* 19 */
//`define EN_NAPOT_RULE_8MB      /* 20 */
//`define EN_NAPOT_RULE_16MB     /* 21 */
//`define EN_NAPOT_RULE_32MB     /* 22 */
//`define EN_NAPOT_RULE_64MB     /* 23 */
//`define EN_NAPOT_RULE_128MB    /* 24 */
//`define EN_NAPOT_RULE_256MB    /* 25 */
//`define EN_NAPOT_RULE_512MB    /* 26 */
//`define EN_NAPOT_RULE_1GB      /* 27 */
//`define EN_NAPOT_RULE_2GB      /* 28 */
//`define EN_NAPOT_RULE_4GB      /* 29 */
//`define EN_NAPOT_RULE_8GB      /* 30 */
//`define EN_NAPOT_RULE_16GB     /* 31 */


`define ENABLE_NAPOT
`define ENABLE_TOR

//`define DEBUG_RULE

import riscv_defines::*;

module riscv_pmp
#(
   parameter N_PMP_ENTRIES = 16
)
(
   input logic                             clk,
   input logic                             rst_n,

   input PrivLvl_t                         pmp_privil_mode_i,

   input logic  [N_PMP_ENTRIES-1:0] [31:0] pmp_addr_i,
   input logic  [N_PMP_ENTRIES-1:0] [7:0]  pmp_cfg_i,


   // data side : if TO pipeline
   input  logic                            data_req_i,
   input  logic [31:0]                     data_addr_i,
   input  logic                            data_we_i,
   output logic                            data_gnt_o,
   // if to Memory
   output logic                            data_req_o,
   input  logic                            data_gnt_i,
   output logic [31:0]                     data_addr_o,
   output logic                            data_err_o,
   input  logic                            data_err_ack_i,


   // fetch side : if TO pipeline
   input  logic                            instr_req_i,
   input  logic [31:0]                     instr_addr_i,
   output logic                            instr_gnt_o,
   // fetch to PF buffer
   output logic                            instr_req_o,
   input  logic                            instr_gnt_i,
   output logic [31:0]                     instr_addr_o,
   output logic                            instr_err_o
);


   logic [N_PMP_ENTRIES-1:0]      EN_rule;
   logic [N_PMP_ENTRIES-1:0]      R_rule;
   logic [N_PMP_ENTRIES-1:0]      W_rule;
   logic [N_PMP_ENTRIES-1:0]      X_rule;
   logic [N_PMP_ENTRIES-1:0][1:0] MODE_rule;
   logic [N_PMP_ENTRIES-1:0][1:0] WIRI_rule;
   logic [N_PMP_ENTRIES-1:0][1:0] LOCK_rule;
   logic [N_PMP_ENTRIES-1:0][31:0] mask_addr;

   logic [N_PMP_ENTRIES-1:0][31:0] start_addr;
   logic [N_PMP_ENTRIES-1:0][31:0] stop_addr;
   logic [N_PMP_ENTRIES-1:0]       data_match_region;
   logic [N_PMP_ENTRIES-1:0]       instr_match_region;
   logic                            data_err_int;
   genvar i;
   int unsigned j,k;


   ///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
   // ██████╗ ██╗   ██╗██╗     ███████╗    ███████╗██╗  ██╗██████╗  █████╗ ███╗   ██╗███████╗██╗ ██████╗ ███╗   ██╗ //
   // ██╔══██╗██║   ██║██║     ██╔════╝    ██╔════╝╚██╗██╔╝██╔══██╗██╔══██╗████╗  ██║██╔════╝██║██╔═══██╗████╗  ██║ //
   // ██████╔╝██║   ██║██║     █████╗      █████╗   ╚███╔╝ ██████╔╝███████║██╔██╗ ██║███████╗██║██║   ██║██╔██╗ ██║ //
   // ██╔══██╗██║   ██║██║     ██╔══╝      ██╔══╝   ██╔██╗ ██╔═══╝ ██╔══██║██║╚██╗██║╚════██║██║██║   ██║██║╚██╗██║ //
   // ██║  ██║╚██████╔╝███████╗███████╗    ███████╗██╔╝ ██╗██║     ██║  ██║██║ ╚████║███████║██║╚██████╔╝██║ ╚████║ //
   // ╚═╝  ╚═╝ ╚═════╝ ╚══════╝╚══════╝    ╚══════╝╚═╝  ╚═╝╚═╝     ╚═╝  ╚═╝╚═╝  ╚═══╝╚══════╝╚═╝ ╚═════╝ ╚═╝  ╚═══╝ //
   ///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
   generate
      for(i=0;i<N_PMP_ENTRIES;i++)
      begin : CFG_EXP
         assign {LOCK_rule[i],WIRI_rule[i],MODE_rule[i],X_rule[i], W_rule[i], R_rule[i] } = pmp_cfg_i[i];
      end

      // address Expansion

      for(i=0;i<N_PMP_ENTRIES;i++)
      begin : ADDR_EXP
         always @(*)
         begin
            start_addr[i] = '0;
            stop_addr[i]  = '0;
            mask_addr[i]  = 32'hFFFF_FFFF;

            case (MODE_rule[i])
               2'b00:
               begin : DISABLED
                  EN_rule[i] = 1'b0;
                  `ifdef DEBUG_RULE $display(" DISABLED[%d]", i ); `endif
               end

`ifdef ENABLE_TOR
               2'b01:
               begin : TOR_MODE
                  EN_rule[i] = 1'b1;
                  if(i==0)
                  begin
                     start_addr[i] = 0;
                  end
                  else
                  begin
                     start_addr[i] = pmp_addr_i[i-1];
                  end

                  stop_addr[i] = pmp_addr_i[i];
                  `ifdef DEBUG_RULE $display(" TOR[%d]: %8h<-- addr --> %8h", i , start_addr[i]<<2, stop_addr[i]<<2 ); `endif
               end
`endif


               2'b10:
               begin : NA4_MODE
                  EN_rule[i] = 1'b1;
                  stop_addr[i]  = pmp_addr_i[i];
                  start_addr[i] = pmp_addr_i[i];
                  `ifdef DEBUG_RULE $display(" NA4[%d]  %8h<-- addr --> %8h", i, start_addr[i]<<2, stop_addr[i]<<2 ); `endif
               end

`ifdef ENABLE_NAPOT
               2'b11:
               begin : NAPOT_MODE
                  EN_rule[i]    = 1'b1;
                  mask_addr[i]  = 32'hFFFF_FFFF;
                  stop_addr[i]  = pmp_addr_i[i];
                  start_addr[i] = pmp_addr_i[i];



                  casex(pmp_addr_i[i])

      `ifdef EN_NAPOT_RULE_8B
                     `RULE_0:
                     begin: BYTE_ALIGN_8B
                        mask_addr[i]  = 32'hFFFF_FFFE;
                        start_addr[i] = pmp_addr_i[i] & mask_addr[i];
                        stop_addr[i]  = pmp_addr_i[i];

                        `ifdef DEBUG_RULE $display(" NAPOT[%d]  --> BYTE_ALIGN_8B: %8h<-- addr --> %8h", i, start_addr[i]<<2, stop_addr[i]<<2 ); `endif
                     end
      `endif
      `ifdef EN_NAPOT_RULE_16B
                     `RULE_1:
                     begin: BYTE_ALIGN_16B
                        mask_addr[i]  = 32'hFFFF_FFFC;
                        start_addr[i] = pmp_addr_i[i] & mask_addr[i];
                        stop_addr[i]  = pmp_addr_i[i];
                        `ifdef DEBUG_RULE $display(" NAPOT[%d]  --> BYTE_ALIGN_16B: %8h<-- addr --> %8h", i, start_addr[i]<<2, stop_addr[i]<<2 ); `endif
                     end
      `endif
      `ifdef EN_NAPOT_RULE_32B
                     `RULE_2:
                     begin: BYTE_ALIGN_32B
                        mask_addr[i]  = 32'hFFFF_FFF8;
                        start_addr[i] = pmp_addr_i[i] & mask_addr[i];
                        stop_addr[i]  = pmp_addr_i[i];
                        `ifdef DEBUG_RULE $display(" NAPOT[%d]  --> BYTE_ALIGN_32B: %8h<-- addr --> %8h", i, start_addr[i]<<2, stop_addr[i]<<2 ); `endif
                     end
      `endif
      `ifdef EN_NAPOT_RULE_64B
                     `RULE_3:
                     begin: BYTE_ALIGN_64B
                        mask_addr[i]  = 32'hFFFF_FFF0;
                        start_addr[i] = pmp_addr_i[i] & mask_addr[i];
                        stop_addr[i]  = pmp_addr_i[i];
                        `ifdef DEBUG_RULE $display(" NAPOT[%d]  --> BYTE_ALIGN_64B: %8h<-- addr --> %8h", i, start_addr[i]<<2, stop_addr[i]<<2 ); `endif
                     end
      `endif



      `ifdef EN_NAPOT_RULE_128B
                     `RULE_4:
                     begin: BYTE_ALIGN_128B
                        mask_addr[i]  = 32'hFFFF_FFE0;
                        start_addr[i] = pmp_addr_i[i] & 32'hFFFF_FFE0;
                        stop_addr[i]  = pmp_addr_i[i];
                        `ifdef DEBUG_RULE $display(" NAPOT[%d]  --> BYTE_ALIGN_128B: %8h<-- addr --> %8h", i, start_addr[i]<<2, stop_addr[i]<<2 ); `endif
                     end
      `endif
      `ifdef EN_NAPOT_RULE_256B
                     `RULE_5:
                     begin: BYTE_ALIGN_256B
                        mask_addr[i]  = 32'hFFFF_FFC0;
                        start_addr[i] = pmp_addr_i[i] & mask_addr[i];
                        stop_addr[i]  = pmp_addr_i[i];
                        `ifdef DEBUG_RULE $display(" NAPOT[%d]  --> BYTE_ALIGN_256B: %8h<-- addr --> %8h", i, start_addr[i]<<2, stop_addr[i]<<2 ); `endif
                     end
      `endif
      `ifdef EN_NAPOT_RULE_512B
                     `RULE_6:
                     begin: BYTE_ALIGN_512B
                        mask_addr[i]  = 32'hFFFF_FF80;
                        start_addr[i] = pmp_addr_i[i] & mask_addr[i];
                        stop_addr[i]  = pmp_addr_i[i];
                        `ifdef DEBUG_RULE $display(" NAPOT[%d]  --> BYTE_ALIGN_512B: %8h<-- addr --> %8h", i, start_addr[i]<<2, stop_addr[i]<<2 ); `endif
                     end
      `endif
      `ifdef EN_NAPOT_RULE_1KB
                     `RULE_7:
                     begin: BYTE_ALIGN_1KB
                        mask_addr[i]  = 32'hFFFF_FF00;
                        start_addr[i] = pmp_addr_i[i] & mask_addr[i];
                        stop_addr[i]  = pmp_addr_i[i];
                        `ifdef DEBUG_RULE $display(" NAPOT[%d]  --> BYTE_ALIGN_1KB: %8h<-- addr --> %8h", i, start_addr[i]<<2, stop_addr[i]<<2 ); `endif
                     end
      `endif



      `ifdef EN_NAPOT_RULE_2KB
                     `RULE_8:
                     begin: BYTE_ALIGN_2KB
                        mask_addr[i]  = 32'hFFFF_FE00;
                        start_addr[i] = pmp_addr_i[i] & mask_addr[i];
                        stop_addr[i]  = pmp_addr_i[i];
                        `ifdef DEBUG_RULE $display(" NAPOT[%d]  --> BYTE_ALIGN_2K: %8h<-- addr --> %8h", i, start_addr[i]<<2, stop_addr[i]<<2 ); `endif
                     end
      `endif
      `ifdef EN_NAPOT_RULE_4KB
                     `RULE_9:
                     begin: BYTE_ALIGN_4KB
                        mask_addr[i]  = 32'hFFFF_FC00;
                        start_addr[i] = pmp_addr_i[i] & mask_addr[i];
                        stop_addr[i]  = pmp_addr_i[i];
                        `ifdef DEBUG_RULE $display(" NAPOT[%d]  --> BYTE_ALIGN_4KB: %8h<-- addr --> %8h", i, start_addr[i]<<2, stop_addr[i]<<2 ); `endif
                     end
      `endif
      `ifdef EN_NAPOT_RULE_8KB
                     `RULE_10:
                     begin: BYTE_ALIGN_8KB
                        mask_addr[i]  = 32'hFFFF_F800;
                        start_addr[i] = pmp_addr_i[i] & mask_addr[i];
                        stop_addr[i]  = pmp_addr_i[i];
                     `ifdef DEBUG_RULE $display(" NAPOT[%d]  --> BYTE_ALIGN_8KB: %8h<-- addr --> %8h", i, start_addr[i]<<2, stop_addr[i]<<2 ); `endif
                     end
      `endif
      `ifdef EN_NAPOT_RULE_16KB
                     `RULE_11:
                     begin: BYTE_ALIGN_16KB
                        mask_addr[i]  = 32'hFFFF_F000;
                        start_addr[i] = pmp_addr_i[i] & mask_addr[i];
                        stop_addr[i]  = pmp_addr_i[i];
                     `ifdef DEBUG_RULE $display(" NAPOT[%d]  --> BYTE_ALIGN_16KB: %8h<-- addr --> %8h", i, start_addr[i]<<2, stop_addr[i]<<2 ); `endif
                     end
      `endif



      `ifdef EN_NAPOT_RULE_32KB
                     `RULE_12:
                     begin: BYTE_ALIGN_32KB
                        mask_addr[i]  = 32'hFFFF_E000;
                        start_addr[i] = pmp_addr_i[i] & mask_addr[i];
                        stop_addr[i]  = pmp_addr_i[i];
                        `ifdef DEBUG_RULE $display(" NAPOT[%d]  --> BYTE_ALIGN_32KB: %8h<-- addr --> %8h", i, start_addr[i]<<2, stop_addr[i]<<2 ); `endif
                     end
      `endif
      `ifdef EN_NAPOT_RULE_64KB
                     `RULE_13:
                     begin: BYTE_ALIGN_64KB
                        mask_addr[i]  = 32'hFFFF_C000;
                        start_addr[i] = pmp_addr_i[i] & mask_addr[i];
                        stop_addr[i]  = pmp_addr_i[i];
                        `ifdef DEBUG_RULE $display(" NAPOT[%d]  --> BYTE_ALIGN_64KB: %8h<-- addr --> %8h", i, start_addr[i]<<2, stop_addr[i]<<2 ); `endif
                     end
      `endif
      `ifdef EN_NAPOT_RULE_128KB
                     `RULE_14:
                     begin: BYTE_ALIGN_128KB
                        mask_addr[i]  = 32'hFFFF_8000;
                        start_addr[i] = pmp_addr_i[i] & mask_addr[i];
                        stop_addr[i]  = pmp_addr_i[i];
                        `ifdef DEBUG_RULE $display(" NAPOT[%d]  --> BYTE_ALIGN_128KB: %8h<-- addr --> %8h", i, start_addr[i]<<2, stop_addr[i]<<2 ); `endif
                     end
      `endif
      `ifdef EN_NAPOT_RULE_256KB
                     `RULE_15:
                     begin: BYTE_ALIGN_256KB
                        mask_addr[i]  = 32'hFFFF_0000;
                        start_addr[i] = pmp_addr_i[i] & mask_addr[i];
                        stop_addr[i]  = pmp_addr_i[i];
                        `ifdef DEBUG_RULE $display(" NAPOT[%d]  --> BYTE_ALIGN_256KB: %8h<-- addr --> %8h", i, start_addr[i]<<2, stop_addr[i]<<2 ); `endif
                     end
      `endif



      `ifdef EN_NAPOT_RULE_512KB
                     `RULE_16:
                     begin: BYTE_ALIGN_512KB
                        mask_addr[i]  = 32'hFFFE_0000;
                        start_addr[i] = pmp_addr_i[i] & mask_addr[i];
                        stop_addr[i]  = pmp_addr_i[i];
                        `ifdef DEBUG_RULE $display(" NAPOT[%d]  --> BYTE_ALIGN_512KB: %8h<-- addr --> %8h", i, start_addr[i]<<2, stop_addr[i]<<2 ); `endif
                     end
      `endif
      `ifdef EN_NAPOT_RULE_1MB
                     `RULE_17:
                     begin: BYTE_ALIGN_1MB
                        mask_addr[i]  = 32'hFFFC_0000;
                        start_addr[i] = pmp_addr_i[i] & mask_addr[i];
                        stop_addr[i]  = pmp_addr_i[i];
                        `ifdef DEBUG_RULE $display(" NAPOT[%d]  --> BYTE_ALIGN_1MB: %8h<-- addr --> %8h", i, start_addr[i]<<2, stop_addr[i]<<2 ); `endif
                     end
      `endif
      `ifdef EN_NAPOT_RULE_2MB
                     `RULE_18:
                     begin: BYTE_ALIGN_2MB
                        mask_addr[i]  = 32'hFFF8_0000;
                        start_addr[i] = pmp_addr_i[i] & mask_addr[i];
                        stop_addr[i]  = pmp_addr_i[i];
                        `ifdef DEBUG_RULE $display(" NAPOT[%d]  --> BYTE_ALIGN_2MB: %8h<-- addr --> %8h", i, start_addr[i]<<2, stop_addr[i]<<2 ); `endif
                     end
      `endif
      `ifdef EN_NAPOT_RULE_4MB
                     `RULE_19:
                     begin: BYTE_ALIGN_4MB
                        mask_addr[i]  = 32'hFFF0_0000;
                        start_addr[i] = pmp_addr_i[i] & mask_addr[i];
                        stop_addr[i]  = pmp_addr_i[i];
                        `ifdef DEBUG_RULE $display(" NAPOT[%d]  --> BYTE_ALIGN_4MB: %8h<-- addr --> %8h", i, start_addr[i]<<2, stop_addr[i]<<2 ); `endif
                     end
      `endif


      `ifdef EN_NAPOT_RULE_8MB
                     `RULE_20:
                     begin: BYTE_ALIGN_8MB
                        mask_addr[i]  = 32'hFFE0_0000;
                        start_addr[i] = pmp_addr_i[i] & mask_addr[i];
                        stop_addr[i]  = pmp_addr_i[i];
                        `ifdef DEBUG_RULE $display(" NAPOT[%d]  --> BYTE_ALIGN_8MB: %8h<-- addr --> %8h", i, start_addr[i]<<2, stop_addr[i]<<2 ); `endif
                     end
      `endif
      `ifdef EN_NAPOT_RULE_16MB
                     `RULE_21:
                     begin: BYTE_ALIGN_16MB
                        mask_addr[i]  = 32'hFFC0_0000;
                        start_addr[i] = pmp_addr_i[i] & mask_addr[i];
                        stop_addr[i]  = pmp_addr_i[i];
                        `ifdef DEBUG_RULE $display(" NAPOT[%d]  --> BYTE_ALIGN_16MB: %8h<-- addr --> %8h", i, start_addr[i]<<2, stop_addr[i]<<2 ); `endif
                     end
      `endif
      `ifdef EN_NAPOT_RULE_32MB
                     `RULE_22:
                     begin: BYTE_ALIGN_32MB
                        mask_addr[i]  = 32'hFF80_0000;
                        start_addr[i] = pmp_addr_i[i] & mask_addr[i];
                        stop_addr[i]  = pmp_addr_i[i];
                        `ifdef DEBUG_RULE $display(" NAPOT[%d]  --> BYTE_ALIGN_32MB: %8h<-- addr --> %8h", i, start_addr[i]<<2, stop_addr[i]<<2 ); `endif
                     end
      `endif
      `ifdef EN_NAPOT_RULE_64MB
                     `RULE_23:
                     begin: BYTE_ALIGN_64MB
                        mask_addr[i]  = 32'hFF00_0000;
                        start_addr[i] = pmp_addr_i[i] & mask_addr[i];
                        stop_addr[i]  = pmp_addr_i[i];
                        `ifdef DEBUG_RULE $display(" NAPOT[%d]  --> BYTE_ALIGN_64MB: %8h<-- addr --> %8h", i, start_addr[i]<<2, stop_addr[i]<<2 ); `endif
                     end
      `endif



      `ifdef EN_NAPOT_RULE_128MB
                     `RULE_24:
                     begin: BYTE_ALIGN_128MB
                        mask_addr[i]  = 32'hFE00_0000;
                        start_addr[i] = pmp_addr_i[i] & mask_addr[i];
                        stop_addr[i]  = pmp_addr_i[i];
                     end
      `endif
      `ifdef EN_NAPOT_RULE_256MB
                     `RULE_25:
                     begin: BYTE_ALIGN_256MB
                        mask_addr[i]  = 32'hFC00_0000;
                        start_addr[i] = pmp_addr_i[i] & mask_addr[i];
                        stop_addr[i]  = pmp_addr_i[i];
                     end
      `endif
      `ifdef EN_NAPOT_RULE_512MB
                     `RULE_26:
                     begin: BYTE_ALIGN_512MB
                        mask_addr[i]  = 32'hF800_0000;
                        start_addr[i] = pmp_addr_i[i] & mask_addr[i];
                        stop_addr[i]  = pmp_addr_i[i];
                     end
      `endif
      `ifdef EN_NAPOT_RULE_1GB
                     `RULE_27:
                     begin: BYTE_ALIGN_1GB
                        mask_addr[i]  = 32'hF000_0000;
                        start_addr[i] = pmp_addr_i[i] & mask_addr[i];
                        stop_addr[i]  = pmp_addr_i[i];
                     end
      `endif



      `ifdef EN_NAPOT_RULE_2GB
                     `RULE_28:
                     begin: BYTE_ALIGN_2GB
                        mask_addr[i]  = 32'hE000_0000;
                        start_addr[i] = pmp_addr_i[i] & mask_addr[i];
                        stop_addr[i]  = pmp_addr_i[i];
                     end
      `endif

      `ifdef EN_NAPOT_RULE_4GB
                     `RULE_29:
                     begin: BYTE_ALIGN_4GB
                        mask_addr[i]  = 32'hC000_0000;
                        start_addr[i] = pmp_addr_i[i] & mask_addr[i];
                        stop_addr[i]  = pmp_addr_i[i];
                     end
      `endif

      `ifdef EN_NAPOT_RULE_8GB
                     `RULE_30:
                     begin: BYTE_ALIGN_8GB
                        mask_addr[i]  = 32'h8000_0000;
                        start_addr[i] = pmp_addr_i[i] & mask_addr[i];
                        stop_addr[i]  = pmp_addr_i[i];
                     end
      `endif

      `ifdef EN_NAPOT_RULE_16GB
                     `RULE_31:
                     begin: BYTE_ALIGN_16GB
                        mask_addr[i]  = 32'h0000_0000;
                        start_addr[i] = pmp_addr_i[i] & mask_addr[i];
                        stop_addr[i]  = pmp_addr_i[i];
                     end
      `endif
                     default:
                     begin: INVALID_RULE
                        EN_rule[i]    = 1'b0;
                        start_addr[i] = '0;
                        stop_addr[i]  = '0;
                     end

                  endcase


               end
`endif

            default:
            begin: DEFAULT_DISABLED
               EN_rule[i]    = 1'b0;
               start_addr[i] = '0;
               stop_addr[i]  = '0;
            end

            endcase
         end
      end
   endgenerate


   ///////////////////////////////////////////////////////////////////////////////////////////////
   // ██████╗ ██╗   ██╗██╗     ███████╗         ██████╗██╗  ██╗███████╗ ██████╗██╗  ██╗███████╗ //
   // ██╔══██╗██║   ██║██║     ██╔════╝        ██╔════╝██║  ██║██╔════╝██╔════╝██║ ██╔╝██╔════╝ //
   // ██████╔╝██║   ██║██║     █████╗          ██║     ███████║█████╗  ██║     █████╔╝ ███████╗ //
   // ██╔══██╗██║   ██║██║     ██╔══╝          ██║     ██╔══██║██╔══╝  ██║     ██╔═██╗ ╚════██║ //
   // ██║  ██║╚██████╔╝███████╗███████╗███████╗╚██████╗██║  ██║███████╗╚██████╗██║  ██╗███████║ //
   // ╚═╝  ╚═╝ ╚═════╝ ╚══════╝╚══════╝╚══════╝ ╚═════╝╚═╝  ╚═╝╚══════╝ ╚═════╝╚═╝  ╚═╝╚══════╝ //
   ///////////////////////////////////////////////////////////////////////////////////////////////




   always_comb
   begin
      for(j=0;j<N_PMP_ENTRIES;j++)
      begin

         if( EN_rule[j] & ((~data_we_i & R_rule[j]) | (data_we_i & W_rule[j])) )
         begin
             case(MODE_rule[j])
         `ifdef ENABLE_TOR
               2'b01:
               begin : TOR_CHECK_DATA
                      if ( ( data_addr_i[31:2] >= start_addr[j])  &&  ( data_addr_i[31:2] < stop_addr[j])  )
                      begin
                         data_match_region[j] = 1'b1;
                         `ifdef DEBUG_RULE $display("HIT on TOR RULE %d: [%8h] <= data_addr_i [%8h] <= [%8h], RULE=%2h, X=%b, W=%b, R=%d", j, (start_addr[j])>>2 , data_addr_i , (stop_addr[j])>>2, pmp_cfg_i[j][4:3], X_rule[j], W_rule[j], R_rule[j]); `endif
                      end
                      else
                      begin
                         data_match_region[j] = 1'b0;
                      end
               end
         `endif

               2'b10:
               begin : NA4_CHECK_DATA
                  if ( data_addr_i[31:2] == start_addr[j][29:0] )
                  begin
                     data_match_region[j] = 1'b1;
                     `ifdef DEBUG_RULE $display("HIT on NA4 RULE %d: [%8h] == [%8h] , RULE=%2h, X=%b, W=%b, R=%d", j, (start_addr[j])>>2 , data_addr_i , pmp_cfg_i[j][4:3], X_rule[j], W_rule[j], R_rule[j]); `endif
                  end
                  else
                  begin
                     data_match_region[j] = 1'b0;
                  end
               end

         `ifdef ENABLE_NAPOT
               2'b11:
               begin : NAPOT_CHECK_DATA
                     //$display("Checking NAPOT RULE [%d]: %8h, == %8h", j, data_addr_i[31:2] &  mask_addr[j][29:0], start_addr[j][29:0]);
                     if ( (data_addr_i[31:2] & mask_addr[j][29:0]) == start_addr[j][29:0] )
                     begin
                        data_match_region[j] = 1'b1;
                     end
                     else
                     begin
                        data_match_region[j] = 1'b0;
                        //$display("NO MACHING NAPOT: %8h, == %8h", (data_addr_i[31:2] &  mask_addr[j][29:0]), start_addr[j][29:0]);
                     end
               end
         `endif

               default:
               begin
                  data_match_region[j] = 1'b0;
               end
            endcase // MODE_rule[j]

         end
         else
         begin
               data_match_region[j] = 1'b0;
         end

      end
   end

   assign data_addr_o  = data_addr_i;

   always_comb
   begin
      if(pmp_privil_mode_i == PRIV_LVL_M)
      begin
         data_req_o   = data_req_i;
         data_gnt_o   = data_gnt_i;
         data_err_int   = 1'b0;

      end
      else
      begin
            if(|data_match_region == 1'b0)
            begin
               data_req_o   = 1'b0;
               data_err_int   = data_req_i;
               data_gnt_o   = 1'b0;
            end
            else
            begin
               data_req_o   =  data_req_i;
               data_err_int =  1'b0;
               data_gnt_o   =  data_gnt_i;
            end
      end
   end


   enum logic {IDLE, GIVE_ERROR} data_err_state_q, data_err_state_n;

   always_comb
   begin
      data_err_o       = 1'b0;
      data_err_state_n = data_err_state_q;
      unique case(data_err_state_q)

         IDLE:
         begin
            if(data_err_int)
               data_err_state_n = GIVE_ERROR;
         end

         GIVE_ERROR:
         begin
            data_err_o = 1'b1;
            if(data_err_ack_i)
               data_err_state_n = IDLE;
         end
      endcase
   end


   always_ff @(posedge clk or negedge rst_n) begin
      if(~rst_n) begin
          data_err_state_q <= IDLE;
      end else begin
          data_err_state_q <= data_err_state_n;
      end
   end


   always_comb
   begin
      for(k=0;k<N_PMP_ENTRIES;k++)
      begin

         if(EN_rule[k] & X_rule[k])
         begin

             case(MODE_rule[k])
         `ifdef ENABLE_TOR
               2'b01:
               begin : TOR_CHECK
                      if ( ( instr_addr_i[31:2] >= start_addr[k])  &&  ( instr_addr_i[31:2] < stop_addr[k])  )
                      begin
                         instr_match_region[k] = 1'b1;
                         `ifdef DEBUG_RULE $display("HIT on TOR RULE %d: [%8h] <= data_addr_i [%8h] <= [%8h], RULE=%2h, X=%b, W=%b, R=%d", k, (start_addr[k])>>2 , data_addr_i , (stop_addr[k])>>2, pmp_cfg_i[k][4:3], X_rule[k], W_rule[k], R_rule[k]); `endif
                      end
                      else
                      begin
                         instr_match_region[k] = 1'b0;
                      end
               end
         `endif

               2'b10:
               begin : NA4_CHECK
                  if ( instr_addr_i[31:2] == start_addr[k][29:0] )
                  begin
                     instr_match_region[k] = 1'b1;
                     `ifdef DEBUG_RULE $display("HIT on NA4 RULE %d: [%8h] == [%8h] , RULE=%2h, X=%b, W=%b, R=%d", k, (start_addr[k])>>2 , data_addr_i , pmp_cfg_i[k][4:3], X_rule[k], W_rule[k], R_rule[k]); `endif
                  end
                  else
                  begin
                     instr_match_region[k] = 1'b0;
                  end
               end

         `ifdef ENABLE_NAPOT
               2'b11:
               begin
                     if ( (instr_addr_i[31:2] & mask_addr[k][29:0]) == start_addr[k][29:0] )
                     begin
                        instr_match_region[k] = 1'b1;
                     end
                     else
                     begin
                        instr_match_region[k] = 1'b0;
                     end
               end
         `endif

               default:
               begin
                  instr_match_region[k] = 1'b0;
               end
            endcase // MODE_rule[i]

/*             if ( ( instr_addr_i[31:2] >= start_addr[k])  &&  ( instr_addr_i[31:2] <= stop_addr[k])  )
             begin
                instr_match_region[k] = 1'b1;
             end
             else
             begin
                instr_match_region[k] = 1'b0;
             end*/
         end
         else
         begin
            instr_match_region[k] = 1'b0;
         end


      end
   end

   assign instr_addr_o  = instr_addr_i;

   always_comb
   begin
      if(pmp_privil_mode_i == PRIV_LVL_M)
      begin
         instr_req_o   = instr_req_i;
         instr_gnt_o   = instr_gnt_i;
         instr_err_o   = 1'b0;

      end
      else
      begin
            if(|instr_match_region == 1'b0)
            begin
               instr_req_o   = 1'b0;
               instr_err_o   = instr_req_i;
               instr_gnt_o   = 1'b0;
            end
            else
            begin
               instr_req_o   =  instr_req_i;
               instr_err_o   =  1'b0;
               instr_gnt_o   =  instr_gnt_i;
            end
      end
   end


endmodule
