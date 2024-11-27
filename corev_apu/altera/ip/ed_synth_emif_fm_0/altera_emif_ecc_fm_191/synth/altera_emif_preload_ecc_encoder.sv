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


///////////////////////////////////////////////////////////////////////////////
// This module is used for simulation memory preloading to append ECC bits
// to the preload data
//
///////////////////////////////////////////////////////////////////////////////

`timescale 1 ns / 1 ps

module altera_emif_preload_ecc_encoder #
(
   parameter DIAG_USE_ABSTRACT_PHY                  = 0,
   parameter DIAG_SIM_MEMORY_PRELOAD_ECC_FILE       = "",
   parameter DIAG_SIM_MEMORY_PRELOAD_MEM_FILE       = "",
   parameter DIAG_SIM_MEMORY_PRELOAD_ABPHY_FILE     = "",
   parameter CTRL_AMM_ADDRESS_WIDTH                 = 1,
   parameter CTRL_AMM_DATA_WIDTH                    = 1,
   parameter MEM_DQ_WIDTH                           = 1,

   parameter USE_AVL_BYTEEN                         = 0,
   parameter CFG_ADDR_ENCODE_ENABLED                = 0,
   parameter CFG_PORT_WIDTH_ECC_CODE_OVERWRITE      = 1
)
(
   emif_usr_clk,
   cfg_ecc_code_overwrite
);

   function automatic integer ceil_log2;
      input integer value;
      begin
         value = value - 1;
         for (ceil_log2 = 0; value > 0; ceil_log2 = ceil_log2 + 1)
            value = value >> 1;
      end
   endfunction

   localparam OUTPUT_FILE                           = (DIAG_USE_ABSTRACT_PHY) ? DIAG_SIM_MEMORY_PRELOAD_ABPHY_FILE : (
                                                                                DIAG_SIM_MEMORY_PRELOAD_MEM_FILE );
   localparam INT_MEM_DQ_WIDTH                      = MEM_DQ_WIDTH - 8;
   localparam BYTEEN_WIDTH                          = INT_MEM_DQ_WIDTH / 8;
   localparam BYTEEN_W_ECC_WIDTH                    = MEM_DQ_WIDTH / 8;
   localparam NUM_DQ_BURSTS                         = CTRL_AMM_DATA_WIDTH / INT_MEM_DQ_WIDTH;
   localparam ADDRESS_WIDTH                         = CTRL_AMM_ADDRESS_WIDTH + ceil_log2(NUM_DQ_BURSTS);

   input                                                  emif_usr_clk;
   input  [CFG_PORT_WIDTH_ECC_CODE_OVERWRITE     - 1 : 0] cfg_ecc_code_overwrite;

   // synthesis translate_off

   logic                                                  preload_ready;
   logic                                                  preload_done;

   function automatic void check_preload_ready ();
      integer                             fd;
      string                              filename;
      string                              line;

      filename = DIAG_SIM_MEMORY_PRELOAD_ECC_FILE;
      fd = $fopen(filename, "r");
      if (fd != 0 && $fgets(line, fd)) begin
         preload_ready = '1;
      end
      $fclose(fd);
   endfunction

   task automatic encode_ecc_to_addr_data (
      input   [ADDRESS_WIDTH - 1:0]    address,
      input   [INT_MEM_DQ_WIDTH - 1:0] data,
      output  [MEM_DQ_WIDTH - 1:0]     ecc_data
   );


      $fatal(1, "CFG_ADDR_ENCODE_ENABLED = 1 - Feature not supported for simulation memory preload!");
   endtask

   task automatic encode_ecc_to_data (
      input   [INT_MEM_DQ_WIDTH - 1:0] data,
      output  [MEM_DQ_WIDTH - 1:0]     ecc_data
   );
      logic [63:0]  data_input;
      logic [71:0]  data_output;

      logic [63:0]  data_wire;
	   logic [34:0]  parity_01_wire;
	   logic [17:0]  parity_02_wire;
	   logic [ 8:0]  parity_03_wire;
	   logic [ 3:0]  parity_04_wire;
	   logic [ 1:0]  parity_05_wire;
	   logic [30:0]  parity_06_wire;
	   logic [ 6:0]  parity_07_wire;
	   logic [70:0]  parity_final_wire;
	   logic [71:0]  q_wire;


      if (INT_MEM_DQ_WIDTH < 64)
         data_input = {{(64 - INT_MEM_DQ_WIDTH){1'b0}}, data};
      else
         data_input = data[63:0];

	   data_wire             = data_input;

	   parity_01_wire[0]     = data_wire[0];
	   parity_01_wire[1]     = (data_wire[1] ^ parity_01_wire[0]);
	   parity_01_wire[2]     = (data_wire[3] ^ parity_01_wire[1]);
	   parity_01_wire[3]     = (data_wire[4] ^ parity_01_wire[2]);
	   parity_01_wire[4]     = (data_wire[6] ^ parity_01_wire[3]);
	   parity_01_wire[5]     = (data_wire[8] ^ parity_01_wire[4]);
	   parity_01_wire[6]     = (data_wire[10] ^ parity_01_wire[5]);
	   parity_01_wire[7]     = (data_wire[11] ^ parity_01_wire[6]);
	   parity_01_wire[8]     = (data_wire[13] ^ parity_01_wire[7]);
	   parity_01_wire[9]     = (data_wire[15] ^ parity_01_wire[8]);
	   parity_01_wire[10]    = (data_wire[17] ^ parity_01_wire[9]);
	   parity_01_wire[11]    = (data_wire[19] ^ parity_01_wire[10]);
	   parity_01_wire[12]    = (data_wire[21] ^ parity_01_wire[11]);
	   parity_01_wire[13]    = (data_wire[23] ^ parity_01_wire[12]);
	   parity_01_wire[14]    = (data_wire[25] ^ parity_01_wire[13]);
	   parity_01_wire[15]    = (data_wire[26] ^ parity_01_wire[14]);
	   parity_01_wire[16]    = (data_wire[28] ^ parity_01_wire[15]);
	   parity_01_wire[17]    = (data_wire[30] ^ parity_01_wire[16]);
	   parity_01_wire[18]    = (data_wire[32] ^ parity_01_wire[17]);
	   parity_01_wire[19]    = (data_wire[34] ^ parity_01_wire[18]);
	   parity_01_wire[20]    = (data_wire[36] ^ parity_01_wire[19]);
	   parity_01_wire[21]    = (data_wire[38] ^ parity_01_wire[20]);
	   parity_01_wire[22]    = (data_wire[40] ^ parity_01_wire[21]);
	   parity_01_wire[23]    = (data_wire[42] ^ parity_01_wire[22]);
	   parity_01_wire[24]    = (data_wire[44] ^ parity_01_wire[23]);
	   parity_01_wire[25]    = (data_wire[46] ^ parity_01_wire[24]);
	   parity_01_wire[26]    = (data_wire[48] ^ parity_01_wire[25]);
	   parity_01_wire[27]    = (data_wire[50] ^ parity_01_wire[26]);
	   parity_01_wire[28]    = (data_wire[52] ^ parity_01_wire[27]);
	   parity_01_wire[29]    = (data_wire[54] ^ parity_01_wire[28]);
	   parity_01_wire[30]    = (data_wire[56] ^ parity_01_wire[29]);
	   parity_01_wire[31]    = (data_wire[57] ^ parity_01_wire[30]);
	   parity_01_wire[32]    = (data_wire[59] ^ parity_01_wire[31]);
	   parity_01_wire[33]    = (data_wire[61] ^ parity_01_wire[32]);
	   parity_01_wire[34]    = (data_wire[63] ^ parity_01_wire[33]);

      parity_02_wire[0]     = data_wire[0];
      parity_02_wire[1]     = ((data_wire[2] ^ data_wire[3]) ^ parity_02_wire[0]);
      parity_02_wire[2]     = ((data_wire[5] ^ data_wire[6]) ^ parity_02_wire[1]);
      parity_02_wire[3]     = ((data_wire[9] ^ data_wire[10]) ^ parity_02_wire[2]);
      parity_02_wire[4]     = ((data_wire[12] ^ data_wire[13]) ^ parity_02_wire[3]);
      parity_02_wire[5]     = ((data_wire[16] ^ data_wire[17]) ^ parity_02_wire[4]);
      parity_02_wire[6]     = ((data_wire[20] ^ data_wire[21]) ^ parity_02_wire[5]);
      parity_02_wire[7]     = ((data_wire[24] ^ data_wire[25]) ^ parity_02_wire[6]);
      parity_02_wire[8]     = ((data_wire[27] ^ data_wire[28]) ^ parity_02_wire[7]);
      parity_02_wire[9]     = ((data_wire[31] ^ data_wire[32]) ^ parity_02_wire[8]);
      parity_02_wire[10]    = ((data_wire[35] ^ data_wire[36]) ^ parity_02_wire[9]);
      parity_02_wire[11]    = ((data_wire[39] ^ data_wire[40]) ^ parity_02_wire[10]);
      parity_02_wire[12]    = ((data_wire[43] ^ data_wire[44]) ^ parity_02_wire[11]);
      parity_02_wire[13]    = ((data_wire[47] ^ data_wire[48]) ^ parity_02_wire[12]);
      parity_02_wire[14]    = ((data_wire[51] ^ data_wire[52]) ^ parity_02_wire[13]);
      parity_02_wire[15]    = ((data_wire[55] ^ data_wire[56]) ^ parity_02_wire[14]);
      parity_02_wire[16]    = ((data_wire[58] ^ data_wire[59]) ^ parity_02_wire[15]);
      parity_02_wire[17]    = ((data_wire[62] ^ data_wire[63]) ^ parity_02_wire[16]);

	   parity_03_wire[0]     = ((data_wire[1] ^ data_wire[2]) ^ data_wire[3]);
	   parity_03_wire[1]     = ((((data_wire[7] ^ data_wire[8]) ^ data_wire[9]) ^ data_wire[10]) ^ parity_03_wire[0]);
	   parity_03_wire[2]     = ((((data_wire[14] ^ data_wire[15]) ^ data_wire[16]) ^ data_wire[17]) ^ parity_03_wire[1]);
	   parity_03_wire[3]     = ((((data_wire[22] ^ data_wire[23]) ^ data_wire[24]) ^ data_wire[25]) ^ parity_03_wire[2]);
	   parity_03_wire[4]     = ((((data_wire[29] ^ data_wire[30]) ^ data_wire[31]) ^ data_wire[32]) ^ parity_03_wire[3]);
	   parity_03_wire[5]     = ((((data_wire[37] ^ data_wire[38]) ^ data_wire[39]) ^ data_wire[40]) ^ parity_03_wire[4]);
	   parity_03_wire[6]     = ((((data_wire[45] ^ data_wire[46]) ^ data_wire[47]) ^ data_wire[48]) ^ parity_03_wire[5]);
	   parity_03_wire[7]     = ((((data_wire[53] ^ data_wire[54]) ^ data_wire[55]) ^ data_wire[56]) ^ parity_03_wire[6]);
	   parity_03_wire[8]     = ((((data_wire[60] ^ data_wire[61]) ^ data_wire[62]) ^ data_wire[63]) ^ parity_03_wire[7]);

      parity_04_wire[0]     = ((((((data_wire[4] ^ data_wire[5]) ^ data_wire[6]) ^ data_wire[7]) ^ data_wire[8]) ^ data_wire[9]) ^ data_wire[10]);
	   parity_04_wire[1]     = ((((((((data_wire[18] ^ data_wire[19]) ^ data_wire[20]) ^ data_wire[21]) ^ data_wire[22]) ^ data_wire[23]) ^ data_wire[24]) ^ data_wire[25]) ^ parity_04_wire[0]);
	   parity_04_wire[2]     = ((((((((data_wire[33] ^ data_wire[34]) ^ data_wire[35]) ^ data_wire[36]) ^ data_wire[37]) ^ data_wire[38]) ^ data_wire[39]) ^ data_wire[40]) ^ parity_04_wire[1]);
	   parity_04_wire[3]     = ((((((((data_wire[49] ^ data_wire[50]) ^ data_wire[51]) ^ data_wire[52]) ^ data_wire[53]) ^ data_wire[54]) ^ data_wire[55]) ^ data_wire[56]) ^ parity_04_wire[2]);

	   parity_05_wire[0]     = ((((((((((((((data_wire[11] ^ data_wire[12]) ^ data_wire[13]) ^ data_wire[14]) ^ data_wire[15]) ^ data_wire[16]) ^ data_wire[17]) ^ data_wire[18]) ^ data_wire[19]) ^ data_wire[20]) ^ data_wire[21]) ^ data_wire[22]) ^ data_wire[23]) ^ data_wire[24]) ^ data_wire[25]);
	   parity_05_wire[1]     = ((((((((((((((((data_wire[41] ^ data_wire[42]) ^ data_wire[43]) ^ data_wire[44]) ^ data_wire[45]) ^ data_wire[46]) ^ data_wire[47]) ^ data_wire[48]) ^ data_wire[49]) ^ data_wire[50]) ^ data_wire[51]) ^ data_wire[52]) ^ data_wire[53]) ^ data_wire[54]) ^ data_wire[55]) ^ data_wire[56]) ^ parity_05_wire[0]);

      parity_06_wire[0]     = data_wire[26];
      parity_06_wire[1]     = (data_wire[27] ^ parity_06_wire[0]);
      parity_06_wire[2]     = (data_wire[28] ^ parity_06_wire[1]);
      parity_06_wire[3]     = (data_wire[29] ^ parity_06_wire[2]);
      parity_06_wire[4]     = (data_wire[30] ^ parity_06_wire[3]);
      parity_06_wire[5]     = (data_wire[31] ^ parity_06_wire[4]);
      parity_06_wire[6]     = (data_wire[32] ^ parity_06_wire[5]);
      parity_06_wire[7]     = (data_wire[33] ^ parity_06_wire[6]);
      parity_06_wire[8]     = (data_wire[34] ^ parity_06_wire[7]);
      parity_06_wire[9]     = (data_wire[35] ^ parity_06_wire[8]);
      parity_06_wire[10]    = (data_wire[36] ^ parity_06_wire[9]);
      parity_06_wire[11]    = (data_wire[37] ^ parity_06_wire[10]);
      parity_06_wire[12]    = (data_wire[38] ^ parity_06_wire[11]);
      parity_06_wire[13]    = (data_wire[39] ^ parity_06_wire[12]);
      parity_06_wire[14]    = (data_wire[40] ^ parity_06_wire[13]);
      parity_06_wire[15]    = (data_wire[41] ^ parity_06_wire[14]);
      parity_06_wire[16]    = (data_wire[42] ^ parity_06_wire[15]);
      parity_06_wire[17]    = (data_wire[43] ^ parity_06_wire[16]);
      parity_06_wire[18]    = (data_wire[44] ^ parity_06_wire[17]);
      parity_06_wire[19]    = (data_wire[45] ^ parity_06_wire[18]);
      parity_06_wire[20]    = (data_wire[46] ^ parity_06_wire[19]);
      parity_06_wire[21]    = (data_wire[47] ^ parity_06_wire[20]);
      parity_06_wire[22]    = (data_wire[48] ^ parity_06_wire[21]);
      parity_06_wire[23]    = (data_wire[49] ^ parity_06_wire[22]);
      parity_06_wire[24]    = (data_wire[50] ^ parity_06_wire[23]);
      parity_06_wire[25]    = (data_wire[51] ^ parity_06_wire[24]);
      parity_06_wire[26]    = (data_wire[52] ^ parity_06_wire[25]);
      parity_06_wire[27]    = (data_wire[53] ^ parity_06_wire[26]);
      parity_06_wire[28]    = (data_wire[54] ^ parity_06_wire[27]);
      parity_06_wire[29]    = (data_wire[55] ^ parity_06_wire[28]);
      parity_06_wire[30]    = (data_wire[56] ^ parity_06_wire[29]);

      parity_07_wire[0]     = data_wire[57];
      parity_07_wire[1]     = (data_wire[58] ^ parity_07_wire[0]);
      parity_07_wire[2]     = (data_wire[59] ^ parity_07_wire[1]);
      parity_07_wire[3]     = (data_wire[60] ^ parity_07_wire[2]);
      parity_07_wire[4]     = (data_wire[61] ^ parity_07_wire[3]);
      parity_07_wire[5]     = (data_wire[62] ^ parity_07_wire[4]);
      parity_07_wire[6]     = (data_wire[63] ^ parity_07_wire[5]);

	   q_wire[63:0]          = data_wire;
	   q_wire[64]            = parity_01_wire[34];
	   q_wire[65]            = parity_02_wire[17];
	   q_wire[66]            = parity_03_wire[8];
	   q_wire[67]            = parity_04_wire[3];
	   q_wire[68]            = parity_05_wire[1];
	   q_wire[69]            = parity_06_wire[30];
	   q_wire[70]            = parity_07_wire[6];

      parity_final_wire[0]  = q_wire[0];
      parity_final_wire[1]  = (q_wire[1] ^ parity_final_wire[0]);
      parity_final_wire[2]  = (q_wire[2] ^ parity_final_wire[1]);
      parity_final_wire[3]  = (q_wire[3] ^ parity_final_wire[2]);
      parity_final_wire[4]  = (q_wire[4] ^ parity_final_wire[3]);
      parity_final_wire[5]  = (q_wire[5] ^ parity_final_wire[4]);
      parity_final_wire[6]  = (q_wire[6] ^ parity_final_wire[5]);
      parity_final_wire[7]  = (q_wire[7] ^ parity_final_wire[6]);
      parity_final_wire[8]  = (q_wire[8] ^ parity_final_wire[7]);
      parity_final_wire[9]  = (q_wire[9] ^ parity_final_wire[8]);
      parity_final_wire[10] = (q_wire[10] ^ parity_final_wire[9]);
      parity_final_wire[11] = (q_wire[11] ^ parity_final_wire[10]);
      parity_final_wire[12] = (q_wire[12] ^ parity_final_wire[11]);
      parity_final_wire[13] = (q_wire[13] ^ parity_final_wire[12]);
      parity_final_wire[14] = (q_wire[14] ^ parity_final_wire[13]);
      parity_final_wire[15] = (q_wire[15] ^ parity_final_wire[14]);
      parity_final_wire[16] = (q_wire[16] ^ parity_final_wire[15]);
      parity_final_wire[17] = (q_wire[17] ^ parity_final_wire[16]);
      parity_final_wire[18] = (q_wire[18] ^ parity_final_wire[17]);
      parity_final_wire[19] = (q_wire[19] ^ parity_final_wire[18]);
      parity_final_wire[20] = (q_wire[20] ^ parity_final_wire[19]);
      parity_final_wire[21] = (q_wire[21] ^ parity_final_wire[20]);
      parity_final_wire[22] = (q_wire[22] ^ parity_final_wire[21]);
      parity_final_wire[23] = (q_wire[23] ^ parity_final_wire[22]);
      parity_final_wire[24] = (q_wire[24] ^ parity_final_wire[23]);
      parity_final_wire[25] = (q_wire[25] ^ parity_final_wire[24]);
      parity_final_wire[26] = (q_wire[26] ^ parity_final_wire[25]);
      parity_final_wire[27] = (q_wire[27] ^ parity_final_wire[26]);
      parity_final_wire[28] = (q_wire[28] ^ parity_final_wire[27]);
      parity_final_wire[29] = (q_wire[29] ^ parity_final_wire[28]);
      parity_final_wire[30] = (q_wire[30] ^ parity_final_wire[29]);
      parity_final_wire[31] = (q_wire[31] ^ parity_final_wire[30]);
      parity_final_wire[32] = (q_wire[32] ^ parity_final_wire[31]);
      parity_final_wire[33] = (q_wire[33] ^ parity_final_wire[32]);
      parity_final_wire[34] = (q_wire[34] ^ parity_final_wire[33]);
      parity_final_wire[35] = (q_wire[35] ^ parity_final_wire[34]);
      parity_final_wire[36] = (q_wire[36] ^ parity_final_wire[35]);
      parity_final_wire[37] = (q_wire[37] ^ parity_final_wire[36]);
      parity_final_wire[38] = (q_wire[38] ^ parity_final_wire[37]);
      parity_final_wire[39] = (q_wire[39] ^ parity_final_wire[38]);
      parity_final_wire[40] = (q_wire[40] ^ parity_final_wire[39]);
      parity_final_wire[41] = (q_wire[41] ^ parity_final_wire[40]);
      parity_final_wire[42] = (q_wire[42] ^ parity_final_wire[41]);
      parity_final_wire[43] = (q_wire[43] ^ parity_final_wire[42]);
      parity_final_wire[44] = (q_wire[44] ^ parity_final_wire[43]);
      parity_final_wire[45] = (q_wire[45] ^ parity_final_wire[44]);
      parity_final_wire[46] = (q_wire[46] ^ parity_final_wire[45]);
      parity_final_wire[47] = (q_wire[47] ^ parity_final_wire[46]); 
      parity_final_wire[48] = (q_wire[48] ^ parity_final_wire[47]);
      parity_final_wire[49] = (q_wire[49] ^ parity_final_wire[48]);
      parity_final_wire[50] = (q_wire[50] ^ parity_final_wire[49]);
      parity_final_wire[51] = (q_wire[51] ^ parity_final_wire[50]);
      parity_final_wire[52] = (q_wire[52] ^ parity_final_wire[51]);
      parity_final_wire[53] = (q_wire[53] ^ parity_final_wire[52]);
      parity_final_wire[54] = (q_wire[54] ^ parity_final_wire[53]);
      parity_final_wire[55] = (q_wire[55] ^ parity_final_wire[54]);
      parity_final_wire[56] = (q_wire[56] ^ parity_final_wire[55]);
      parity_final_wire[57] = (q_wire[57] ^ parity_final_wire[56]);
      parity_final_wire[58] = (q_wire[58] ^ parity_final_wire[57]);
      parity_final_wire[59] = (q_wire[59] ^ parity_final_wire[58]);
      parity_final_wire[60] = (q_wire[60] ^ parity_final_wire[59]);
      parity_final_wire[61] = (q_wire[61] ^ parity_final_wire[60]);
      parity_final_wire[62] = (q_wire[62] ^ parity_final_wire[61]);
      parity_final_wire[63] = (q_wire[63] ^ parity_final_wire[62]);
      parity_final_wire[64] = (q_wire[64] ^ parity_final_wire[63]);
      parity_final_wire[65] = (q_wire[65] ^ parity_final_wire[64]);
      parity_final_wire[66] = (q_wire[66] ^ parity_final_wire[65]);
      parity_final_wire[67] = (q_wire[67] ^ parity_final_wire[66]);
      parity_final_wire[68] = (q_wire[68] ^ parity_final_wire[67]);
      parity_final_wire[69] = (q_wire[69] ^ parity_final_wire[68]);
      parity_final_wire[70] = (q_wire[70] ^ parity_final_wire[69]);

	   q_wire[71]            = parity_final_wire[70];

	   data_output           = q_wire;

	   if (INT_MEM_DQ_WIDTH < 64)
	      ecc_data = {data_output[71:64], data_output[INT_MEM_DQ_WIDTH-1:0]};
	   else
	      ecc_data = {data_output[71:64], data_output[63:0]};

   endtask

   task automatic preload_encode_ecc ();
      integer                                               fd_in;
      integer                                               fd_out;
      string                                                line;
      string                                                cs;
      string                                                c;
      string                                                bg;
      string                                                ba;
      string                                                row;
      string                                                col;

      logic   [ADDRESS_WIDTH - 1:0]                         addr;
      logic   [INT_MEM_DQ_WIDTH - 1:0]                      data;
      logic   [BYTEEN_WIDTH -1:0]                           byteen;
      logic   [MEM_DQ_WIDTH - 1:0]                          data_w_ecc;
      logic   [BYTEEN_W_ECC_WIDTH -1:0]                     byteen_w_ecc;

      fd_in = $fopen(DIAG_SIM_MEMORY_PRELOAD_ECC_FILE, "r");
      fd_out = $fopen(OUTPUT_FILE, "w");
      if (fd_in != 0 && fd_out != 0) begin
         while ($fgets(line, fd_in)) begin
            if ($sscanf(line, "ECC: CS=%s C=%s BG=%s BA=%s ROW=%s COL=%s ADDRESS=%h DATA=%h BYTEENABLE=%h", cs, c, bg, ba, row, col, addr, data, byteen) == 9) begin

               if (byteen != '1) begin
                  $fatal(1, "Error: When ECC is enabled, byte-enable must be enabled for all bytes in simulation memory preload data. Violation found in file %s at line %s",
                         DIAG_SIM_MEMORY_PRELOAD_ECC_FILE, line);
               end

               if (CFG_ADDR_ENCODE_ENABLED) begin
                  encode_ecc_to_addr_data(.address(addr), .data(data), .ecc_data(data_w_ecc));
               end else begin
                  encode_ecc_to_data(.data(data), .ecc_data(data_w_ecc));
               end
               byteen_w_ecc = {1'b1, byteen};

               if (DIAG_USE_ABSTRACT_PHY) begin
                  $fwrite(fd_out, "ABPHY: CS=%s C=%s BG=%s BA=%s ROW=%s COL=%s DATA=%h BYTEENABLE=%h\n", cs, c, bg, ba, row, col, data_w_ecc, byteen_w_ecc);
               end else begin
                  $fwrite(fd_out, "DDRX: CS=%s C=%s BG=%s BA=%s ROW=%s COL=%s DATA=%h BYTEENABLE=%h\n", cs, c, bg, ba, row, col, data_w_ecc, byteen_w_ecc);
               end
            end else begin
               $error(1, "Error: Missing information in file %s at line: %s", DIAG_SIM_MEMORY_PRELOAD_ECC_FILE, line);
            end
         end
      end else begin
         if (fd_in == 0) begin
            $error(1, "Error: Unable to open file %s for reading", DIAG_SIM_MEMORY_PRELOAD_ECC_FILE);
         end
         if (fd_out == 0) begin
            $error(1, "Error: Unable to open file %s for writing", OUTPUT_FILE);
         end
      end
      $fflush(fd_out);
      $fclose(fd_in);
      $fclose(fd_out);

   endtask

   initial begin
      integer fd_out;

      preload_ready = '0;
      preload_done = '0;

      fd_out = $fopen(OUTPUT_FILE, "w");
      $fclose(fd_out);
   end

   always @ (posedge emif_usr_clk) begin
      if (!preload_ready) begin
         check_preload_ready();
      end else if (!preload_done) begin
         preload_encode_ecc();
         preload_done = '1;
      end
   end

   // synthesis translate_on
endmodule
`ifdef QUESTA_INTEL_OEM
`pragma questa_oem_00 "sfv4CgBD2gRw66FfSic/D/DxyUF4ju6abSGjNZTz+XJ5wNcp1RmzgamT61rscvjMkkNKCYCGE4Hkry++3eL2fSJkmOtrYLQextJ2AFr2kX/6sa63SwNG1Dg8CndZgqHpcPsbI8J/52/6EA/5eQJiUNmwpEDzzugi2WpUBRBy4gGrSJ7A8zUzUrkHlWNSHE1mVOTkuXrL/BUqA6hBwwkS7qZD/J3TRyAu6L9p+9tB0EBMsHfgvgLrHe8UYp8Wl0pTxPxLOCWp7/jsVWNsp+Nt2lMmk4xxD1dSJfR8jxa81tihafHkJYGoi7tgC8DEETB4D8H/dYw2e8ihCN+19edns8PY+pZ5TA0RbFNmWaEK2vrbdNey7MubXJYNWNLKd0nOCTev7W5Up2V0gJn9+E4UHRoVBT7rUE7io/lL0G3UYmTV1mhrNeLkZPVusB612xgNAk0iraplNHhjzYMOEerIDetneUKw+2oLwjNJauKVmdS7jRvhlAWYWC7GQZDpF5D9vNLpk0WtZvsmXjZc7ahajIRlWH547JuDpZ6cM5rzCs5ISNBXGGYHSgF7bkVoHH8dWFMAizSUSZgnM5r6erReXPHajIW+tc4gdFi4H2U8mtqBTKyyp7r5k/moceTYU55tTxHKIC/nAgsj9+4uiN/LH8Z8IZSwXk2UAyod17BSp9sHGCR7qODmjQ1iaLaQTOw5+R0kB0kkHXWHBBm+aeEOT9Quivz8s9aGX/k58XrfU3OOcyoS5wdOVm9hM8HZcDf5ta3VqQpNpTyP0QVxJ8NYnGbmvRyXIbwA4OssXggw8OGW3T1Km2/zDUQUi8Ev4RWkE9pu/NyIoRV6xd/Tu65CWquQVff51lXxwzeBS2BlSIZyHIq653EYRkdEU0E1SChTAiVt/nZhUDbtL1/w03dJJAnCFx/oryRpm/6nwJzBYBzteqJ6eMGtPX38e1fj391ANUB2Xrlk6E8U3jhNqAL8OZT9a6gGiuhWJF/LEmqYE4REs5N/pdl+rz+My2q+z6UE"
`endif