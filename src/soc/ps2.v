//////////////////////////////////////////////////////////////////////
////                                                              ////
////  ps2.v                                                       ////
////                                                              ////
////  This file is part of the "ps2" project                      ////
////  http://www.opencores.org/cores/ps2/                         ////
////                                                              ////
////  Author(s):                                                  ////
////      - mihad@opencores.org                                   ////
////      - Miha Dolenc                                           ////
////                                                              ////
////  All additional information is avaliable in the README.txt   ////
////  file.                                                       ////
////                                                              ////
////                                                              ////
//////////////////////////////////////////////////////////////////////
////                                                              ////
//// Copyright (C) 2000 Miha Dolenc, mihad@opencores.org          ////
////                                                              ////
//// This source file may be used and distributed without         ////
//// restriction provided that this copyright statement is not    ////
//// removed from the file and that any derivative work contains  ////
//// the original copyright notice and the associated disclaimer. ////
////                                                              ////
//// This source file is free software; you can redistribute it   ////
//// and/or modify it under the terms of the GNU Lesser General   ////
//// Public License as published by the Free Software Foundation; ////
//// either version 2.1 of the License, or (at your option) any   ////
//// later version.                                               ////
////                                                              ////
//// This source is distributed in the hope that it will be       ////
//// useful, but WITHOUT ANY WARRANTY; without even the implied   ////
//// warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR      ////
//// PURPOSE.  See the GNU Lesser General Public License for more ////
//// details.                                                     ////
////                                                              ////
//// You should have received a copy of the GNU Lesser General    ////
//// Public License along with this source; if not, download it   ////
//// from http://www.opencores.org/lgpl.shtml                     ////
////                                                              ////
//////////////////////////////////////////////////////////////////////

module ps2(clk, rst, rx_ascii_read, 
           PS2_K_CLK_IO, PS2_K_DATA_IO, PS2_M_CLK_IO, PS2_M_DATA_IO,
           ascii_code, ascii_data_ready, rx_translated_scan_code);

   input clk, rst;
   input rx_ascii_read;

   inout PS2_K_CLK_IO;
   inout PS2_K_DATA_IO;
   inout PS2_M_CLK_IO;
   inout PS2_M_DATA_IO;

   output ascii_data_ready;
   output [7:0] rx_translated_scan_code;
   output reg [6:0] ascii_code;
   reg [7:0]        kcode;

   wire             ps2_k_clk_en_o_ ;
   wire             ps2_k_data_en_o_ ;
   wire             ps2_k_clk_i ;
   wire             ps2_k_data_i ;

   wire             rx_released;
   wire [7:0]       rx_scan_code;
   wire             rx_scan_ready;
   reg [7:0]        tx_data;
   reg              tx_write;
   wire             tx_write_ack_o;
   wire             tx_error_no_keyboard_ack;
   reg              translate, shift, ctrl ;
   wire [15:0]      divide_reg = 13000;
   reg              ascii_data_ready, data_ready_dly;
   wire [7:0]       rx_translated_scan_code, rx_ascii_code;
   wire             rx_translated_data_ready, rx_ascii_data_ready;

   assign rx_ascii_code = ascii_code;
   assign rx_ascii_data_ready = ascii_data_ready;

`include "ascii_code.v"

   always @(posedge clk) // or posedge rst) // JRRK - does this need async ?
   if (rst)
     begin
        translate = 1;
        tx_write = 0;
        tx_data = 0;
        kcode = 0;
        shift = 0;
        ctrl = 0;
        ascii_data_ready = 0;
        ascii_code = 0;
        data_ready_dly <= 0;
     end
   else
     begin
        data_ready_dly <= rx_translated_data_ready;
        if (rx_ascii_read)
          ascii_data_ready = 0; 
        if (rx_translated_data_ready & ~data_ready_dly)
          begin
             kcode = 0;
             case(rx_translated_scan_code[6:0])
               7'H2A, 7'H36: shift = ~rx_translated_scan_code[7];
               7'H1D: ctrl = ~rx_translated_scan_code[7];
               default: kcode = ASCII_code(rx_translated_scan_code,shift|ctrl);
             endcase
             if (kcode && !rx_translated_scan_code[7])
               begin
                  if (ctrl && (kcode >= "A") && (kcode <= "]"))
                    begin
                       kcode = kcode & ~(7'H40);
                    end
                  ascii_code = kcode;
                  ascii_data_ready = 1;
               end
          end
     end

   IOBUF #(
           .DRIVE(12), // Specify the output drive strength
           .IOSTANDARD("DEFAULT"), // Specify the I/O standard
           .SLEW("SLOW") // Specify the output slew rate
           ) IOBUF_k_clk (
                          .O(ps2_k_clk_i),     // Buffer output
                          .IO(PS2_K_CLK_IO),   // Buffer inout port (connect directly to top-level port)
                          .I(ps2_k_clk_en_o_),     // Buffer input
                          .T(ps2_k_clk_en_o_)      // 3-state enable input 
                          );

   IOBUF #(
           .DRIVE(12), // Specify the output drive strength
           .IOSTANDARD("DEFAULT"), // Specify the I/O standard
           .SLEW("SLOW") // Specify the output slew rate
           ) IOBUF_k_data (
                           .O(ps2_k_data_i),     // Buffer output
                           .IO(PS2_K_DATA_IO),   // Buffer inout port (connect directly to top-level port)
                           .I(ps2_k_data_en_o_),     // Buffer input
                           .T(ps2_k_data_en_o_)      // 3-state enable input 
                           );

   ps2_keyboard key1(
                     .clock_i(clk),
                     .reset_i(rst),
                     .ps2_clk_en_o_(ps2_k_clk_en_o_),
                     .ps2_data_en_o_(ps2_k_data_en_o_),
                     .ps2_clk_i(ps2_k_clk_i),
                     .ps2_data_i(ps2_k_data_i),
                     .rx_released(rx_released),
                     .rx_scan_code(rx_scan_code),
                     .rx_data_ready(rx_scan_ready),       // rx_read_o
                     .rx_read(rx_scan_read),             // rx_read_ack_i
                     .tx_data(tx_data),
                     .tx_write(tx_write),
                     .tx_write_ack_o(tx_write_ack_o),
                     .tx_error_no_keyboard_ack(tx_error_no_keyboard_ack),
                     .translate(translate),
                     .divide_reg_i(divide_reg)
                     );

   ps2_translation_table i_ps2_translation_table
     (
      .reset_i                    (rst),
      .clock_i                    (clk),
      .translate_i                (translate),
      .code_i                     (rx_scan_code),
      .code_o                     (rx_translated_scan_code),
      .address_i                  (8'h00),
      .data_i                     (8'h00),
      .we_i                       (1'b0),
      .re_i                       (1'b0),
      .data_o                     (),
      .rx_data_ready_i            (rx_scan_ready),
      .rx_translated_data_ready_o (rx_translated_data_ready),
      .rx_read_i                  (rx_translated_data_ready),
      .rx_read_o                  (rx_scan_read),
      .rx_released_i              (rx_released)
      ) ;

   wire ps2_m_clk_en_o_ ;
   wire ps2_m_data_en_o_ ;
   wire ps2_m_clk_i ;
   wire ps2_m_data_i ;

   IOBUF #(
           .DRIVE(12), // Specify the output drive strength
           .IOSTANDARD("DEFAULT"), // Specify the I/O standard
           .SLEW("SLOW") // Specify the output slew rate
           ) IOBUF_m_clk (
                          .O(ps2_m_clk_i),     // Buffer output
                          .IO(PS2_M_CLK_IO),   // Buffer inout port (connect directly to top-level port)
                          .I(ps2_m_clk_en_o_),     // Buffer input
                          .T(ps2_m_clk_en_o_)      // 3-state enable input 
                          );

   IOBUF #(
           .DRIVE(12), // Specify the output drive strength
           .IOSTANDARD("DEFAULT"), // Specify the I/O standard
           .SLEW("SLOW") // Specify the output slew rate
           ) IOBUF_m_data (
                           .O(ps2_m_data_i),     // Buffer output
                           .IO(PS2_M_DATA_IO),   // Buffer inout port (connect directly to top-level port)
                           .I(ps2_m_data_en_o_),     // Buffer input
                           .T(ps2_m_data_en_o_)      // 3-state enable input 
                           );

endmodule
