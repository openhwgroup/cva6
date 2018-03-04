//////////////////////////////////////////////////////////////////////
////                                                              ////
////  ps2_translation_table.v                                     ////
////                                                              ////
////  This file is part of the "ps2" project                      ////
////  https://github.com/freecores/ps2/verilog                    ////
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
//
// CVS Revision History
//
// $Log: not supported by cvs2svn $
// Revision 1.3  2003/06/02 17:13:22  simons
// resetall keyword removed. ifdef moved to a separated line.
//
// Revision 1.2  2002/04/09 13:21:15  mihad
// Added mouse interface and everything for its handling, cleaned up some unused code
//
// Revision 1.1.1.1  2002/02/18 16:16:56  mihad
// Initial project import - working
//
//

`include "ps2_defines.v"

// synopsys translate_off
//`include "timescale.v"
// synopsys translate_on

module ps2_translation_table
  (
   reset_i,
   clock_i,
   translate_i,
   code_i,
   code_o,
   address_i,
   data_i,
   we_i,
   re_i,
   data_o,
   rx_data_ready_i,
   rx_translated_data_ready_o,
   rx_read_i,
   rx_read_o,
   rx_released_i
   ) ;

   input wire reset_i,
         clock_i,
         translate_i ;

   input [7:0] code_i ;
   output [7:0] code_o ;
   input [7:0]  address_i ;
   input [7:0]  data_i ;
   input        wire we_i,
                re_i ;

   output [7:0] data_o ;

   input        wire rx_data_ready_i,
                rx_read_i ;

   output       wire rx_translated_data_ready_o ;
   output       wire rx_read_o ;

   input        wire rx_released_i ;

   wire         translation_table_write_enable  = we_i && (!translate_i || !rx_data_ready_i) ;
   wire [7:0]   translation_table_address = ((we_i || re_i) && (!rx_data_ready_i || !translate_i)) ? address_i : code_i ;
   wire         translation_table_enable        = we_i || re_i || (translate_i && rx_data_ready_i) ;

   reg          rx_translated_data_ready ;
   always@(posedge clock_i) // or posedge reset_i)
     begin
        if ( reset_i )
          rx_translated_data_ready <= #1 1'b0 ;
        else if ( rx_read_i || !translate_i )
          rx_translated_data_ready <= #1 1'b0 ;
        else
          rx_translated_data_ready <= #1 rx_data_ready_i ;
     end

`ifdef PS2_RAMB4
 `define PS2_RAM_SELECTED

   wire [7:0] ram_out ;
   RAMB4_S8 
 `ifdef SIM
     #("ignore",
       `PS2_TRANSLATION_TABLE_31_0,
       `PS2_TRANSLATION_TABLE_63_32,
       `PS2_TRANSLATION_TABLE_95_64,
       `PS2_TRANSLATION_TABLE_127_96,
       `PS2_TRANSLATION_TABLE_159_128,
       `PS2_TRANSLATION_TABLE_191_160,
       `PS2_TRANSLATION_TABLE_223_192,
       `PS2_TRANSLATION_TABLE_255_224)
 `endif
   ps2_ram
     (
      .DO   (ram_out),
      .ADDR ({1'b0, translation_table_address}),
      .DI   (data_i),
      .EN   (translation_table_enable),
      .CLK  (clock_i),
      .WE   (translation_table_write_enable),
      .RST  (reset_i)
      ) ;

`endif

`ifdef PS2_CONSTANTS_ROM
 `define PS2_RAM_SELECTED

   reg [32 * 8 - 1:0] ps2_32byte_constant ;
   reg [7:0]          ram_out ;

   always@(translation_table_address)
     begin
        case (translation_table_address[7:5])
          3'b000:ps2_32byte_constant = `PS2_TRANSLATION_TABLE_31_0    ;
          3'b001:ps2_32byte_constant = `PS2_TRANSLATION_TABLE_63_32   ;
          3'b010:ps2_32byte_constant = `PS2_TRANSLATION_TABLE_95_64   ;
          3'b011:ps2_32byte_constant = `PS2_TRANSLATION_TABLE_127_96  ;
          3'b100:ps2_32byte_constant = `PS2_TRANSLATION_TABLE_159_128 ;
          3'b101:ps2_32byte_constant = `PS2_TRANSLATION_TABLE_191_160 ;
          3'b110:ps2_32byte_constant = `PS2_TRANSLATION_TABLE_223_192 ;
          3'b111:ps2_32byte_constant = `PS2_TRANSLATION_TABLE_255_224 ;
        endcase
     end

   always@(posedge clock_i) // or posedge reset_i)
     begin
        if ( reset_i )
          ram_out <= #1 8'h0 ;
        else if ( translation_table_enable )
          begin:get_dat_out
             reg [7:0] bit_num ;
             
             bit_num = translation_table_address[4:0] << 3 ;

             repeat(8)
               begin
                  ram_out[bit_num % 8] <= #1 ps2_32byte_constant[bit_num] ;
                  bit_num = bit_num + 1'b1 ;
               end
          end
     end

`endif

`ifdef PS2_RAM_SELECTED
`else
 `define PS2_RAM_SELECTED

   reg [7:0] ps2_ram [0:255] ;
   reg [7:0] ram_out ;

   always@(posedge clock_i) // or posedge reset_i)
     begin
        if ( reset_i )
          ram_out <= #1 8'h0 ;
        else if ( translation_table_enable )
          ram_out <= #1 ps2_ram[translation_table_address] ;
     end

   always@(posedge clock_i)
     begin
        if ( translation_table_write_enable )
          ps2_ram[translation_table_address] <= #1 data_i ;
     end

   // synopsys translate_off
   initial
     begin:ps2_ram_init
        integer i ;
        reg [255:0] temp_init_val ;

        temp_init_val = `PS2_TRANSLATION_TABLE_31_0 ;

        for ( i = 0 ; i <= 31 ; i = i + 1 )
          begin
             ps2_ram[i] = temp_init_val[7:0] ;
             temp_init_val = temp_init_val >> 8 ;
          end

        temp_init_val = `PS2_TRANSLATION_TABLE_63_32 ;

        for ( i = 32 ; i <= 63 ; i = i + 1 )
          begin
             ps2_ram[i] = temp_init_val[7:0] ;
             temp_init_val = temp_init_val >> 8 ;
          end

        temp_init_val = `PS2_TRANSLATION_TABLE_95_64 ;

        for ( i = 64 ; i <= 95 ; i = i + 1 )
          begin
             ps2_ram[i] = temp_init_val[7:0] ;
             temp_init_val = temp_init_val >> 8 ;
          end

        temp_init_val = `PS2_TRANSLATION_TABLE_127_96 ;

        for ( i = 96 ; i <= 127 ; i = i + 1 )
          begin
             ps2_ram[i] = temp_init_val[7:0] ;
             temp_init_val = temp_init_val >> 8 ;
          end

        temp_init_val = `PS2_TRANSLATION_TABLE_159_128 ;

        for ( i = 128 ; i <= 159 ; i = i + 1 )
          begin
             ps2_ram[i] = temp_init_val[7:0] ;
             temp_init_val = temp_init_val >> 8 ;
          end

        temp_init_val = `PS2_TRANSLATION_TABLE_191_160 ;

        for ( i = 160 ; i <= 191 ; i = i + 1 )
          begin
             ps2_ram[i] = temp_init_val[7:0] ;
             temp_init_val = temp_init_val >> 8 ;
          end

        temp_init_val = `PS2_TRANSLATION_TABLE_223_192 ;

        for ( i = 192 ; i <= 223 ; i = i + 1 )
          begin
             ps2_ram[i] = temp_init_val[7:0] ;
             temp_init_val = temp_init_val >> 8 ;
          end

        temp_init_val = `PS2_TRANSLATION_TABLE_255_224 ;

        for ( i = 224 ; i <= 255 ; i = i + 1 )
          begin
             ps2_ram[i] = temp_init_val[7:0] ;
             temp_init_val = temp_init_val >> 8 ;
          end
     end

   // synopsys translate_on

`endif

   assign data_o = ram_out ;
   assign code_o = translate_i ? {(rx_released_i | ram_out[7]), ram_out[6:0]} : code_i ;
   assign rx_translated_data_ready_o = translate_i ? rx_translated_data_ready : rx_data_ready_i ;
   assign rx_read_o = rx_read_i ;

`undef PS2_RAM_SELECTED

endmodule //ps2_translation_table
