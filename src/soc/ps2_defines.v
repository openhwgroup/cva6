//////////////////////////////////////////////////////////////////////
////                                                              ////
////  ps2_defines.v                                               ////
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
//
// CVS Revision History
//
// $Log: not supported by cvs2svn $
// Revision 1.4  2003/07/01 12:34:03  mihad
// Added an option to use constant values instead of RAM
// in the translation table.
//
// Revision 1.3  2002/04/09 13:21:15  mihad
// Added mouse interface and everything for its handling, cleaned up some unused code
//
// Revision 1.2  2002/02/18 16:33:08  mihad
// Changed defines for simulation to work without xilinx primitives
//
// Revision 1.1.1.1  2002/02/18 16:16:56  mihad
// Initial project import - working
//
//

//`define PS2_RAMB4
`define PS2_CONSTANTS_ROM

`define PS2_TRANSLATION_TABLE_31_0    256'h5b03111e1f2c71665a02101d702a386559290f3e40424464583c3b3d3f4143ff
`define PS2_TRANSLATION_TABLE_63_32   256'h5f0908162432726a5e071522233031695d061314212f39685c040512202d2e67
`define PS2_TRANSLATION_TABLE_95_64   256'h76632b751b1c363a6e620d1a7428736d610c19272635346c600a0b181725336b
`define PS2_TRANSLATION_TABLE_127_96  256'h544649374a514e574501484d4c5053526f7f7e474b7d4f7c7b0e7a7978775655
`define PS2_TRANSLATION_TABLE_159_128 256'h9f9e9d9c9b9a999897969594939291908f8e8d8c8b8a89888786855441828180
`define PS2_TRANSLATION_TABLE_191_160 256'hbfbebdbcbbbab9b8b7b6b5b4b3b2b1b0afaeadacabaaa9a8a7a6a5a4a3a2a1a0
`define PS2_TRANSLATION_TABLE_223_192 256'hdfdedddcdbdad9d8d7d6d5d4d3d2d1d0cfcecdcccbcac9c8c7c6c5c4c3c2c1c0
`define PS2_TRANSLATION_TABLE_255_224 256'hfffefdfcfbfaf9f8f7f6f5f4f3f2f1f0efeeedecebeae9e8e7e6e5e4e3e2e1e0

`define PS2_TIMER_60USEC_VALUE_PP 12  // Number of sys_clks for 60usec.
`define PS2_TIMER_60USEC_BITS_PP  4    // Number of bits needed for timer
`define PS2_TIMER_5USEC_VALUE_PP 500    // Number of sys_clks for debounce
`define PS2_TIMER_5USEC_BITS_PP 16       // Number of bits needed for timer

//`define PS2_AUX
