//-----------------------------------------------------------------------------
// Copyright 2024 Robert Bosch GmbH
//
// SPDX-License-Identifier: SHL-0.51
//
// Original Author: Coralie Allioux - Robert Bosch France SAS
//-----------------------------------------------------------------------------

package ahb_pkg;

  localparam integer AHBSizeWidth = 3;
  localparam integer AHBTransWidth = 2;
  localparam integer AHBBurstWidth = 3;
  localparam integer AHBProtWidth  = 4;

  // htrans values
  localparam logic [AHBTransWidth-1:0] AhbTransIdle   = 2'b00;
  localparam logic [AHBTransWidth-1:0] AhbTransBusy   = 2'b01;
  localparam logic [AHBTransWidth-1:0] AhbTransNonseq = 2'b10;
  localparam logic [AHBTransWidth-1:0] AhbTransSeq    = 2'b11;

  // hburst values
  localparam logic [AHBBurstWidth-1:0] AhbBurstSingle = 3'b000;
  localparam logic [AHBBurstWidth-1:0] AhbBurstIncr   = 3'b001;
  localparam logic [AHBBurstWidth-1:0] AhbBurstWrap4  = 3'b010;
  localparam logic [AHBBurstWidth-1:0] AhbBurstIncr4  = 3'b011;
  localparam logic [AHBBurstWidth-1:0] AhbBurstWrap8  = 3'b100;
  localparam logic [AHBBurstWidth-1:0] AhbBurstIncr8  = 3'b101;
  localparam logic [AHBBurstWidth-1:0] AhbBurstWrap16 = 3'b110;
  localparam logic [AHBBurstWidth-1:0] AhbBurstIncr16 = 3'b111;

  // hsize values
  localparam logic [AHBSizeWidth-1:0] AhbSizeByte       = 3'b000;
  localparam logic [AHBSizeWidth-1:0] AhbSizeHalfword   = 3'b001;
  localparam logic [AHBSizeWidth-1:0] AhbSizeWord       = 3'b010;
  localparam logic [AHBSizeWidth-1:0] AhbSizeDoubleword = 3'b011;
  localparam logic [AHBSizeWidth-1:0] AhbSize4wordline  = 3'b100;
  localparam logic [AHBSizeWidth-1:0] AhbSize8wordline  = 3'b101;

  typedef logic [AHBSizeWidth-1:0]  size_t;
  typedef logic [AHBTransWidth-1:0] trans_t;
  typedef logic [AHBBurstWidth-1:0] burst_t;
  typedef logic [AHBProtWidth-1:0]  prot_t;

endpackage
