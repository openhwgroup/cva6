//-----------------------------------------------------------------------------
// Copyright 2024 Robert Bosch GmbH
//
// SPDX-License-Identifier: SHL-0.51
//
// Original Author: Coralie Allioux - Robert Bosch France SAS
//-----------------------------------------------------------------------------

package scratchpad_pkg;

  // ----------------------
  // Instruction Scratchpad Mode
  // ----------------------
  typedef enum logic {
    ISCR_MODE_FUNCTIONAL,
    ISCR_MODE_PRELOAD
  } iscr_mode_t;

  // ----------------------
  // Arbit values
  // ----------------------
  localparam DSCR_ARBIT_NUM_IN = 3;
  localparam ISCR_ARBIT_NUM_IN = 4;

  localparam logic [$clog2(ISCR_ARBIT_NUM_IN)-1:0] ISCR_ARBIT_LOAD = 2'b00;
  localparam logic [$clog2(ISCR_ARBIT_NUM_IN)-1:0] ISCR_ARBIT_STORE = 2'b01;
  localparam logic [$clog2(ISCR_ARBIT_NUM_IN)-1:0] ISCR_ARBIT_AHB = 2'b10;
  localparam logic [$clog2(ISCR_ARBIT_NUM_IN)-1:0] ISCR_ARBIT_FRONTEND = 2'b11;

  localparam logic [$clog2(DSCR_ARBIT_NUM_IN)-1:0] DSCR_ARBIT_LOAD = 2'b00;
  localparam logic [$clog2(DSCR_ARBIT_NUM_IN)-1:0] DSCR_ARBIT_STORE = 2'b01;
  localparam logic [$clog2(DSCR_ARBIT_NUM_IN)-1:0] DSCR_ARBIT_AHB = 2'b10;

endpackage
