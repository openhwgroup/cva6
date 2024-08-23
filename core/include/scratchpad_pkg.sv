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

  typedef enum logic [$clog2(ISCR_ARBIT_NUM_IN)-1:0] {
    ISCR_ARBIT_LOAD,
    ISCR_ARBIT_STORE,
    ISCR_ARBIT_AHB,
    ISCR_ARBIT_FRONTEND
  } iscr_arbit_e;

  typedef enum logic [$clog2(DSCR_ARBIT_NUM_IN)-1:0] {
    DSCR_ARBIT_LOAD,
    DSCR_ARBIT_STORE,
    DSCR_ARBIT_AHB
  } dscr_arbit_e;

endpackage
