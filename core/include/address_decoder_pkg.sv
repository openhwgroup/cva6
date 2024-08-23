//-----------------------------------------------------------------------------
// Copyright 2024 Robert Bosch GmbH
//
// SPDX-License-Identifier: SHL-0.51
//
// Original Author: Coralie Allioux - Robert Bosch France SAS
//-----------------------------------------------------------------------------

package address_decoder_pkg;

  // ----------------------
  // Address Decoder Mode
  // ----------------------

  localparam DECODER_MODE_WIDTH = 2;
  typedef enum logic [DECODER_MODE_WIDTH-1:0] {
    DECODER_MODE_CACHE,
    DECODER_MODE_DSCR,
    DECODER_MODE_ISCR,
    DECODER_MODE_AHB_PERIPH
  } addr_dec_mode_e;

endpackage
