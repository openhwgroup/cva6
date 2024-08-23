//-----------------------------------------------------------------------------
// Copyright 2024 Robert Bosch GmbH
//
// SPDX-License-Identifier: SHL-0.51
//
// Original Author: Coralie Allioux - Robert Bosch France SAS
//-----------------------------------------------------------------------------

package ahb_pkg;

  localparam AHBSizeWidth = 3;
  localparam AHBTransWidth = 2;
  localparam AHBBurstWidth = 3;
  localparam AHBProtWidth = 4;

  typedef logic [AHBSizeWidth-1:0] size_t;
  typedef logic [AHBTransWidth-1:0] trans_t;
  typedef logic [AHBBurstWidth-1:0] burst_t;
  typedef logic [AHBProtWidth-1:0] prot_t;

  // htrans values
  typedef enum logic [AHBTransWidth-1:0] {
    AHB_TRANS_IDLE,
    AHB_TRANS_BUSY,
    AHB_TRANS_NONSEQ,
    AHB_TRANS_SEQ
  } ahb_trans_e;

endpackage
