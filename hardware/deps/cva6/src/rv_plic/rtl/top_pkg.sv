// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

package top_pkg;

localparam TL_AW=32;
localparam TL_DW=32;
localparam TL_AIW=8;    // a_source, d_source
localparam TL_DIW=1;    // d_sink
localparam TL_AUW=16;   // a_user
localparam TL_DUW=16;   // d_user
localparam TL_DBW=(TL_DW>>3);
localparam TL_SZW=$clog2($clog2(TL_DBW)+1);

endpackage
