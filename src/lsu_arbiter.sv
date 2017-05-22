// Author: Florian Zaruba, ETH Zurich
// Date: 22.05.2017
// Description: Arbitrates the LSU result port
//
// Copyright (C) 2017 ETH Zurich, University of Bologna
// All rights reserved.
//
// This code is under development and not yet released to the public.
// Until it is released, the code is under the copyright of ETH Zurich and
// the University of Bologna, and may contain confidential and/or unpublished
// work. Any reuse/redistribution is strictly forbidden without written
// permission from ETH Zurich.
//
// Bug fixes and contributions will eventually be released under the
// SolderPad open hardware license in the context of the PULP platform
// (http://www.pulp-platform.org), under the copyright of ETH Zurich and the
// University of Bologna.

import ariane_pkg::*;

module lsu_arbiter (
    input  logic                     clk_i,    // Clock
    input  logic                     rst_ni,   // Asynchronous reset active low
    input  logic                     flush_i,
    // Load Port
    input logic                      ld_valid_i,
    input logic                      ld_ready_i,
    input logic [TRANS_ID_BITS-1:0]  ld_trans_id_i,
    input logic [63:0]               ld_result_i,
    // Store Port
    input logic                      st_valid_i,
    input logic                      st_ready_i,
    input logic [TRANS_ID_BITS-1:0]  st_trans_id_i,
    input logic [63:0]               st_result_i,
    // Output Port
    output logic                     valid_o,
    output logic                     ready_o,
    output logic [TRANS_ID_BITS-1:0] trans_id_o,
    output logic [63:0]              result_o
);


endmodule