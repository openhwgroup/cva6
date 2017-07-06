// Author: Pasquale Davide Schiavone <pschiavo@iis.ee.ethz.ch>
//
// Date: 05.06.2017
// Description: Ariane MULW
//
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
//

import ariane_pkg::*;

module multw
(
    input  logic [TRANS_ID_BITS-1:0] trans_id_i,
    input  logic                     mulw_valid_i,
    input  logic [63:0]              operand_a_i,
    input  logic [63:0]              operand_b_i,
    output logic [63:0]              result_o,
    output logic                     mulw_valid_o,
    output logic                     mulw_ready_o,
    output logic [TRANS_ID_BITS-1:0] mulw_trans_id_o
);
    // MULW is a single cycle instructions, hence it is always ready

    assign mulw_ready_o    = 1'b1;
    assign mulw_valid_o    = mulw_valid_i;
    assign mulw_trans_id_o = trans_id_i;

    logic signed [63:0] multw_result;

    assign multw_result = $signed(operand_a_i[31:0])*$signed(operand_b_i[31:0]);
    assign result_o     = $signed(multw_result[31:0]);

endmodule
