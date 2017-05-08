// Author: Florian Zaruba, ETH Zurich
// Date: 20.04.2017
// Description: PC generation stage
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

module pcgen (
    input  logic        clk_i,                    // Clock
    input  logic        rst_ni,                   // Asynchronous reset active low

    input  logic        flush_i,
    input  logic [63:0] pc_if_i,
    input  mispredict   mispredict_i,             // from controller signaling a mispredict -> update BTB
    // to IF
    output logic [63:0] branch_target_address_o,
    output logic        predict_taken_o,          // btb thinks we should take that branch
    output logic        is_branch_o               // to check if we mispredicted
);


    btb #(
        .NR_ENTRIES(64),
        .BITS_SATURATION_COUNTER(2)
    )
    btb_i
    (
        .vpc_i                   ( pc_if_i                 ),
        .misspredict_i           ( misspredict_i           ),
        .is_branch_o             ( is_branch_o             ),
        .predict_taken_o         ( predict_taken_o         ),
        .branch_target_address_o ( branch_target_address_o ),
        .*
    );


endmodule