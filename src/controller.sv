// Author: Florian Zaruba, ETH Zurich
// Date: 08.05.2017
// Description: Flush controller
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

module controller (
    input  logic            clk_i,    // Clock
    input  logic            rst_ni,   // Asynchronous reset active low

    input  logic            flush_commit_i, // flush request from commit stage in
    input  logic            flush_csr_i,
    input  branchpredict    branchpredict_i
);

// flush on mispredict

// flush on exception
endmodule
