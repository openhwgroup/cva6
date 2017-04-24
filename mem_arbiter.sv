// Author: Florian Zaruba, ETH Zurich
// Date: 24.4.2017
// Description: Arbitrates the memory ports
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
module mem_arbiter #(
        parameter int NR_PORTS = 3
    )
    (
    input logic                  clk_i,    // Clock
    input logic                  rst_ni,  // Asynchronous reset active low

    mem_if.Master [NR_PORTS-1:0] masters,
    mem_if.Slave                 slave
);

    // addressing read and write

    // results


endmodule