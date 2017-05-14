// Author: Florian Zaruba, ETH Zurich
// Date: 14.5.2017
// Description: Fetch FIFO interface
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
`ifndef FETCH_FIFO_IF_SV
`define FETCH_FIFO_IF_SV
import ariane_pkg::*;

interface fetch_fifo_if #(
        parameter type dtype = logic[7:0]
    )(
        input clk
    );

    wire                                flush;
    wire [$bits(branchpredict_sbe)-1:0] in_branch_predict;
    wire [63:0]                         in_addr;
    wire [31:0]                         in_rdata;
    wire                                in_valid;
    wire                                in_ready;
    wire [$bits(branchpredict_sbe)-1:0] out_branch_predict;
    wire [63:0]                         out_addr;
    wire [31:0]                         out_rdata;
    wire                                out_valid;
    wire                                out_ready;

   clocking mck @(posedge clk);
        input  in_ready, out_branch_predict, out_addr, out_rdata, out_valid;
        output flush, in_branch_predict, in_addr, in_rdata, in_valid, out_ready;
   endclocking

   clocking pck @(posedge clk);
        input  in_ready, out_branch_predict, out_addr, out_rdata, out_valid,
               flush, in_branch_predict, in_addr, in_rdata, in_valid, out_ready;
   endclocking

endinterface
`endif