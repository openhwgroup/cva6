// Author: Florian Zaruba, ETH Zurich
// Date: 24.4.2017
// Description: FIFO interface
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
`ifndef FIFO_IF_SV
`define FIFO_IF_SV
interface fifo_if #(parameter type dtype = logic[7:0])
                   (input clk);

   wire   full;
   wire   empty;
   dtype  wdata;
   wire   push;
   dtype  rdata;
   wire   pop;

   clocking mck @(posedge clk);
        input  full, empty, rdata;
        output  wdata, push, pop;
   endclocking

   clocking sck @(posedge clk);
        input  wdata, push, pop;
        output full, empty, rdata;
   endclocking

   clocking pck @(posedge clk);
        input  wdata, push, pop, full, empty, rdata;
   endclocking

endinterface
`endif