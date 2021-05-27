// Copyright (c) 2018 ETH Zurich, University of Bologna
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
// Author: Michael Schaffner <schaffner@iis.ee.ethz.ch>, ETH Zurich
// Date: 15.08.2018
// Description:
//

//////////////////////////////////////////////////////////////////////////////
// use to ensure proper ATI timing
///////////////////////////////////////////////////////////////////////////////

`define APPL_ACQ_WAIT #(ACQ_DEL-APPL_DEL);

`define WAIT_CYC(CLK, N)            \
repeat(N) @(posedge(CLK));

`define WAIT(CLK, SIG)              \
do begin                            \
    @(posedge(CLK));                \
end while(SIG == 1'b0);

`define WAIT_SIG(CLK,SIG)           \
do begin                            \
    @(posedge(CLK));                \
end while(SIG == 1'b0);

`define APPL_WAIT_COMB_SIG(CLK,SIG) \
`APPL_ACQ_WAIT                      \
while(SIG == 1'b0) begin            \
    @(posedge(CLK));                \
    #(ACQ_DEL);                     \
end

`define APPL_WAIT_SIG(CLK,SIG)      \
do begin                            \
    @(posedge(CLK));                \
    #(APPL_DEL);                    \
end while(SIG == 1'b0);

`define ACQ_WAIT_SIG(CLK,SIG)       \
do begin                            \
    @(posedge(CLK));                \
    #(ACQ_DEL);                     \
end while(SIG == 1'b0);


`define APPL_WAIT_CYC(CLK, N)       \
repeat(N) @(posedge(CLK));          \
#(tb_pkg::APPL_DEL);

`define ACQ_WAIT_CYC(CLK, N)        \
repeat(N) @(posedge(CLK));          \
#(tb_pkg::ACQ_DEL);

