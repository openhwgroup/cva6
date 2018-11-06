// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

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
