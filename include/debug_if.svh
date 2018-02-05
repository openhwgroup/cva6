// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the “License”); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an “AS IS” BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Author: Andreas Traber
// Date: 3/18/2017
// Description: Debug interface for memory mapped debug
//              The interface can be used in Master or Slave mode.

`ifndef DEBUG_IF__SV
`define DEBUG_IF__SV
interface debug_if
    #(
        parameter ADDR_WIDTH = 15
    );
      logic                  req;
      logic                  gnt;
      logic                  rvalid;
      logic [ADDR_WIDTH-1:0] addr;
      logic                  we;
      logic [63:0]           wdata;
      logic [63:0]           rdata;
      // Master Side
      //***************************************
      modport Master
      (
        output      req,  addr,   we, wdata,
        input       gnt,  rvalid,     rdata
      );
      // Slave Side
      //***************************************
      modport Slave
      (
        input       req,  addr,   we, wdata,
        output      gnt,  rvalid,     rdata
      );
endinterface
`endif
