// Author: Andreas Traber, ACP
// Date: 3/18/2017
// Description: Debug interface for memory mapped debug
//              The interface can be used in Master or Slave mode.
//
// Copyright (C) 2017 ETH Zurich, University of Bologna
// All rights reserved.

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