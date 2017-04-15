// Author: Florian Zaruba, ETH Zurich
// Date: 3/18/2017
// Description: Generic memory interface used by the core.
//              The interface can be used in Master or Slave mode.
//
// Copyright (C) 2017 ETH Zurich, University of Bologna
// All rights reserved.

// Guard statement proposed by "Easier UVM" (doulos)
`ifndef MEM_IF__SV
`define MEM_IF__SV
interface mem_if
    #(
        parameter int ADDRESS_SIZE = 64
    );
        logic [ADDRESS_SIZE-1:0] address;           // Address for read/write request
        logic [31:0]             data_wdata;        // Data to be written
        logic                    data_req;          // Requests read data
        logic                    data_gnt;          // Request has been granted, signals can be changed as
                                                    // soon as request has been granted
        logic                    data_rvalid;       // Read data is valid
        logic [31:0]             data_rdata;        // Read data
        logic                    data_we;           // Write enable
        logic [3:0]              data_be;           // Byte enable
        // Memory interface configured as master
        modport Master
        (
            input   address, data_wdata, data_req, data_we, data_be,
            output  data_gnt, data_rvalid, data_rdata
        );
        // Memory interface configured as slave
        modport Slave
        (
            output  address, data_wdata, data_req, data_we, data_be,
            input   data_gnt, data_rvalid, data_rdata
        );
endinterface
`endif