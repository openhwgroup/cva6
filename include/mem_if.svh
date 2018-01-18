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
// Author: Florian Zaruba, ETH Zurich
// Date: 3/18/2017
// Description: Generic memory interface used by the core.
//              The interface can be used in Master or Slave mode.

// Guard statement proposed by "Easier UVM" (doulos)
`ifndef MEM_IF_SV
`define MEM_IF_SV
interface mem_if
    #( parameter int ADDRESS_SIZE = 64,
       parameter int DATA_WIDTH = 64
    )
    (
        input clk
    );
        wire [ADDRESS_SIZE-1:0] address;           // Address for read/write request
        wire [DATA_WIDTH-1:0]   data_wdata;        // Data to be written
        wire                    data_req;          // Requests read data
        wire                    data_gnt;          // Request has been granted, signals can be changed as
                                                   // soon as request has been granted
        wire                    data_rvalid;       // Read data is valid
        wire [DATA_WIDTH-1:0]   data_rdata;        // Read data
        wire                    data_we;           // Write enable
        wire [DATA_WIDTH/8-1:0] data_be;           // Byte enable

        // super hack in assigning the wire a value
        // we need to keep all interface signals as wire as
        // the simulator does not now if this interface will be used
        // as an active or passive device
        // only helpful thread so far:
        // https://verificationacademy.com/forums/uvm/getting-multiply-driven-warnings-vsim-passive-agent

        // Memory interface configured as master
        // we are also synthesizing this interface
        `ifndef VERILATOR
        `ifndef SYNTHESIS
        clocking mck @(posedge clk);
            input   address, data_wdata, data_we, data_req, data_be;
            output  data_rvalid, data_rdata, data_gnt;
        endclocking
        // Memory interface configured as slave
        clocking sck @(posedge clk);
            output  address, data_wdata, data_we, data_req, data_be;
            input   data_rvalid, data_rdata, data_gnt;
        endclocking

        clocking pck @(posedge clk);
            // default input #1ns output #1ns;
            input  address, data_wdata, data_req, data_we, data_be,
                   data_gnt, data_rvalid, data_rdata;
        endclocking
        `endif
        `endif


        modport master (
            `ifndef VERILATOR
            `ifndef SYNTHESIS
            clocking mck,
            `endif
            `endif
            input   address, data_wdata, data_req, data_we, data_be,
            output  data_gnt, data_rvalid, data_rdata
        );
        modport slave  (
            `ifndef VERILATOR
            `ifndef SYNTHESIS
            clocking sck,
            `endif
            `endif
            output  address, data_wdata, data_req, data_we, data_be,
            input   data_gnt, data_rvalid, data_rdata
        );
        // modport Passive (clocking pck);

endinterface
`endif
