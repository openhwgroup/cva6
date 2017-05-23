// Author: Florian Zaruba, ETH Zurich
// Date: 23.05.2017
// Description: Load Store Unit, handles address calculation and memory interface signals
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

module core_mem (
    input logic clk_i,    // Clock
    input logic rst_ni,  // Asynchronous reset active low

     // Instruction memory/cache
    input  logic [63:0]              instr_if_address_i,
    input  logic                     instr_if_data_req_i,
    input  logic [3:0]               instr_if_data_be_i,
    output logic                     instr_if_data_gnt_o,
    output logic                     instr_if_data_rvalid_o,
    output logic [31:0]              instr_if_data_rdata_o,
    // Data memory/cache
    input  logic [63:0]              data_if_address_i,
    input  logic [63:0]              data_if_data_wdata_i,
    input  logic                     data_if_data_req_i,
    input  logic                     data_if_data_we_i,
    input  logic [7:0]               data_if_data_be_i,
    input  logic [1:0]               data_if_tag_status_i,
    output logic                     data_if_data_gnt_o,
    output logic                     data_if_data_rvalid_o,
    output logic [63:0]              data_if_data_rdata_o
);

endmodule