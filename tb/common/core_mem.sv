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
    input logic clk_i,   // Clock
    input logic rst_ni,  // Asynchronous reset active low

     // Instruction memory/cache
    input  logic [63:0]              instr_if_address_i,
    input  logic                     instr_if_data_req_i,
    input  logic [3:0]               instr_if_data_be_i,
    output logic                     instr_if_data_gnt_o,
    output logic                     instr_if_data_rvalid_o,
    output logic [31:0]              instr_if_data_rdata_o,
    // Data memory/cache
    input  logic [11:0]              data_if_address_index_i,
    input  logic [43:0]              data_if_address_tag_i,
    input  logic [63:0]              data_if_data_wdata_i,
    input  logic                     data_if_data_req_i,
    input  logic                     data_if_data_we_i,
    input  logic [7:0]               data_if_data_be_i,
    input  logic                     data_if_kill_req_i,
    input  logic                     data_if_tag_valid_i,
    output logic                     data_if_data_gnt_o,
    output logic                     data_if_data_rvalid_o,
    output logic [63:0]              data_if_data_rdata_o
);
    // we always grant the access
    localparam ADDRESS_WIDTH = 16;

    logic [ADDRESS_WIDTH-1:0] instr_address;
    logic [2:0]               instr_address_offset_q;
    logic [63:0]              instr_data;
    // D$ Mock
    logic req, we;
    logic [7:0] be;
    logic [11:0] index;
    logic [63:0] wdata;
    logic [55:0] data_address;
    assign data_address = {data_if_address_tag_i, index[11:3]};

    // we always grant the request
    assign instr_if_data_gnt_o   = instr_if_data_req_i;
    assign instr_address         = instr_if_address_i[ADDRESS_WIDTH-1+3:3];
    // this is necessary as the interface to the dual port memory is 64 bit, but the fetch interface of the core is 32 bit
    assign instr_if_data_rdata_o = (instr_address_offset_q[2]) ? instr_data[63:32] : instr_data[31:0];

    dp_ram  #(
        .ADDR_WIDTH    ( ADDRESS_WIDTH                   ),
        .DATA_WIDTH    ( 64                              )
    ) ram_i (
        .clk           ( clk_i                           ),
        .en_a_i        ( 1'b1                            ),
        .addr_a_i      ( instr_address                   ),
        .wdata_a_i     (                                 ), // not connected
        .rdata_a_o     ( instr_data                      ),
        .we_a_i        ( 1'b0                            ), // r/o interface
        .be_a_i        (                                 ),
        // data RAM
        .en_b_i        ( req                             ),
        .addr_b_i      ( data_address[ADDRESS_WIDTH-1:0] ),
        .wdata_b_i     ( wdata                           ),
        .rdata_b_o     ( data_if_data_rdata_o),
        .we_b_i        ( we                              ),
        .be_b_i        ( be                              )
    );

    // ----------------------
    // DCache Mock Interface
    // ----------------------
    // give the grant immediately
    assign data_if_data_gnt_o = data_if_data_req_i;
    assign data_if_data_rvalid_o = req;

    always_ff @(posedge clk_i or negedge rst_ni) begin
        if(~rst_ni) begin
            req   <= '0;
            be    <= '0;
            we    <= '0;
            index <= '0;
            wdata <= '0;
        end else begin
            req   <= data_if_data_req_i;
            be    <= data_if_data_be_i;
            we    <= data_if_data_we_i;
            index <= data_if_address_index_i;
            wdata <= data_if_data_wdata_i;
        end
    end

    // Output the rvalid one cycle later, together with the rdata
    always_ff @(posedge clk_i or negedge rst_ni) begin : proc_
        if(~rst_ni) begin
            instr_if_data_rvalid_o <= 1'b0;
            instr_address_offset_q <= 'b0;
        end else begin
            instr_if_data_rvalid_o <= instr_if_data_req_i;
            instr_address_offset_q <= instr_if_address_i[2:0];
        end
    end
endmodule