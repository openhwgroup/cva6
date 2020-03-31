// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Author: Florian Zaruba, ETH Zurich
// Date: 23.05.2017
// Description: Load Store Unit, handles address calculation and memory interface signals

module core_mem #(
        parameter logic [63:0] DRAM_BASE = 64'h80000000
    )(
    input logic                      clk_i,   // Clock
    input logic                      rst_ni,  // Asynchronous reset active low
    // Data memory/cache
    input  logic [63:0]              data_if_address_i,
    input  logic                     data_if_data_req_i,
    input  logic [7:0]               data_if_data_be_i,
    output logic                     data_if_data_rvalid_o,
    output logic [63:0]              data_if_data_rdata_o,
    input  logic [63:0]              data_if_data_wdata_i,
    input  logic                     data_if_data_we_i
);
    // we always grant the access
    localparam ADDRESS_WIDTH = 24;

    logic [63:0] fetch_data_ram, fetch_data_rom;

    logic [63:0] data_address_q;
    logic [63:0] data_ram, data_rom;

    // look at the address of the previous cycle to determine what to return
    assign data_if_data_rdata_o = (data_address_q >= DRAM_BASE) ? data_ram : data_rom;

    dp_ram  #(
        .ADDR_WIDTH    ( ADDRESS_WIDTH                                      ),
        .DATA_WIDTH    ( 64                                                 )
    ) ram_i (
        .clk           ( clk_i                                              ),
        .en_a_i        ( 1'b0                                               ),
        .addr_a_i      (                                                    ),
        .wdata_a_i     (                                                    ), // not connected
        .rdata_a_o     (                                                    ),
        .we_a_i        ( 1'b0                                               ), // r/o interface
        .be_a_i        (                                                    ),
        // data RAM
        .en_b_i        ( data_if_data_req_i                                 ),
        .addr_b_i      ( data_if_address_i[ADDRESS_WIDTH-1+3:3]             ),
        .wdata_b_i     ( data_if_data_wdata_i                               ),
        .rdata_b_o     ( data_ram                                           ),
        .we_b_i        ( ((data_if_address_i >= DRAM_BASE) ? data_if_data_we_i : 1'b0) ),
        .be_b_i        ( data_if_data_be_i                                  )
    );

    boot_rom data_boot_rom_i (
        .clk_i     ( clk_i                        ),
        .rst_ni    ( rst_ni                       ),
        .address_i ( data_address_q               ),
        .data_o    ( data_rom                     )
    );

    // Output the rvalid one cycle later, together with the rdata
    always_ff @(posedge clk_i or negedge rst_ni) begin : proc_
        if (~rst_ni) begin
            data_if_data_rvalid_o  <= 1'b0;
            data_address_q         <= '0;
        end else begin
            data_if_data_rvalid_o  <= data_if_data_req_i;
            data_address_q         <= data_if_address_i;
        end
    end
endmodule
