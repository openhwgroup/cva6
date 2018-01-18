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
// Date: 19.03.2017
// Description: Ariane Top-level module

import ariane_pkg::*;

import "DPI-C" function void write_uint64(input longint unsigned address, input longint unsigned data);
import "DPI-C" function longint unsigned read_uint64(input longint unsigned address);

module ariane_wrapped #(
        parameter logic [63:0] CACHE_START_ADDR  = 64'h4000_0000, // address on which to decide whether the request is cache-able or not
        parameter int unsigned AXI_ID_WIDTH      = 10,
        parameter int unsigned AXI_USER_WIDTH    = 1,
        parameter int unsigned AXI_ADDRESS_WIDTH = 64,
        parameter int unsigned AXI_DATA_WIDTH    = 64
    )(
        input  logic                           clk_i,
        input  logic                           rst_ni,
        input  logic                           test_en_i,     // enable all clock gates for testing

        output logic                           flush_icache_o, // request to flush icache
        // CPU Control Signals
        input  logic                           fetch_enable_i,
        output logic                           core_busy_o,
        input  logic                           l1_icache_miss_i,

        // Core ID, Cluster ID and boot address are considered more or less static
        input  logic [63:0]                    boot_addr_i,
        input  logic [ 3:0]                    core_id_i,
        input  logic [ 5:0]                    cluster_id_i,
        // Interrupt inputs
        input  logic [1:0]                     irq_i,        // level sensitive IR lines, mip & sip
        input  logic                           ipi_i,        // inter-processor interrupts
        input  logic [4:0]                     irq_id_i,
        output logic                           irq_ack_o,
        input  logic                           irq_sec_i,
        output logic                           sec_lvl_o,
        // Timer facilities
        input  logic [63:0]                    time_i,        // global time (most probably coming from an RTC)
        input  logic                           time_irq_i,    // timer interrupt in

        // Debug Interface
        input  logic                           debug_req_i,
        output logic                           debug_gnt_o,
        output logic                           debug_rvalid_o,
        input  logic [15:0]                    debug_addr_i,
        input  logic                           debug_we_i,
        input  logic [63:0]                    debug_wdata_i,
        output logic [63:0]                    debug_rdata_o,
        output logic                           debug_halted_o,
        input  logic                           debug_halt_i,
        input  logic                           debug_resume_i
    );

    localparam int unsigned AXI_NUMBYTES = AXI_DATA_WIDTH/8;


    logic [63:0] instr_if_address;
    logic        instr_if_data_req;
    logic [3:0]  instr_if_data_be;
    logic        instr_if_data_gnt;
    logic        instr_if_data_rvalid;
    logic [63:0] instr_if_data_rdata;

    AXI_BUS #(
        .AXI_ADDR_WIDTH ( 64             ),
        .AXI_DATA_WIDTH ( 64             ),
        .AXI_ID_WIDTH   ( AXI_ID_WIDTH   ),
        .AXI_USER_WIDTH ( AXI_USER_WIDTH )
    ) data_if();

    AXI_BUS #(
        .AXI_ADDR_WIDTH ( 64             ),
        .AXI_DATA_WIDTH ( 64             ),
        .AXI_ID_WIDTH   ( AXI_ID_WIDTH   ),
        .AXI_USER_WIDTH ( AXI_USER_WIDTH )
    ) bypass_if();

    ariane #(
        .CACHE_START_ADDR ( 64'h4000_0000 ),
        .AXI_ID_WIDTH     ( 10            ),
        .AXI_USER_WIDTH   ( 1             )
    ) i_ariane (
        .*,
        .data_if                ( data_if              ),
        .bypass_if              ( bypass_if            ),
        .instr_if_address_o     ( instr_if_address     ),
        .instr_if_data_req_o    ( instr_if_data_req    ),
        .instr_if_data_be_o     ( instr_if_data_be     ),
        .instr_if_data_gnt_i    ( instr_if_data_gnt    ),
        .instr_if_data_rvalid_i ( instr_if_data_rvalid ),
        .instr_if_data_rdata_i  ( instr_if_data_rdata  )
    );

    core2mem i_core2mem (
        .instr_if_address_i     ( instr_if_address     ),
        .instr_if_data_req_i    ( instr_if_data_req    ),
        .instr_if_data_be_i     ( instr_if_data_be     ),
        .instr_if_data_gnt_o    ( instr_if_data_gnt    ),
        .instr_if_data_rvalid_o ( instr_if_data_rvalid ),
        .instr_if_data_rdata_o  ( instr_if_data_rdata  ),
        .bypass_if              ( bypass_if            ),
        .data_if                ( data_if              ),
        .*
    );

endmodule


module core2mem #(
        parameter int unsigned AXI_ID_WIDTH      = 10,
        parameter int unsigned AXI_USER_WIDTH    = 1,
        parameter int unsigned AXI_ADDRESS_WIDTH = 64,
        parameter int unsigned AXI_DATA_WIDTH    = 64
    )(
    input logic         clk_i,    // Clock
    input logic         rst_ni,  // Asynchronous reset active low
    AXI_BUS.Slave       bypass_if,
    AXI_BUS.Slave       data_if,
    // Instruction memory interface
    input  logic [63:0] instr_if_address_i,
    input  logic        instr_if_data_req_i,
    input  logic [3:0]  instr_if_data_be_i,
    output logic        instr_if_data_gnt_o,
    output logic        instr_if_data_rvalid_o,
    output logic [63:0] instr_if_data_rdata_o
);

    logic        bypass_req,     data_req;
    logic [63:0] bypass_address, data_address;
    logic        bypass_we,      data_we;
    logic [7:0]  bypass_be,      data_be;
    logic [63:0] bypass_wdata,   data_wdata;
    logic [63:0] bypass_rdata,   data_rdata;

    axi2mem #(
        .AXI_ID_WIDTH   ( AXI_ID_WIDTH      ),
        .AXI_ADDR_WIDTH ( AXI_ADDRESS_WIDTH ),
        .AXI_DATA_WIDTH ( AXI_DATA_WIDTH    ),
        .AXI_USER_WIDTH ( AXI_USER_WIDTH    )
    ) i_bypass (
        .clk_i  ( clk_i          ),
        .rst_ni ( rst_ni         ),
        .slave  ( bypass_if      ),
        .req_o  ( bypass_req     ),
        .we_o   ( bypass_we      ),
        .addr_o ( bypass_address ),
        .be_o   ( bypass_be      ),
        .data_o ( bypass_wdata   ),
        .data_i ( bypass_rdata   )
    );

    axi2mem #(
        .AXI_ID_WIDTH   ( AXI_ID_WIDTH      ),
        .AXI_ADDR_WIDTH ( AXI_ADDRESS_WIDTH ),
        .AXI_DATA_WIDTH ( AXI_DATA_WIDTH    ),
        .AXI_USER_WIDTH ( AXI_USER_WIDTH    )
    ) i_data (
        .clk_i  ( clk_i        ),
        .rst_ni ( rst_ni       ),
        .slave  ( data_if      ),
        .req_o  ( data_req     ),
        .we_o   ( data_we      ),
        .addr_o ( data_address ),
        .be_o   ( data_be      ),
        .data_o ( data_wdata   ),
        .data_i ( data_rdata   )
    );

    // ------------------------
    // Bypass Interface
    // ------------------------
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (~rst_ni) begin
            bypass_rdata <= '0;
        end else begin
            if (bypass_req & bypass_we)
                write_uint64({data_address[63:3], 3'b0}, bypass_wdata);
            else if (bypass_req)
                bypass_rdata <= read_uint64({bypass_address[63:3], 3'b0});
        end
    end

    // ------------------------
    // Data Interface
    // ------------------------
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (~rst_ni) begin
            data_rdata <= '0;
        end else begin
            if (data_req & data_we)
                write_uint64({data_address[63:3], 3'b0}, data_wdata);
            else if (data_req)
                data_rdata <= read_uint64({data_address[63:3], 3'b0});
        end
    end

    // ------------------------
    // Instruction Interface
    // ------------------------
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (~rst_ni) begin
            instr_if_data_rvalid_o <= 1'b0;
            instr_if_data_rdata_o  <= '0;
         end else begin
            // rvalid always one cycle after receiving re
            instr_if_data_rvalid_o <= instr_if_data_req_i;
            instr_if_data_rdata_o  <= instr_if_data_req_i ? read_uint64({instr_if_address_i[63:3], 3'b0}) : '0;
        end
    end

    assign instr_if_data_gnt_o = instr_if_data_req_i;

endmodule

