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
// Date: 19.03.2017
// Description: Ariane Top-level module

import ariane_pkg::*;

import "DPI-C" function void write_uint64(input longint unsigned address, input longint unsigned data);
import "DPI-C" function longint unsigned read_uint64(input longint unsigned address);
import "DPI-C" function longint unsigned get_tohost_address();
import "DPI-C" function longint unsigned get_fromhost_address();

module ariane_wrapped #(
        parameter logic [63:0] CACHE_START_ADDR  = 64'h8000_0000, // address on which to decide whether the request is cache-able or not
        parameter int unsigned AXI_ID_WIDTH      = 10,
        parameter int unsigned AXI_USER_WIDTH    = 1,
        parameter int unsigned AXI_ADDRESS_WIDTH = 64,
        parameter int unsigned AXI_DATA_WIDTH    = 64
    )(
        input  logic                           clk_i,
        input  logic                           rst_ni,
        input  logic                           test_en_i,     // enable all clock gates for testing
        // Core ID, Cluster ID and boot address are considered more or less static
        input  logic [63:0]                    boot_addr_i,
        input  logic [ 3:0]                    core_id_i,
        input  logic [ 5:0]                    cluster_id_i,
        input  logic                           flush_req_i,
        output logic                           flushing_o,
        // Interrupt inputs
        input  logic [1:0]                     irq_i,        // level sensitive IR lines, mip & sip
        input  logic                           ipi_i,        // inter-processor interrupts
        output logic                           sec_lvl_o,    // current privilege level oot
        // Timer facilities
        input  logic [63:0]                    time_i,        // global time (most probably coming from an RTC)
        input  logic                           time_irq_i     // timer interrupt in
    );

    localparam int unsigned AXI_NUMBYTES = AXI_DATA_WIDTH/8;

    longint unsigned tohost, fromhost;

    logic        flush_dcache_ack, flush_dcache;
    logic        flush_dcache_d, flush_dcache_q;

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

    AXI_BUS #(
        .AXI_ADDR_WIDTH ( 64             ),
        .AXI_DATA_WIDTH ( 64             ),
        .AXI_ID_WIDTH   ( AXI_ID_WIDTH   ),
        .AXI_USER_WIDTH ( AXI_USER_WIDTH )
    ) instr_if();

    ariane #(
        .CACHE_START_ADDR ( CACHE_START_ADDR ),
        .AXI_ID_WIDTH     ( 10               ),
        .AXI_USER_WIDTH   ( 1                )
    ) i_ariane (
        .*,
        .flush_dcache_i         ( flush_dcache         ),
        .flush_dcache_ack_o     ( flush_dcache_ack     ),
        .data_if                ( data_if              ),
        .bypass_if              ( bypass_if            ),
        .instr_if               ( instr_if             )
    );

    core2mem i_core2mem (
        .instr_if               ( instr_if             ),
        .bypass_if              ( bypass_if            ),
        .data_if                ( data_if              ),
        .*
    );

    assign flush_dcache = flush_dcache_q;
    assign flushing_o = flush_dcache_q;

    // direct store interface
    always_ff @(posedge clk_i or negedge rst_ni) begin

        automatic logic [63:0] store_address;

        if (~rst_ni) begin
            flush_dcache_q  <= 1'b0;
        end else begin
            // got acknowledge from dcache - release the flush signal
            if (flush_dcache_ack)
                flush_dcache_q <= 1'b0;

            // a write to tohost or fromhost
            if (i_ariane.ex_stage_i.lsu_i.i_store_unit.data_req_o
              & i_ariane.ex_stage_i.lsu_i.i_store_unit.data_gnt_i
              & i_ariane.ex_stage_i.lsu_i.i_store_unit.data_we_o) begin
                store_address = {i_ariane.ex_stage_i.lsu_i.i_store_unit.address_tag_o, i_ariane.ex_stage_i.lsu_i.i_store_unit.address_index_o[11:3], 3'b0};

                // this assumes that tohost writes are always 64-bit
                if (store_address == tohost || store_address == fromhost) begin
                    flush_dcache_q <= 1'b1;
                end
            end

            if (flush_req_i) begin
                flush_dcache_q <= 1'b1;
            end
        end
    end

    initial begin
        tohost = get_tohost_address();
        fromhost = get_fromhost_address();
    end

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
    AXI_BUS.Slave       instr_if
);

    logic        instr_req,     bypass_req,     data_req;
    logic [63:0] instr_address, bypass_address, data_address;
    logic        instr_we,      bypass_we,      data_we;
    logic [7:0]  instr_be,      bypass_be,      data_be;
    logic [63:0] instr_wdata,   bypass_wdata,   data_wdata;
    logic [63:0] instr_rdata,   bypass_rdata,   data_rdata;

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

    axi2mem #(
        .AXI_ID_WIDTH   ( AXI_ID_WIDTH      ),
        .AXI_ADDR_WIDTH ( AXI_ADDRESS_WIDTH ),
        .AXI_DATA_WIDTH ( AXI_DATA_WIDTH    ),
        .AXI_USER_WIDTH ( AXI_USER_WIDTH    )
    ) i_instr (
        .clk_i  ( clk_i         ),
        .rst_ni ( rst_ni        ),
        .slave  ( instr_if      ),
        .req_o  ( instr_req     ),
        .we_o   ( instr_we      ),
        .addr_o ( instr_address ),
        .be_o   ( instr_be      ),
        .data_o ( instr_wdata   ),
        .data_i ( instr_rdata   )
    );

    // ------------------------
    // Bypass Interface
    // ------------------------
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (~rst_ni) begin
            bypass_rdata <= '0;
        end else begin
            if (bypass_req & bypass_we)
                write_uint64({bypass_address[63:3], 3'b0}, bypass_wdata);
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
            instr_rdata <= '0;
        end else begin
            if (instr_req & instr_we)
                write_uint64({instr_address[63:3], 3'b0}, instr_wdata);
            else if (instr_req)
                instr_rdata <= read_uint64({instr_address[63:3], 3'b0});
        end
    end
endmodule

