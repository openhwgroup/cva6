/* Copyright 2018 ETH Zurich and University of Bologna.
 * Copyright and related rights are licensed under the Solderpad Hardware
 * License, Version 0.51 (the “License”); you may not use this file except in
 * compliance with the License.  You may obtain a copy of the License at
 * http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
 * or agreed to in writing, software, hardware and materials distributed under
 * this License is distributed on an “AS IS” BASIS, WITHOUT WARRANTIES OR
 * CONDITIONS OF ANY KIND, either express or implied. See the License for the
 * specific language governing permissions and limitations under the License.
 *
 * File:   dm_mem.sv
 * Author: Florian Zaruba <zarubaf@iis.ee.ethz.ch>
 * Date:   11.7.2018
 *
 * Description: Memory module for execution-based debug clients
 *
 */

module dm_mem #(
    parameter int NrHarts = -1
)(
    input  logic               clk_i,       // Clock
    input  logic               dmactive_i,  // debug module reset

    output logic [NrHarts-1:0] halted_o,    // hart acknowledge halt
    output logic [NrHarts-1:0] going_o,     // hart is running
    output logic [NrHarts-1:0] resuming_o,  // hart is resuming
    output logic [NrHarts-1:0] exception_o, // hart ran into an exception

    input  logic [dm::ProgBufSize-1:0][31:0] progbuf_i, // program buffer to expose
    input  logic [dm::DataCount-1:0][31:0]   data_i,    // data in
    // SRAM interface
    input  logic        req_i,
    input  logic        we_i,
    input  logic [63:0] addr_i,
    input  logic [63:0] wdata_i,
    input  logic [7:0]  be_i,
    output logic [63:0] rdata_o
);
    localparam HartSelLen = (NrHarts == 1) ? 1 : $clog2(NrHarts);

    logic [63:0] rom_rdata;
    // distinguish whether we need to forward data from the ROM or the FSM
    // latch the address for this
    logic fwd_rom_d, fwd_rom_q;

    debug_rom i_debug_rom (
        .clk_i,
        .req_i,
        .addr_i,
        .rdata_o (rom_rdata)
    );
    logic [HartSelLen-1:0] hart_sel;
    assign hart_sel = wdata_i[HartSelLen-1:0];
    // read/write logic
    always_comb begin
        halted_o    = '0;
        going_o     = '0;
        resuming_o  = '0;
        exception_o = '0;
        rdata_o     = fwd_rom_q ? rom_rdata : '0;
        // we've got a new request
        if (req_i) begin
            // this is a write
            if (we_i) begin
                case (addr_i[dm::DbgAddressBits-1:0])
                    dm::Halted:    halted_o[hart_sel]    = 1'b1;
                    dm::Going:     going_o[hart_sel]     = 1'b1;
                    dm::Resuming:  resuming_o[hart_sel]  = 1'b1;
                    dm::Exception: exception_o[hart_sel] = 1'b1;
                endcase
            // this is a read
            end else begin

            end
        end
    end

    // ROM starts at the HaltAddress of the core e.g.: it immediately jumps to
    // the ROM base address
    assign fwd_rom_d = (addr_i[dm::DbgAddressBits-1:0] >= dm::HaltAddress) ? 1'b1 : 1'b0;

    always_ff @(posedge clk_i) begin
        if (~dmactive_i) begin
            fwd_rom_q <= 1'b0;
        end else begin
            fwd_rom_q <= fwd_rom_d;
        end
    end

endmodule
