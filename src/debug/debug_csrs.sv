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
 * File:   axi_riscv_debug_module.sv
 * Author: Florian Zaruba <zarubaf@iis.ee.ethz.ch>
 * Date:   30.6.2018
 *
 * Description: Debug CSRs. Communication over Debug Transport Module (DTM)
 */

module debug_csrs #(
    parameter int NrHarts = -1
)(
    input  logic        clk_i,   // Clock
    input  logic        rst_ni,  // Asynchronous reset active low
    input  logic        debug_req_valid,
    output logic        debug_req_ready,
    input  logic [ 6:0] debug_req_bits_addr,
    input  logic [ 1:0] debug_req_bits_op, // 0 = nop, 1 = read, 2 = write
    input  logic [31:0] debug_req_bits_data,
    // every request needs a response one cycle later
    output logic        debug_resp_valid,
    input  logic        debug_resp_ready,
    output logic [ 1:0] debug_resp_bits_resp,
    output logic [31:0] debug_resp_bits_data,
    // hart communication
    input  logic [NrHarts-1:0] halted_i,      // hart is halted
    input  logic [NrHarts-1:0] running_i,     // hart is running
    input  logic [NrHarts-1:0] unavailable_i  // e.g.: powered down

);
    // the amount of bits we need to represent all harts
    localparam NrHartBits = (NrHarts == 1) ? 1 : $clog2(NrHarts);

    logic        resp_queue_full;
    logic        resp_queue_empty;
    logic        resp_queue_push;
    logic [31:0] resp_queue_data;

    dm::dmstatus_t  dmstatus;
    dm::dmcontrol_t dmcontrol_d, dmcontrol_q;

    // a successful response returns zero
    assign debug_resp_bits_resp = DTM_SUCCESS;
    assign debug_resp_valid     = ~resp_queue_empty;
    assign debug_req_ready      = ~resp_queue_full;
    assign resp_queue_push      = debug_req_valid & debug_req_ready;

    always_comb begin : csr_read_write
        // default assignments
        dmstatus         = '0;
        dmstatus.version = DbgVersion013;
        // no authentication implemented
        dmstatus.authenticated = 1'b1;

        dmcontrol_d = dmcontrol_q;
        // we only allow 1024 harts
        dmcontrol_d.hartselhi = '0;
        // determine how how many harts we actually want to select
        dmcontrol_d.hartsello[9:NrHartBits] = '0;

        resp_queue_data = 32'0;

        if (debug_req_valid && debug_req_bits_op == DTM_READ) begin
            unique case ({1'b0, debug_req_bits_addr})
                default:;
            endcase
        end

        if (debug_req_valid && debug_req_bits_op == DTM_WRITE) begin
            unique case ({1'b0, debug_req_bits_addr})
                default:;
            endcase
        end
    end

    // response FIFO
    fifo #(
        .dtype(logic [31:0]),
        .DEPTH(2)
    ) i_fifo (
        .clk_i            ( clk_i                ),
        .rst_ni           ( rst_ni               ),
        .flush_i          ( 1'b0                 ), // we do not need to flush this queue
        .full_o           ( resp_queue_full      ),
        .empty_o          ( resp_queue_empty     ),
        .single_element_o (                      ),
        .data_i           ( resp_queue_data      ),
        .push_i           ( resp_queue_push      ),
        .data_o           ( debug_resp_bits_data ),
        .pop_i            ( debug_resp_ready     )
    );

    always_ff @(posedge clk_i or negedge rst_ni) begin : proc_
        if(~rst_ni) begin
            dmcontrol_q <= '0;
        end else begin
            dmcontrol_q <= dmcontrol_d;
        end
    end

    `ifndef SYNTHESIS
        initial begin
            assert (NR_HARTS == 1024) else $error ("A maxium of 1024 harts is allowed.");
        end
    `endif
endmodule
