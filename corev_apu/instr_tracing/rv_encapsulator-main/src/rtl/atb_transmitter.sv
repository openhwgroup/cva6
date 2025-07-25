// Copyright 2025 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
// SPDX-License-Identifier: SHL-0.51

// Author:  Umberto Laghi
// Contact: umberto.laghi2@unibo.it
// Github:  @ubolakes

/* ATB TRANSMITTER */
/*
this module implements an ATB transmitter as described in the AMBA ATB protocol specification.
*/

module atb_transmitter #(
    parameter DATA_LEN = 32 // to simplify: use the same value as SLICE_LEN
) (
    input logic                         clk_i,
    input logic                         rst_ni,

    input logic                         atready_i,
    input logic                         afvalid_i,
    input logic                         fifo_empty_i,
    input logic [DATA_LEN-1:0]          slice_i,
    input logic [$clog2(DATA_LEN)-4:0]  valid_bytes_i,
    input logic [6:0]                   atid_i,

    output logic [$clog2(DATA_LEN)-4:0] atbytes_o,
    output logic [DATA_LEN-1:0]         atdata_o,
    output logic [6:0]                  atid_o,
    output logic                        atvalid_o,
    output logic                        afready_o,
    output logic                        fifo_pop_o
);
    logic valid_enable_d, valid_enable_q;
    logic flush_d, flush_q;

    assign valid_enable_d = rst_ni;
    assign flush_d = atvalid_o && atready_i && afvalid_i;
    assign afready_o = flush_q;

    /* 
    the fifo outputs the signal until it gets popped: so if a transmission does not happen, there 
    is no need to store that value in a register, but simply the fifo is not popped.
    */
    always_comb begin
        // initialization
        atdata_o = '0;
        atbytes_o = '0;
        atvalid_o = '0;
        fifo_pop_o = '0;
        atid_o = '0;

        // transmitting until there is something in the fifo
        if (!fifo_empty_i && valid_enable_q) begin
            atdata_o = slice_i;
            atbytes_o = valid_bytes_i;
            atid_o = atid_i;    
            
            // when receiver is ready it pops the fifo and sets output as valid
            if (atready_i) begin
                fifo_pop_o = '1;
                atvalid_o = '1;
            end
        end
    end

    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            valid_enable_q <= '0;
            flush_q <= '0;
        end else begin
            valid_enable_q <= valid_enable_d;
            flush_q <= flush_d;
        end
    end

endmodule