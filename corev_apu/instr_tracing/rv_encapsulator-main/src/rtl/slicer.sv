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

/* SLICER */
/*
this module slices the inputs into N sized chunks and outputs them one for cycle
*/
/*
the idea is to output the SLICE_LEN LSBs each cycle. When the counter goes up, the register 
storing the data to slice shifts right of SLICE_LEN positions.
*/

module slicer #(
    parameter SLICE_LEN = 32
) (
    input logic                             clk_i,
    input logic                             rst_ni,

    input logic                             valid_i,
    input encap_pkg::encap_fifo_entry_s     encap_fifo_entry_i,
    input logic                             fifo_full_i,

    output logic                            valid_o,
    output logic [SLICE_LEN-1:0]            slice_o,
    output logic [$clog2(SLICE_LEN)-4:0]    valid_bytes_o,
    output logic                            fifo_pop_o
);
    // internal state variables
    logic [8:0]                     slice_index_d, slice_index_q; // current slice index
    logic [encap_pkg::MAX_LEN-1:0]  payload_to_slice_d, payload_to_slice_q;
    logic                           stored_value_d, stored_value_q;
    logic [SLICE_LEN-1:0]           slice_d, slice_q;
    logic                           count;
    logic [8:0]                     num_slices_d, num_slices_q;
    logic [8:0]                     total_len;
    logic [8:0]                     length_left0_d, length_left0_q;
    logic [8:0]                     length_left1_d, length_left1_q;
    encap_pkg::header_s             header;
    logic [encap_pkg::T_LEN-1:0]    timestamp;
    encap_pkg::payload_s            payload;

    // assignments from input
    assign header = encap_fifo_entry_i.header;
    assign timestamp = encap_fifo_entry_i.timestamp;
    assign payload = encap_fifo_entry_i.payload;
    // checks if timestamp is present 
    assign total_len = header.extend ?  encap_pkg::H_LEN + encap_pkg::T_LEN + header.length*8 : 
                                        encap_pkg::H_LEN + header.length*8;
    // FFs assignments
    assign count = slice_index_q <= num_slices_q && stored_value_q && !fifo_full_i;
    // output assignments
    //assign ready_o = !stored_value_q;
    assign fifo_pop_o = slice_index_q == num_slices_q && num_slices_q != 0;
    assign slice_o = slice_q;
    assign valid_o = length_left1_q > 0 && !fifo_full_i;

    always_comb begin
        // initialization
        valid_bytes_o = '0;

        if (length_left1_q >= SLICE_LEN/8) begin
            valid_bytes_o = '1;
        end else if (length_left1_q < SLICE_LEN/8 && 
                     length_left1_q > 0) begin
            valid_bytes_o = length_left1_q - SLICE_LEN/8 - 1;
        end
    end

    always_comb begin
        // init
        payload_to_slice_d = payload_to_slice_q;
        stored_value_d = stored_value_q;
        num_slices_d = num_slices_q;
        length_left0_d = length_left0_q;
        length_left1_d = length_left1_q;
        slice_index_d = slice_index_q;
        slice_d = slice_q;

        if (!fifo_full_i) begin
            if (valid_i && !stored_value_q) begin
                payload_to_slice_d = header.extend ? {'0, payload, timestamp, header} : {'0, payload, header};
                stored_value_d = valid_i;
                num_slices_d = (total_len + SLICE_LEN -1) / SLICE_LEN;
                length_left0_d = total_len / 8;
                length_left1_d = length_left0_q;
            end else begin
                if (slice_index_q == num_slices_q) begin
                    slice_index_d = '0;
                    stored_value_d = '0;
                    slice_d = '0;
                    length_left0_d = '0;
                    length_left1_d = '0;
                end else if (slice_index_q < num_slices_q && stored_value_q) begin
                    slice_d = payload_to_slice_q[SLICE_LEN-1:0];
                    slice_index_d = count ? slice_index_q+1 : slice_index_q;
                    payload_to_slice_d = payload_to_slice_d >> SLICE_LEN;
                    if (length_left0_q - SLICE_LEN/8 + 1 > 0) begin
                        length_left0_d -= SLICE_LEN/8;
                    end
                end
            end
        end
    end
    
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            slice_index_q <= '0;
            payload_to_slice_q <= '0;
            stored_value_q <= '0;
            slice_q <= '0;
            num_slices_q <= '0;
            length_left0_q <= '0;
            length_left1_q <= '0;
        end else begin
            payload_to_slice_q <= payload_to_slice_d;
            stored_value_q <= stored_value_d;
            num_slices_q <= num_slices_d;
            length_left0_q <= length_left0_d;
            length_left1_q <= length_left1_d;
            slice_q <= {'0, slice_d};
            slice_index_q <= slice_index_d;
        end
    end

endmodule