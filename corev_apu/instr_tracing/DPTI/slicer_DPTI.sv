// Copyright (c) 2025 Thales DIS design services SAS
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
// Author: Maxime Colson - Thales
// Date: 21/05/2025
module slicer_DPTI #(
    parameter SLICE_LEN = 32,
    parameter NO_TIME   = 0    // 0 : include time ; 1 : exclude time
) (
    input logic clk_i,
    input logic rst_ni,

    input logic                         valid_i,
    input encap_pkg::encap_fifo_entry_s encap_fifo_entry_i,
    input logic                         fifo_full_i,

    output logic                 valid_o,
    output logic [SLICE_LEN-1:0] slice_o,
    output logic                 done_o
);
  localparam DATA_LEN = encap_pkg::H_LEN + (NO_TIME ? 0 : encap_pkg::T_LEN) + encap_pkg::PAYLOAD_LEN;
  localparam NUM_SLICES = DATA_LEN / SLICE_LEN;
  localparam COUNT_LEN = $clog2(NUM_SLICES);

  logic [DATA_LEN-1 : 0] data_to_slice_q, data_to_slice_d;
  logic [COUNT_LEN-1:0] slice_index_d, slice_index_q;
  logic running_q, running_d;

  assign slice_o = data_to_slice_q[DATA_LEN-1:DATA_LEN-SLICE_LEN];
  assign valid_o = running_q && !fifo_full_i;
  assign done_o  = running_q && (slice_index_q == NUM_SLICES - 1) && !fifo_full_i;

  always_comb begin
    data_to_slice_d = data_to_slice_q;
    slice_index_d = slice_index_q;
    running_d = running_q;

    if (valid_i && !running_q) begin
      //new data to slice 
      data_to_slice_d = NO_TIME ? {encap_fifo_entry_i.header,encap_fifo_entry_i.payload} :
            {encap_fifo_entry_i.header,encap_fifo_entry_i.timestamp,encap_fifo_entry_i.payload};
      slice_index_d = 0;
      running_d = 1;
    end else if (running_q && !fifo_full_i) begin  // Stall if fifo is full
      //Slicing 
      data_to_slice_d = data_to_slice_q << SLICE_LEN;
      slice_index_d   = slice_index_q + 1;
      if (slice_index_q == NUM_SLICES - 1) begin
        running_d = 0;
      end
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      data_to_slice_q <= '0;
      slice_index_q <= '0;
      running_q <= '0;
    end else begin
      data_to_slice_q <= data_to_slice_d;
      slice_index_q <= slice_index_d;
      running_q <= running_d;
    end
  end


endmodule
