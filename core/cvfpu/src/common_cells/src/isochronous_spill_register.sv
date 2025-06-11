// Copyright 2020 ETH Zurich and University of Bologna.
//
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Florian Zaruba <zarubaf@iis.ee.ethz.ch>

`include "common_cells/registers.svh"

/// A register with handshakes that completely cuts any combinatorial paths
/// between the input and output in isochronous clock domains.
///
/// > Definition of isochronous: In telecommunication, an isochronous signal is a signal
/// > in which the time interval separating any two significant instants is equal to the
/// > unit interval or a multiple of the unit interval.
///
/// The source and destination clock domains must be derived from the same clock
/// but can vary in frequency by a constant factor (e.g., double the frequency).
///
/// The module is basically a two deep dual-clock fifo with read and write pointers
/// in different clock domains. As we know the static timing relationship between the
/// clock domains we can rely on static timing analysis (STA) to get the sampling windows
/// right and therefore don't need any synchronization.
module isochronous_spill_register #(
  /// Data type of spill register.
  parameter type T      = logic,
  /// Make this spill register transparent.
  parameter bit  Bypass = 1'b0
) (
  /// Clock of source clock domain.
  input  logic src_clk_i,
  /// Active low async reset in source domain.
  input  logic src_rst_ni,
  /// Source input data is valid.
  input  logic src_valid_i,
  /// Source is ready to accept.
  output logic src_ready_o,
  /// Source input data.
  input  T     src_data_i,
  /// Clock of destination clock domain.
  input  logic dst_clk_i,
  /// Active low async reset in destination domain.
  input  logic dst_rst_ni,
  /// Destination output data is valid.
  output logic dst_valid_o,
  /// Destination is ready to accept.
  input  logic dst_ready_i,
  /// Destination output data.
  output T     dst_data_o
);
  // Don't generate the spill register.
  if (Bypass) begin : gen_bypass
    assign dst_valid_o = src_valid_i;
    assign src_ready_o = dst_ready_i;
    assign dst_data_o  = src_data_i;
  // Generate the spill register
  end else begin : gen_isochronous_spill_register
    /// Read/write pointer are one bit wider than necessary.
    /// We implicitly capture the full and empty state with the second bit:
    /// If all but the topmost bit of `rd_pointer_q` and `wr_pointer_q` agree, the
    /// FIFO is in a critical state. If the topmost bit is equal, the FIFO is
    /// empty, otherwise it is full.
    logic [1:0] rd_pointer_q, wr_pointer_q;
    // Advance write pointer if we pushed a new item into the FIFO. (Source clock domain)
    `FFLARN(wr_pointer_q, wr_pointer_q+1, (src_valid_i && src_ready_o), '0, src_clk_i, src_rst_ni)
    // Advance read pointer if downstream consumed an item. (Destination clock domain)
    `FFLARN(rd_pointer_q, rd_pointer_q+1, (dst_valid_o && dst_ready_i), '0, dst_clk_i, dst_rst_ni)

    T [1:0] mem_d, mem_q;
    `FFLNR(mem_q, mem_d, (src_valid_i && src_ready_o), src_clk_i)
    always_comb begin
      mem_d = mem_q;
      mem_d[wr_pointer_q[0]] = src_data_i;
    end

    assign src_ready_o = (rd_pointer_q ^ wr_pointer_q) != 2'b10;

    assign dst_valid_o = (rd_pointer_q ^ wr_pointer_q) != '0;
    assign dst_data_o = mem_q[rd_pointer_q[0]];
  end
endmodule
