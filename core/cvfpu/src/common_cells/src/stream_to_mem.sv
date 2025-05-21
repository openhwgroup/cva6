// Copyright 2020 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Authors:
// - Andreas Kurth <akurth@iis.ee.ethz.ch>

/// `stream_to_mem`: Allows to use memories with flow control (`valid`/`ready`) for requests but without flow
/// control for output data to be used in streams.
`include "common_cells/registers.svh"
module stream_to_mem #(
  /// Memory request payload type, usually write enable, write data, etc.
  parameter type         mem_req_t  = logic,
  /// Memory response payload type, usually read data
  parameter type         mem_resp_t = logic,
  /// Number of buffered responses (fall-through, thus no additional latency).  This defines the
  /// maximum number of outstanding requests on the memory interface. If the attached memory
  /// responds in the same cycle a request is applied, this MUST be 0. If the attached memory
  /// responds at least one cycle after a request, this MUST be >= 1 and should be equal to the
  /// response latency of the memory to saturate bandwidth.
  parameter int unsigned BufDepth   = 32'd1
) (
  /// Clock
  input  logic      clk_i,
  /// Asynchronous reset, active low
  input  logic      rst_ni,
  /// Request stream interface, payload
  input  mem_req_t  req_i,
  /// Request stream interface, payload is valid for transfer
  input  logic      req_valid_i,
  /// Request stream interface, payload can be accepted
  output logic      req_ready_o,
  /// Response stream interface, payload
  output mem_resp_t resp_o,
  /// Response stream interface, payload is valid for transfer
  output logic      resp_valid_o,
  /// Response stream interface, payload can be accepted
  input  logic      resp_ready_i,
  /// Memory request interface, payload
  output mem_req_t  mem_req_o,
  /// Memory request interface, payload is valid for transfer
  output logic      mem_req_valid_o,
  /// Memory request interface, payload can be accepted
  input  logic      mem_req_ready_i,
  /// Memory response interface, payload
  input  mem_resp_t mem_resp_i,
  /// Memory response interface, payload is valid
  input  logic      mem_resp_valid_i
);

  typedef logic [$clog2(BufDepth+1):0] cnt_t;

  cnt_t cnt_d, cnt_q;
  logic buf_ready,
        req_ready;

  if (BufDepth > 0) begin : gen_buf
    // Count number of outstanding requests.
    always_comb begin
      cnt_d = cnt_q;
      if (req_valid_i && req_ready_o) begin
        cnt_d++;
      end
      if (resp_valid_o && resp_ready_i) begin
        cnt_d--;
      end
    end

    // Can issue another request if the counter is not at its limit or a response is delivered in
    // the current cycle.
    assign req_ready = (cnt_q < BufDepth) | (resp_valid_o & resp_ready_i);

    // Control request and memory request interface handshakes.
    assign req_ready_o = mem_req_ready_i & req_ready;
    assign mem_req_valid_o = req_valid_i & req_ready;

    // Buffer responses.
    stream_fifo #(
      .FALL_THROUGH ( 1'b1       ),
      .DEPTH        ( BufDepth   ),
      .T            ( mem_resp_t )
    ) i_resp_buf (
      .clk_i,
      .rst_ni,
      .flush_i    ( 1'b0             ),
      .testmode_i ( 1'b0             ),
      .data_i     ( mem_resp_i       ),
      .valid_i    ( mem_resp_valid_i ),
      .ready_o    ( buf_ready        ),
      .data_o     ( resp_o           ),
      .valid_o    ( resp_valid_o     ),
      .ready_i    ( resp_ready_i     ),
      .usage_o    ( /* unused */     )
    );

    // Register
    `FFARN(cnt_q, cnt_d, '0, clk_i, rst_ni)

  end else begin : gen_no_buf
    // Control request, memory request, and response interface handshakes.
    assign mem_req_valid_o = req_valid_i;
    assign resp_valid_o    = mem_req_valid_o & mem_req_ready_i & mem_resp_valid_i;
    assign req_ready_o     = resp_ready_i    & resp_valid_o;

    // Forward responses.
    assign resp_o = mem_resp_i;
  end

  // Forward requests.
  assign mem_req_o = req_i;

// Assertions
// pragma translate_off
`ifndef VERILATOR
  if (BufDepth > 0) begin : gen_buf_asserts
    assert property (@(posedge clk_i) mem_resp_valid_i |-> buf_ready)
      else $error("Memory response lost!");
    assert property (@(posedge clk_i) cnt_q == '0 |=> cnt_q != '1)
      else $error("Counter underflowed!");
    assert property (@(posedge clk_i) cnt_q == BufDepth |=> cnt_q != BufDepth + 1)
      else $error("Counter overflowed!");
  end else begin : gen_no_buf_asserts
    assume property (@(posedge clk_i) mem_req_valid_o & mem_req_ready_i |-> mem_resp_valid_i)
      else $error("Without BufDepth = 0, the memory must respond in the same cycle!");
  end
`endif
// pragma translate_on
endmodule
