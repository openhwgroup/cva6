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

// Author: Florian Zaruba <zarubaf@iis.ee.ethz.ch>

/// Testbench for the isochronous spill register.
/// ## Compilation
///
/// This module needs to be compile with `-timescale "1 ns / 1 ps"` as
/// it doesn't specify an internal timescale.
module isochronous_spill_register_tb #(
  parameter int unsigned NumReq   = 32'd10000,
  parameter time SrcCyclTime      = 20ns,
  /// Make sure that the clocks are an integer multiple of each other.
  parameter time DstCyclTime      = SrcCyclTime*2
);

  logic src_clk, dst_clk;
  logic src_rst_n, dst_rst_n;
  logic sim_done;

  typedef logic [15:0] payload_t;
  // check FIFO
  payload_t data_fifo[$];

  STREAM_DV #(
    .payload_t (payload_t)
  ) dut_in (
    .clk_i (src_clk)
  );

  STREAM_DV #(
    .payload_t (payload_t)
  ) dut_out (
    .clk_i (dst_clk)
  );

  typedef stream_test::stream_driver #(
    .payload_t (payload_t),
    .TA (SrcCyclTime*0.2),
    .TT (SrcCyclTime*0.8)
  ) stream_driver_in_t;

  typedef stream_test::stream_driver #(
    .payload_t (payload_t),
    .TA (DstCyclTime*0.2),
    .TT (DstCyclTime*0.8)
  ) stream_driver_out_t;

  stream_driver_in_t in_driver = new(dut_in);
  stream_driver_out_t out_driver = new(dut_out);

  // Generate Stream data
  initial begin : proc_stream_master
    automatic payload_t    test_data;
    automatic int unsigned stall_cycles;
    in_driver.reset_in();
    @(posedge src_rst_n);
    repeat (5) @(posedge src_clk);
    for (int unsigned i = 0; i < NumReq; i++) begin
      test_data = payload_t'($urandom());
      stall_cycles = $urandom_range(0, 5);
      data_fifo.push_back(test_data);
      repeat (stall_cycles) @(posedge src_clk);
      in_driver.send(test_data);
    end
  end

  // consume stream data and check that the result matches
  initial begin : proc_stream_slave
    automatic int unsigned stall_cycles;
    automatic payload_t    expected, actual;
    automatic int unsigned num_tested = 32'd0;
    sim_done = 0;
    out_driver.reset_out();
    @(posedge dst_rst_n);
    repeat (5) @(posedge dst_clk);
    while (num_tested < NumReq) begin
      stall_cycles = $urandom_range(0, 5);
      repeat (stall_cycles) @(posedge dst_clk);
      out_driver.recv(actual);
      expected = data_fifo.pop_front();
      assert(expected === actual) else $error("expected: %h, actual: %0h", expected, actual);
      num_tested++;
    end
    repeat (50) @(posedge dst_clk);
    sim_done = 1'b1;
  end

  // stop the simulation
  initial begin : proc_sim_stop
    @(posedge src_rst_n);
    wait (sim_done);
    $stop();
  end

  // Clock Generation
  initial begin
    src_clk = 1'b0;
    forever begin
      src_clk = ~src_clk;
      #(SrcCyclTime / 2);
    end
  end

  initial begin
    dst_clk = 1'b0;
    forever begin
      dst_clk = ~dst_clk;
      #(DstCyclTime / 2);
    end
  end

  // Reset Generation
  initial begin
    static int unsigned rst_cnt = 0;
    src_rst_n = 1'b0;
    while (rst_cnt <= 10) begin
      @(posedge src_clk);
      rst_cnt++;
    end
    src_rst_n = 1'b1;
  end

  initial begin
    static int unsigned rst_cnt = 0;
    dst_rst_n = 1'b0;
    while (rst_cnt <= 10) begin
      @(posedge src_clk);
      rst_cnt++;
    end
    dst_rst_n = 1'b1;
  end

  isochronous_spill_register #(
    .T (payload_t)
  ) i_isochronous_spill_register (
    .src_clk_i (dut_in.clk_i),
    .src_rst_ni (src_rst_n),
    .src_valid_i (dut_in.valid),
    .src_ready_o (dut_in.ready),
    .src_data_i (dut_in.data),
    .dst_clk_i (dut_out.clk_i),
    .dst_rst_ni (dst_rst_n),
    .dst_valid_o (dut_out.valid),
    .dst_ready_i (dut_out.ready),
    .dst_data_o (dut_out.data)
  );

endmodule
