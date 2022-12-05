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

/// Testbench for the isochronous spill register and 4-phase handshake.
/// ## Compilation
///
/// This module needs to be compile with `-timescale "1 ns / 1 ps"` as
/// it doesn't specify an internal timescale.
module isochronous_crossing_tb #(
  parameter int unsigned NumReq   = 32'd10000,
  parameter string DUT            = "spill_register",
  parameter int unsigned TCK_SRC_MULT = 2,
  parameter int unsigned TCK_DST_MULT = 6
);

  localparam time CyclTime = 10ns; // smallest possible cycle time

  logic src_clk, dst_clk;
  logic src_rst_n, dst_rst_n;
  logic sim_done;

  typedef logic [15:0] payload_t;
  // check FIFO
  payload_t data_fifo[$];
  mailbox #(payload_t) data_mbx = new();

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
    .TA (TCK_SRC_MULT*CyclTime*0.2),
    .TT (TCK_SRC_MULT*CyclTime*0.8)
  ) stream_driver_in_t;

  typedef stream_test::stream_driver #(
    .payload_t (payload_t),
    .TA (TCK_DST_MULT*CyclTime*0.2),
    .TT (TCK_DST_MULT*CyclTime*0.8)
  ) stream_driver_out_t;

  stream_driver_in_t in_driver = new(dut_in);
  stream_driver_out_t out_driver = new(dut_out);

  int unsigned handshake_mst = 0;
  int unsigned handshake_slv = 0;

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
      handshake_mst++;
      repeat (stall_cycles) @(posedge src_clk);
      in_driver.send(test_data);
      data_mbx.put(test_data);
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
      data_mbx.get(expected);
      handshake_slv++;
      assert(expected === actual) else $error("expected: %h, actual: %0h", expected, actual);
      num_tested++;
    end
    repeat (50) @(posedge dst_clk);
    sim_done = 1'b1;
    assert(handshake_mst == handshake_slv) else $error("Amount of handshakes differed.");
  end

  // stop the simulation
  initial begin : proc_sim_stop
    @(posedge src_rst_n);
    wait (sim_done);
    $stop();
  end

  // Clock Generation
  initial begin
    $display("Simulating %d", DUT);
    src_clk = 1'b0;
    dst_clk = 1'b0;
    forever begin
      fork
        forever begin
          src_clk = ~src_clk;
          #((CyclTime * TCK_SRC_MULT) / 2);
        end
        forever begin
          dst_clk = ~dst_clk;
          #((CyclTime * TCK_DST_MULT) / 2);
        end
      join
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

  if (DUT == "spill_register") begin
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
  end if (DUT == "4phase_handshake") begin
    isochronous_4phase_handshake
    isochronous_4phase_handshake (
      .src_clk_i (dut_in.clk_i),
      .src_rst_ni (src_rst_n),
      .src_valid_i (dut_in.valid),
      .src_ready_o (dut_in.ready),
      .dst_clk_i (dut_out.clk_i),
      .dst_rst_ni (dst_rst_n),
      .dst_valid_o (dut_out.valid),
      .dst_ready_i (dut_out.ready)
    );

    always_ff @(posedge dut_in.clk_i)
      if (dut_in.valid & dut_in.ready)
        dut_out.data <= dut_in.data;
  end
endmodule
