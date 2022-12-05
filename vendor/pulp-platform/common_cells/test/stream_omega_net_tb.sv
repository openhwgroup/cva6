// Copyright (c) 2020 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Author: Wolfgang Roenninger <wroennin@ethz.ch>

/// Testbench for the module `stream_xbar`.
module stream_omega_net_tb #(
  /// Number of requests per input.
  parameter int unsigned NumReq      = 32'd20000,
  /// Number of inputs.
  parameter int unsigned DutNumInp   = 32'd10,
  /// Number of outputs.
  parameter int unsigned DutNumOut   = 32'd10,
  /// Radix of network
  parameter int unsigned DutRadix    = 32'd2,
  /// Outputs have a spill register.
  parameter bit          DutSpillReg = 1'b0,
  /// Clock cycle time.
  parameter time         CyclTime    = 20ns
);
  localparam OutSelWidth = (DutNumOut > 32'd1) ? unsigned'($clog2(DutNumOut)) : 32'd1;
  localparam InpIdxWidth = (DutNumInp > 32'd1) ? unsigned'($clog2(DutNumInp)) : 32'd1;
  typedef logic [OutSelWidth-1:0] sel_t;
  typedef logic [InpIdxWidth-1:0] idx_t;
  typedef struct packed {
    logic [15:0] payload;
    idx_t        index;
  } payload_t;

  logic              clk;
  logic              rst_n;
  logic              flush;
  logic [DutNumInp-1:0] sim_done;

  assign flush = 1'b0;

  // clock generator
  clk_rst_gen #(
    .ClkPeriod    ( CyclTime ),
    .RstClkCycles ( 5        )
  ) i_clk_rst_gen (
    .clk_o  ( clk   ),
    .rst_no ( rst_n )
  );

  // check FIFO
  payload_t data_fifo [DutNumInp-1:0][DutNumOut-1:0][$];

  typedef stream_test::stream_driver #(
    .payload_t (payload_t),
    .TA (CyclTime*0.2),
    .TT (CyclTime*0.8)
  ) stream_driver_in_t;

  typedef stream_test::stream_driver #(
    .payload_t (payload_t),
    .TA (CyclTime*0.2),
    .TT (CyclTime*0.8)
  ) stream_driver_out_t;

  payload_t [DutNumInp-1:0] inp_data;
  logic     [DutNumInp-1:0] inp_valid, inp_ready;
  sel_t     [DutNumInp-1:0] out_sel;
  for (genvar i = 0; i < DutNumInp; i++) begin : gen_inp
    STREAM_DV #(
      .payload_t (payload_t)
    ) dut_in (
      .clk_i (clk)
    );
    assign inp_data[i]  = dut_in.data;
    assign inp_valid[i] = dut_in.valid;
    assign dut_in.ready = inp_ready[i];

    stream_driver_in_t  in_driver = new(dut_in);

    initial begin : proc_source
      automatic payload_t    data;
      automatic int unsigned wait_cycl;
      data.index = idx_t'(i);

      @(posedge rst_n);
      in_driver.reset_in();
      out_sel[i]  = 1'b0;
      sim_done[i] = 1'b0;

      for (int unsigned i_stim = 0; i_stim < (NumReq/DutNumInp); i_stim++) begin
        wait_cycl = $urandom_range(0, 5);
        repeat (wait_cycl) @(posedge clk);
        data.payload = $urandom();
        out_sel[i]   = sel_t'($urandom_range(0, DutNumOut-1));
        data_fifo[i][out_sel[i]].push_back(data);
        in_driver.send(data);
      end

      sim_done[i] = 1'b1;
    end
  end

  payload_t [DutNumOut-1:0] out_data;
  logic     [DutNumOut-1:0] out_valid, out_ready;
  idx_t     [DutNumOut-1:0] out_idx;
  for (genvar j = 0; j < DutNumOut; j++) begin : gen_out
    STREAM_DV #(
      .payload_t (payload_t)
    ) dut_out (
      .clk_i (clk)
    );
    assign dut_out.data  = out_data[j];
    assign dut_out.valid = out_valid[j];
    assign out_ready[j]  = dut_out.ready;

    stream_driver_out_t out_driver = new(dut_out);
    initial begin : proc_sink
      automatic payload_t    data,      exp;
      automatic int unsigned wait_cycl;
      @(posedge rst_n);
      out_driver.reset_out();

      forever begin
        wait_cycl = $urandom_range(0, 5);
        repeat (wait_cycl) @(posedge clk);
        out_driver.recv(data);
        exp = data_fifo[out_idx[j]][j].pop_front();
        assert(data == exp) else
          $error("Out %d: Payload data does not match. Observed: %0h Expected: %0h", j, data, exp);
        assert(data.index == out_idx[j]) else
          $error("Index in payload: %0d does not match idx_o[%0d]: %0d", data.index, j, out_idx[j]);
      end
    end
  end

  initial begin : proc_stop_sim
    @(posedge rst_n);
    wait (&sim_done);
    repeat (20) @(posedge clk);
    $display("Sim done.");
    $stop();
  end

  // Dut instantiation
  stream_omega_net #(
    .NumInp       ( DutNumInp   ),
    .NumOut       ( DutNumOut   ),
    .payload_t    ( payload_t   ),
    .SpillReg     ( DutSpillReg ),
    .Radix        ( DutRadix    ),
    .ExtPrio      ( 1'b0        ),
    .AxiVldRdy    ( 1'b1        ),
    .LockIn       ( 1'b1        )
  ) i_stream_omega_net_dut (
    .clk_i   ( clk       ),
    .rst_ni  ( rst_n     ),
    .flush_i ( flush     ),
    .rr_i    ( '0        ),
    .data_i  ( inp_data  ),
    .sel_i   ( out_sel   ),
    .valid_i ( inp_valid ),
    .ready_o ( inp_ready ),
    .data_o  ( out_data  ),
    .idx_o   ( out_idx   ),
    .valid_o ( out_valid ),
    .ready_i ( out_ready )
  );
endmodule
