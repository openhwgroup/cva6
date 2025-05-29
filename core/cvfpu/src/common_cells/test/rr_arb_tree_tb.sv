// Copyright 2020 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Author: Wolfgang Roennigner <wroennin@iis.ee.ethz.ch>

/// Testbench for the module `rr_arb_tree`
module rr_arb_tree_tb #(
  /// Number of input streams to the DUT
  parameter int unsigned NumInp    = 32'd7,
  /// Number of requests per input
  parameter int unsigned NumReqs   = 32'd20000,
  /// Handshaking as in AXI
  parameter bit          AxiVldRdy = 1'b1,
  /// Do not deassert the input request
  parameter bit          LockIn    = 1'b1,
  /// Enable fair arbitration, when disabled, no assertion for fairness
  parameter bit          FairArb   = 1'b1
);

  localparam time CyclTime = 10ns;
  localparam time ApplTime = 2ns;
  localparam time TestTime = 8ns;

  // throw an error if the measured throughput and expected throughput differ
  // more than this value
  localparam real error_threshold = 0.1;

  localparam int unsigned IdxWidth  = (NumInp > 32'd1) ? unsigned'($clog2(NumInp)) : 32'd1;
  localparam int unsigned DataWidth = 32'd45;
  typedef logic [IdxWidth-1:0]  idx_t;
  typedef logic [DataWidth-1:0] data_t;

  // clock signal
  logic               clk;
  logic               rst_n;
  logic               flush;
  idx_t               rr,       idx;
  logic  [NumInp-1:0] req_inp,  gnt_inp, end_of_sim;
  data_t [NumInp-1:0] data_inp;
  logic               req_oup,  gnt_oup;
  data_t              data_oup;

  // clock and rst gen
  clk_rst_gen #(
    .ClkPeriod    ( CyclTime ),
    .RstClkCycles ( 5        )
  ) i_clk_rst_gen (
    .clk_o  ( clk   ),
    .rst_no ( rst_n )
  );

  // drive input streams
  // Can not use `stream_driver`, as this also tests for requests taken away.
  for (genvar i = 0; i < NumInp; i++) begin : gen_stream_gen
    initial begin : proc_stream_gen
      automatic data_t       stimuli;
      automatic int unsigned rand_wait;

      end_of_sim[i] = 1'b0;
      @(posedge rst_n);
      data_inp[i] = '0;
      req_inp[i]  = 1'b0;

      // First have them continuously active for a number of time
      for (int unsigned j = 0; j < (i+1) * NumReqs; j++) begin
        data_inp[i] <= #ApplTime data_t'(i);
        req_inp[i]  <= #ApplTime 1'b1;
        @(posedge clk);
      end
      data_inp[i] <= #ApplTime '0;
      req_inp[i]  <= #ApplTime 1'b0;

      // wait until all other processes have their fixed request finished.
      repeat ((NumInp-i)*NumReqs) @(posedge clk);
      repeat (1000) @(posedge clk);

      // First have them continuously active for a number of time
      for (int unsigned j = 0; j < (NumInp-i) * NumReqs; j++) begin
        data_inp[i] <= #ApplTime data_t'(i);
        req_inp[i]  <= #ApplTime 1'b1;
        @(posedge clk);
      end
      data_inp[i] <= #ApplTime '0;
      req_inp[i]  <= #ApplTime 1'b0;

      repeat ((1+i)*NumReqs) @(posedge clk);
      repeat (1000) @(posedge clk);

      // First have them continuously active for a number of time
      for (int unsigned j = 0; j < (NumInp-i) * NumReqs; j++) begin
        if ((i % 2) == 0) begin
          data_inp[i] <= #ApplTime data_t'(i);
          req_inp[i]  <= #ApplTime 1'b1;
        end
        @(posedge clk);
      end
      data_inp[i] <= #ApplTime '0;
      req_inp[i]  <= #ApplTime 1'b0;

      repeat ((1+i)*NumReqs) @(posedge clk);
      repeat (1000) @(posedge clk);


      // have random stimuli
      for (int unsigned j = 0; j < NumReqs; j++) begin
        data_inp[i] <= #ApplTime new_stimuli();
        req_inp[i]  <= #ApplTime 1'b1;
        rand_wait = $urandom_range(1, 2*NumInp);
        if (LockIn) begin
          #TestTime;
          while (!gnt_inp[i]) begin
            @(posedge clk);
            #TestTime;
          end
        end else begin
          repeat (rand_wait) @(posedge clk);
        end
        @(posedge clk);
        data_inp[i] <= #ApplTime '0;
        req_inp[i]  <= #ApplTime 1'b0;

        rand_wait = $urandom_range(0, NumInp);
        repeat (rand_wait) @(posedge clk);
      end

      end_of_sim[i] = 1'b1;
    end
  end

  function data_t new_stimuli();
    for (int unsigned i = 0; i < DataWidth; i++) begin
      new_stimuli[i] = $urandom();
    end
  endfunction : new_stimuli

  // consume streams
  initial begin : proc_stream_consume
    @(posedge rst_n);
    gnt_oup = 1'b0;
    forever begin
      gnt_oup <= #ApplTime 1'b1;
      @(posedge clk);
    end
  end

  // flush sometimes
  initial begin : proc_flush
    automatic int unsigned rand_wait;
    flush = 1'b0;
    @(posedge rst_n);
    forever begin
      rand_wait = $urandom_range(2000, 20000);
      repeat (rand_wait) @(posedge clk);
      flush <= #ApplTime 1'b1;
      @(posedge clk);
      flush <= #ApplTime 1'b0;
    end
  end

  // end simulation
  initial begin : proc_sim_end
    @(posedge rst_n);
    wait (&end_of_sim);
    repeat (10) @(posedge clk);
    $stop();
  end

  // Check throughput
  for (genvar i = 0; i < NumInp; i++) begin : gen_throughput_checker
    initial begin : proc_throughput_checker
      automatic longint unsigned tot_active [NumInp:1];
      automatic longint unsigned tot_served [NumInp:1];
      automatic int     unsigned num_active;
      automatic real             throughput, exp_through, error;
      for (int unsigned j = 0; j < NumInp; j++) begin
       tot_active[j] = 0;
       tot_served[j] = 0;
      end

      @(posedge rst_n);
      while (!(&end_of_sim)) begin
        #TestTime;

        if (req_inp[i] && gnt_oup) begin
          num_active = 0;
          for (int unsigned j = 0; j < NumInp; j++) begin
            if (req_inp[j]) begin
              num_active++;
            end
          end

          tot_active[num_active] = tot_active[num_active] + 1;
          if (gnt_inp[i]) begin
            tot_served[num_active] = tot_served[num_active] + 1;
          end
        end
        @(posedge clk);
      end

      for (int unsigned j = 1; j <= NumInp; j++) begin
        if (tot_active[j] > 0) begin
          throughput  = real'(tot_served[j])/real'(tot_active[j]);
          exp_through = real'(1)/real'(j);
          error       = throughput - exp_through;
          if (FairArb && LockIn) begin
            assert(error < error_threshold && error > -error_threshold) else
                $warning("Line: %0d is unfair!", i);
          end
          $display("Line: %0d, TotActice: %0d Throughput: %0f Ideal: %0f Diff: %0f",
              i, j, throughput, exp_through, error);        end
      end
    end
  end

  // check data
  initial begin : proc_check_data
    automatic data_t data_queues[NumInp-1:0][$];
    automatic data_t exp_data;
    forever begin
      @(posedge clk);
      #TestTime;
      // Put exp data into the queues
      for (int unsigned i = 0; i < NumInp; i++) begin
        if (req_inp[i] && gnt_inp[i]) begin
          data_queues[i].push_back(data_inp[i]);
        end
      end

      // check that the right data is observed
      if (req_oup && gnt_oup) begin
        exp_data = data_queues[idx].pop_front();
        assert(exp_data === data_oup);
      end
    end
  end

  // DUT
  rr_arb_tree #(
    .NumIn     ( NumInp    ),
    .DataWidth ( DataWidth ),
    .ExtPrio   ( 1'b0      ),
    .AxiVldRdy ( AxiVldRdy ),
    .LockIn    ( LockIn    ),
    .FairArb   ( FairArb   )
  ) i_rr_arb_tree_dut (
    .clk_i  ( clk      ),
    .rst_ni ( rst_n    ),
    .flush_i( flush    ),
    .rr_i   ( '0       ),
    .req_i  ( req_inp  ),
    .gnt_o  ( gnt_inp  ),
    .data_i ( data_inp ),
    .gnt_i  ( gnt_oup  ),
    .req_o  ( req_oup  ),
    .data_o ( data_oup ),
    .idx_o  ( idx      )
  );
endmodule
