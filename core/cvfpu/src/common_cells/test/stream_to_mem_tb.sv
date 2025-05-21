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
// - Wolfgang Rönninger <wroennin@iis.ee.ethz.ch>

// Test bench for `stream_to_mem`
module stream_to_mem_tb #(
  parameter int unsigned NumReq   = 32'd10000,
  parameter int unsigned BufDepth = 32'd1
);

  localparam time CyclTime = 10ns;
  localparam time ApplTime = 2ns;
  localparam time TestTime = 8ns;

  typedef logic [15:0] payload_t;


  // Signals
  logic     clk,       rst_n,      sim_done;
  payload_t req,       resp,       mem_req,       mem_resp;
  logic     req_valid, resp_valid, mem_req_valid, mem_resp_valid;
  logic     req_ready, resp_ready, mem_req_ready;

  // check FIFO
  payload_t data_fifo[$];

  // Generate Stream data
  initial begin : proc_stream_master
    automatic payload_t    test_data;
    automatic int unsigned stall_cycles;
    @(posedge rst_n);
    req       = '0;
    req_valid = '0;
    repeat (5) @(posedge clk);
    for (int unsigned i = 0; i < NumReq; i++) begin
      stall_cycles = $urandom_range(0, 5);
      repeat (stall_cycles) @(posedge clk);
      test_data = payload_t'($urandom());
      data_fifo.push_back(test_data);
      req       <= #ApplTime payload_t'(test_data);
      req_valid <= #ApplTime 1'b1;
      #TestTime;
      while (!req_ready) begin
        @(posedge clk);
        #TestTime;
      end
      @(posedge clk);
      req       <= #ApplTime '0;
      req_valid <= #ApplTime 1'b0;
    end
  end

  // consume stream data and check that the result matches
  initial begin : proc_stream_slave
    automatic int unsigned stall_cycles;
    automatic payload_t    test_data;
    automatic int unsigned num_tested = 32'd0;
    sim_done = 0;
    @(posedge rst_n);
    resp_ready = '0;
    repeat (5) @(posedge clk);
    while (num_tested < NumReq) begin
      resp_ready <= #ApplTime $urandom();
      #TestTime;
      if (resp_valid && resp_ready) begin
        test_data = data_fifo.pop_front();
        assert(test_data === resp) else $error("test_data: %h, resp_data: %0h", test_data, resp);
        num_tested++;
      end
      @(posedge clk);
    end
    repeat (50) @(posedge clk);
    sim_done = 1'b1;
  end

  // reflect the payload exactly `BufDepth` Cycles later, standin for memory
  initial begin : proc_mem_reflect
    automatic payload_t reflect_fifo[$];
    @(posedge rst_n);
    mem_req_ready  = '0;
    mem_resp       = '0;
    mem_resp_valid = '0;
    forever begin
      mem_req_ready <= #ApplTime $urandom();
      #(CyclTime / 2);
      if (mem_req_valid && mem_req_ready) begin
        reflect_fifo.push_back(mem_req);
        // respond with a one cycle pule BufDepth cycles later
        fork
          begin
            if (BufDepth) begin
              repeat (BufDepth) @(posedge clk);
              #ApplTime;
            end
            mem_resp       = reflect_fifo.pop_front();
            mem_resp_valid = 1'b1;
            @(posedge clk);
            #(ApplTime / 2);
            mem_resp_valid = 1'b0;
          end
        join_none
      end
      @(posedge clk);
    end
  end

  // stop the simulation
  initial begin : proc_sim_stop
    @(posedge rst_n);
    wait (sim_done);
    $stop();
  end

  // CLK generator
  clk_rst_gen #(
    .ClkPeriod    ( CyclTime ),
    .RstClkCycles ( 10       )
  ) i_clk_rst_gen (
    .clk_o  ( clk   ),
    .rst_no ( rst_n )
  );

  // DUT
  stream_to_mem #(
    .mem_req_t  ( payload_t ),
    .mem_resp_t ( payload_t ),
    .BufDepth   ( BufDepth  )
  ) i_stream_to_mem_dut (
    .clk_i            ( clk            ),
    .rst_ni           ( rst_n          ),
    .req_i            ( req            ),
    .req_valid_i      ( req_valid      ),
    .req_ready_o      ( req_ready      ),
    .resp_o           ( resp           ),
    .resp_valid_o     ( resp_valid     ),
    .resp_ready_i     ( resp_ready     ),
    .mem_req_o        ( mem_req        ),
    .mem_req_valid_o  ( mem_req_valid  ),
    .mem_req_ready_i  ( mem_req_ready  ),
    .mem_resp_i       ( mem_resp       ),
    .mem_resp_valid_i ( mem_resp_valid )
  );

endmodule
