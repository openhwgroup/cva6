// Copyright (c) 2019 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Author: Wolfgang Roenninger <wroennin@ethz.ch>

// This testbench can be used to look at the `sub_per_hash` function outputs.
// The stimuli increment the input per clock cycle up to a max amount of cycles.
module sub_per_hash_tb;
  //---------------------------------------------------------
  // TB parameters
  //---------------------------------------------------------
  localparam time TCycle = 10ns;
  localparam time TAppli =  2ns;
  localparam time TTest  =  8ns;
  localparam longint unsigned MaxCycles = 64'd100000000;

  //---------------------------------------------------------
  // DUT parameters / signals
  //---------------------------------------------------------
  localparam int unsigned DataWidth   = 32'd11;
  localparam int unsigned HashWidth   = 32'd5;
  localparam int unsigned NoHashes    = 32'd3;
  localparam int unsigned NoRounds    = 32'd1;
  typedef logic [DataWidth-1:0]    data_t;
  typedef logic [HashWidth-1:0]    hash_t;
  typedef logic [2**HashWidth-1:0] onehot_hash_t;

  localparam cb_filter_pkg::cb_seed_t [NoHashes-1:0] Seeds = '{
    '{PermuteSeed: 32'd299034753, XorSeed: 32'd4094834 },
    '{PermuteSeed: 32'd19921030,  XorSeed: 32'd995713  },
    '{PermuteSeed: 32'd294388,    XorSeed: 32'd65146511}
  };

  logic  clk;
  logic  rst_n;

  data_t                       data;
  hash_t        [NoHashes-1:0] hash;
  onehot_hash_t [NoHashes-1:0] onehot_hash;

  // -------------
  // Clock generator
  // -------------
  clk_rst_gen #(
    .CLK_PERIOD     ( TCycle ),
    .RST_CLK_CYCLES (      1 )
  ) i_clk_gen (
    .clk_o  (   clk ),
    .rst_no ( rst_n )
  );

  // ------------------------
  // Test Bench
  // ------------------------
  program test_cbf;
    initial begin : shutdown_sim
      repeat (MaxCycles) @(posedge clk);
      $info("Stop, because max cycles was reached.");
      $stop();
    end

    initial begin : stimulus
      set_data(0);
      // wait for reset
      @(posedge rst_n);
      repeat (10) @(posedge clk);

      for (longint unsigned i = 0; i < 2**DataWidth; i++) begin
        set_data(i);
      end

      repeat (10) @(posedge clk);
      $info("Stop, because all possible inputs were applied.");
      $stop();
    end

    task cycle_start();
      #TTest;
    endtask : cycle_start

    task cycle_end();
      @(posedge clk);
    endtask : cycle_end

    task set_data (input longint unsigned nbr);
      data <= #TAppli data_t'(nbr);
      cycle_end();
    endtask : set_data

    task init_signals();
      data <= '0;
    endtask : init_signals
  endprogram

  // generate duts
  for (genvar i = 0; i < NoHashes; i++) begin : gen_hash_dut
    sub_per_hash #(
      .InpWidth   ( DataWidth            ),
      .HashWidth  ( HashWidth            ),
      .NoRounds   ( NoRounds             ),
      .PermuteKey ( Seeds[i].PermuteSeed ),
      .XorKey     ( Seeds[i].XorSeed     )
    ) i_hash (
      .data_i        ( data           ),
      .hash_o        ( hash[i]        ),
      .hash_onehot_o ( onehot_hash[i] )
    );
  end
endmodule
