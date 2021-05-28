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

// Test bench for the counting bloom filter
// Randomly puts in data items into the filter.
// Removes the put in items after some time.
// One random lookup in each cycle.
// The testbench has a `control_array`, which serves as the golden model for the lookups.
// Each time a value gets put or removed into the filter, the array gets updated.
// On each lookup in the DUT it gets cross checked with the array.
// The test bench keeps book for each lookup and prints at the end the number of lookups,
// and the number of positive, false positive, negative and false negative lookups.
// The number of false negatives has to be 0 as it would indicate that the lookup was negative,
// even when the data was put in the filter. False positives are ok, because they are the result
// of hash-collisions, inherent to a counting bloom filter.

module cb_filter_tb;
  // TB parameters
  localparam time TCycle = 10ns;
  localparam time TAppli =  2ns;
  localparam time TTest  =  8ns;
  localparam int unsigned RunCycles  = 10000000;

  // DUT parameters
  localparam int unsigned NoHashes    = 32'd3;
  localparam int unsigned HashWidth   = 32'd6;
  localparam int unsigned HashRounds  = 32'd1;
  localparam int unsigned DataWidth   = 32'd11;
  localparam int unsigned BucketWidth = 32'd3;

  typedef logic [DataWidth-1:0] data_t;

  localparam cb_filter_pkg::cb_seed_t [NoHashes-1:0] Seeds = '{
    '{PermuteSeed: 32'd299034753, XorSeed: 32'd4094834 },
    '{PermuteSeed: 32'd19921030,  XorSeed: 32'd995713  },
    '{PermuteSeed: 32'd294388,    XorSeed: 32'd65146511}
  };

//---------------------------------------------------------
// Associative array as model
//---------------------------------------------------------
  logic control_array [*];
  int unsigned max_items;
  int unsigned min_items;

//---------------------------------------------------------
// Bookkeeping
//---------------------------------------------------------
  longint unsigned no_tests;
  longint unsigned no_positives;
  longint unsigned no_false_positives;
  longint unsigned no_negatives;
  longint unsigned no_false_negatives;

//---------------------------------------------------------
// DUT signals
//---------------------------------------------------------
  logic  clk;
  logic  rst_n;
  logic  sim_done;

  data_t look_data;
  logic  look_valid;
  data_t incr_data;
  logic  incr_valid;
  data_t decr_data;
  logic  decr_valid;

  logic                  filter_clear;
  logic  [HashWidth-1:0] filter_usage;
  logic                  filter_full,  filter_empty, filter_error;

  // -------------
  // Clock generator
  // -------------
  clk_rst_gen #(
    .CLK_PERIOD     ( TCycle ),
    .RST_CLK_CYCLES (       5 )
  ) i_clk_gen (
    .clk_o  (   clk ),
    .rst_no ( rst_n )
  );

  // ------------------------
  // Test Bench
  // ------------------------
  program test_cbf;
    initial begin : stimulus
      sim_done = 1'b0;
      no_tests           = 64'd0;
      no_positives       = 64'd0;
      no_false_positives = 64'd0;
      no_negatives       = 64'd0;
      no_false_negatives = 64'd0;
      init_signals();
      fork
        begin
          // simulation control branch
          max_items = 10;
          min_items =  3;
          @(posedge rst_n);
          repeat (RunCycles) @(posedge clk);
          sim_done = 1'b1;
        end
        begin
          @(posedge rst_n);
          run_lookup(sim_done);
        end
        begin
          @(posedge rst_n);
          run_increment(sim_done, decr_valid);
        end
        begin
          @(posedge rst_n);
          run_decrement(sim_done);
        end
      join
      print_result(no_tests, no_positives, no_false_positives, no_negatives, no_false_negatives);
      empty_filter();
      $stop();
    end

    task cycle_start();
      #TTest;
    endtask : cycle_start

    task cycle_end();
      @(posedge clk);
    endtask : cycle_end

    task reset_filter();
      filter_clear <= #TAppli '1;
      cycle_end();
      filter_clear <= #TAppli '0;
    endtask : reset_filter

    task init_signals();
      look_data    <= #TAppli '0;
      incr_data    <= #TAppli '0;
      incr_valid   <= #TAppli '0;
      decr_data    <= #TAppli '0;
      decr_valid   <= #TAppli '0;
      filter_clear <= #TAppli '0;
    endtask : init_signals

    // runs each cycle a lookup and tests if the output is expected
    task automatic run_lookup(ref logic sim_done);
      while (!sim_done) begin
        logic [DataWidth-1:0] lookup = $urandom_range(0,2**DataWidth-1);;
        rand_wait(0,6);
        look_data    <= #TAppli lookup;
        cycle_start();
        no_tests++;
        // check the result
        if(control_array.exists(lookup)) begin
          // the result has to be right
          if(!look_valid) begin
            $warning(1, "Had a false negative!!!\nIndex: %d", lookup);
            no_false_negatives++;
          end else begin
            no_positives++;
          end
        end else begin
          // here we can check for false positives
          if(look_valid) begin
            //$display("Had a false positive!\nIndex: %d", lookup);
            no_false_positives++;
          end else begin
            //$display("Item correctly not in Set.\nIndex: %d", lookup);
            no_negatives++;
          end
        end
        cycle_end();
      end
    endtask : run_lookup

    // randomly put data into the filter
    task automatic run_increment(ref logic sim_done, ref logic decr_valid);
      while (!sim_done) begin
        logic [DataWidth-1:0] data = $urandom_range(0,2**DataWidth-1);
        if(!control_array.exists(data)) begin
          rand_wait(0,5);
          incr_data <= #TAppli data;
          while (filter_full | (control_array.num() > max_items))
              begin if (sim_done | decr_valid) break; cycle_end(); end
          incr_valid <= #TAppli 1'b1;
          cycle_end();
          control_array[data] = 1'b1;
          incr_data  <= #TAppli '0;
          incr_valid <= #TAppli '0;
        end else begin
          cycle_end();
        end
      end
    endtask : run_increment

    // remove randomly an item from the filter
    task automatic run_decrement(ref logic sim_done);
      int unsigned nb_tryes = 0;
      while (!sim_done) begin
        logic [DataWidth-1:0] data = $urandom_range(0,2**DataWidth-1);;
        if(control_array.exists(data)) begin
          if(control_array.num() > min_items) begin
            rand_wait(0,5);
            decr_data  <= #TAppli data;
            decr_valid <= #TAppli 1'b1;
            cycle_start();
            control_array.delete(data);
            cycle_end();
            decr_data  <= #TAppli '0;
            decr_valid <= #TAppli 1'b0;
          end else begin
            cycle_end();
          end
        end else begin
          if(nb_tryes < 100) begin
            nb_tryes++;
          end else begin
            nb_tryes = 0;
            cycle_end();
          end
        end
      end
    endtask : run_decrement

    // clear the filter from all items
    task empty_filter();
      rand_wait(10,15);
      for (int unsigned i = 0; i < 2**DataWidth; i++) begin
        if(control_array.exists(i)) begin
          decr_data  <= #TAppli i;
          decr_valid <= #TAppli 1'b1;
          cycle_start();
          control_array.delete(i);
          cycle_end();
        end
      end
      // check empty flag
      decr_data  <= #TAppli '0;
      decr_valid <= #TAppli 1'b0;
      cycle_start();
      cycle_end();
      $display("Filter empty is: %b", filter_empty);
    endtask : empty_filter

    task print_result(input longint unsigned n_test, n_pos, n_f_pos, n_neg, n_f_neg);
      $info(   "######################################################");
      if (n_f_neg == 64'h0) begin
        $display("***SUCCESS***");
      end else begin
        $display("!!!FAILED!!!");
      end
      $display("Finished Tests");
      $display("NO Testes:    %d", n_test);
      $display("NO Positive:  %d", n_pos);
      $display("NO False Pos: %d", n_f_pos);
      $display("NO Negatives: %d", n_neg);
      $display("NO False Neg: %d <--- Success if this is 0!", n_f_neg);
      $display("######################################################");
    endtask : print_result

    task automatic rand_wait(input int unsigned min, max);
      int unsigned rand_success, cycles;
      rand_success = std::randomize(cycles) with {
        cycles >= min;
        cycles <= max;
      };
      assert (rand_success) else $error("Failed to randomize wait cycles!");
      repeat (cycles) @(posedge clk);
    endtask : rand_wait

  endprogram

  cb_filter #(
    .KHashes       ( NoHashes    ), // Number of hash functions
    .HashWidth     ( HashWidth   ), // Number of counters is 2**HASH_WIDTH
    .HashRounds    ( HashRounds  ),
    .InpWidth      ( DataWidth   ), // Input data width
    .BucketWidth   ( BucketWidth ), // Width of Bucket counters
    .Seeds         ( Seeds       )
  ) i_dut (
    .clk_i  ( clk   ),  // Clock
    .rst_ni ( rst_n ),  // Active low reset
    // data lookup
    .look_data_i    ( look_data    ),
    .look_valid_o   ( look_valid   ),
    // data increment
    .incr_data_i    ( incr_data    ),
    .incr_valid_i   ( incr_valid   ),
    // data decrement
    .decr_data_i    ( decr_data    ),
    .decr_valid_i   ( decr_valid   ),
    // status signals
    .filter_clear_i ( filter_clear ),
    .filter_usage_o ( filter_usage ),
    .filter_full_o  ( filter_full  ),
    .filter_empty_o ( filter_empty ),
    .filter_error_o ( filter_error )
  );
endmodule
