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

// `cb_filter`: This module implements a counting bloom filter with parameterizable hash functions.
//
// Functionality: A counting bloom filter is a data structure to efficiently implement
//                set lookups. It does so by hashing its data inputs onto multiple pointers
//                which serve as indicators for an array of buckets. For lookups can be
//                false positives, but no false negatives.
// - Seeding:     The pseudo random generators need seeds at elaboration time to generate
//                different hashes. In principle any combination of seeds can be used.
//                But one should look that the hash outputs give sufficient different patterns,
//                such that the resulting collision rate is low. The package `cb_filter_pkg`
//                contains the struct for seeding the PRG's in the hash functions.
// - Lookup:
//   - Ports:       `look_data_i`, `look_valid_o`
//   - Description: Lookup combinational, `look_valid_o` is high, when `look_data_i` was
//                  previously put into the filter.
// - Increment:
//   - Ports:       `incr_data_i`, `incr_valid_i`
//   - Description: Put data into the counting bloom filter, when valid is high.
// - Decrement:
//   - Ports:       `decr_data_i`, `decr_valid_i`
//   - Description: Remove data from the counting bloom filter. Only remove data that was
//                  previously put in, otherwise will go in a wrong state.
// - Status:
//   - `filter_clear_i`:  Clears the filter and sets all counters to 0.
//   - `filter_ussage_o`: How many data items are currently in the filter.
//   - `filter_full_o`:   Filter is full, can no longer hold more items.
//   - `filter_empty_o`:  Filter is empty.
//   - `filter_error_o`:  One of the internal counters or buckets overflowed.

// package with the struct definition for the seeds and an example
package cb_filter_pkg;
  typedef struct packed {
    int unsigned PermuteSeed;
    int unsigned XorSeed;
  } cb_seed_t;

  // example seeding struct
  localparam cb_seed_t [2:0] EgSeeds = '{
    '{PermuteSeed: 32'd299034753, XorSeed: 32'd4094834  },
    '{PermuteSeed: 32'd19921030,  XorSeed: 32'd995713   },
    '{PermuteSeed: 32'd294388,    XorSeed: 32'd65146511 }
  };
endpackage

// This is a counting bloom filter
module cb_filter #(
  parameter int unsigned KHashes     =  32'd3,  // Number of hash functions
  parameter int unsigned HashWidth   =  32'd4,  // Number of counters is 2**HashWidth
  parameter int unsigned HashRounds  =  32'd1,  // Number of permutation substitution rounds
  parameter int unsigned InpWidth    =  32'd32, // Input data width
  parameter int unsigned BucketWidth =  32'd4,  // Width of Bucket counters
  // the seeds used for seeding the PRG's inside each hash, one `cb_seed_t` per hash function.
  parameter cb_filter_pkg::cb_seed_t [KHashes-1:0] Seeds = cb_filter_pkg::EgSeeds
) (
  input  logic                 clk_i,   // Clock
  input  logic                 rst_ni,  // Active low reset
  // data lookup
  input  logic [InpWidth-1:0]  look_data_i,
  output logic                 look_valid_o,
  // data increment
  input  logic [InpWidth-1:0]  incr_data_i,
  input  logic                 incr_valid_i,
  // data decrement
  input  logic [InpWidth-1:0]  decr_data_i,
  input  logic                 decr_valid_i,
  // status signals
  input  logic                 filter_clear_i,
  output logic [HashWidth-1:0] filter_usage_o,
  output logic                 filter_full_o,
  output logic                 filter_empty_o,
  output logic                 filter_error_o
);

  localparam int unsigned NoCounters  = 2**HashWidth;

  // signal declarations
  logic [NoCounters-1:0] look_ind; // hash function pointers
  logic [NoCounters-1:0] incr_ind; // hash function pointers
  logic [NoCounters-1:0] decr_ind; // hash function pointers
  // bucket (counter signals)
  logic [NoCounters-1:0] bucket_en;
  logic [NoCounters-1:0] bucket_down;
  logic [NoCounters-1:0] bucket_occupied;
  logic [NoCounters-1:0] bucket_overflow;
  logic [NoCounters-1:0] bucket_full;
  logic [NoCounters-1:0] bucket_empty;
  // membership lookup signals
  logic [NoCounters-1:0] data_in_bucket;
  // tot count signals (filter usage)
  logic cnt_en;
  logic cnt_down;
  logic cnt_overflow;

  // -----------------------------------------
  // Lookup Hash - Membership Detection
  // -----------------------------------------
  hash_block #(
    .NoHashes     ( KHashes      ),
    .InpWidth     ( InpWidth     ),
    .HashWidth    ( HashWidth    ),
    .NoRounds     ( HashRounds   ),
    .Seeds        ( Seeds        )
  ) i_look_hashes (
    .data_i       ( look_data_i  ),
    .indicator_o  ( look_ind     )
  );
  assign data_in_bucket = look_ind & bucket_occupied;
  assign look_valid_o   = (data_in_bucket == look_ind) ? 1'b1 : 1'b0;

  // -----------------------------------------
  // Increment Hash - Add Member to Set
  // -----------------------------------------
  hash_block #(
    .NoHashes     ( KHashes      ),
    .InpWidth     ( InpWidth     ),
    .HashWidth    ( HashWidth    ),
    .NoRounds     ( HashRounds   ),
    .Seeds        ( Seeds        )
  ) i_incr_hashes (
    .data_i       ( incr_data_i  ),
    .indicator_o  ( incr_ind     )
  );

  // -----------------------------------------
  // Decrement Hash - Remove Member from Set
  // -----------------------------------------
  hash_block #(
    .NoHashes     ( KHashes      ),
    .InpWidth     ( InpWidth     ),
    .HashWidth    ( HashWidth    ),
    .NoRounds     ( HashRounds   ),
    .Seeds        ( Seeds        )
  ) i_decr_hashes (
    .data_i       ( decr_data_i  ),
    .indicator_o  ( decr_ind     )
  );

  // -----------------------------------------
  // Control the incr/decr of buckets
  // -----------------------------------------
  assign bucket_down = decr_valid_i ? decr_ind : '0;

  always_comb begin : proc_bucket_control
    case ({incr_valid_i, decr_valid_i})
      2'b00 : bucket_en = '0;
      2'b10 : bucket_en = incr_ind;
      2'b01 : bucket_en = decr_ind;
      2'b11 : bucket_en = incr_ind ^ decr_ind;
    endcase
  end

  // -----------------------------------------
  // Counters
  // -----------------------------------------
  for (genvar i = 0; i < NoCounters; i++) begin : gen_buckets
    logic [BucketWidth-1:0] bucket_content;
    counter #(
      .WIDTH( BucketWidth )
    ) i_bucket (
      .clk_i      ( clk_i             ),
      .rst_ni     ( rst_ni            ),
      .clear_i    ( filter_clear_i    ),
      .en_i       ( bucket_en[i]      ),
      .load_i     ( '0                ),
      .down_i     ( bucket_down[i]    ),
      .d_i        ( '0                ),
      .q_o        ( bucket_content    ),
      .overflow_o ( bucket_overflow[i])
    );
    assign bucket_full[i]     =  bucket_overflow[i] | (&bucket_content);
    assign bucket_occupied[i] = |bucket_content;
    assign bucket_empty[i]    = ~bucket_occupied[i];
  end

  // -----------------------------------------
  // Filter tot item counter
  // -----------------------------------------
  assign cnt_en   = incr_valid_i ^ decr_valid_i;
  assign cnt_down = decr_valid_i;
  counter #(
    .WIDTH ( HashWidth )
  ) i_tot_count (
    .clk_i     ( clk_i          ),
    .rst_ni    ( rst_ni         ),
    .clear_i   ( filter_clear_i ),
    .en_i      ( cnt_en         ),
    .load_i    ( '0             ),
    .down_i    ( cnt_down       ),
    .d_i       ( '0             ),
    .q_o       ( filter_usage_o ),
    .overflow_o( cnt_overflow   )
  );

  // -----------------------------------------
  // Filter Output Flags
  // -----------------------------------------
  assign filter_full_o  = |bucket_full;
  assign filter_empty_o = &bucket_empty;
  assign filter_error_o = |bucket_overflow | cnt_overflow;
endmodule

// gives out the or 'onehots' of all hash functions
module hash_block #(
  parameter int unsigned NoHashes                         = 32'd3,
  parameter int unsigned InpWidth                         = 32'd11,
  parameter int unsigned HashWidth                        = 32'd5,
  parameter int unsigned NoRounds                         = 32'd1,
  parameter cb_filter_pkg::cb_seed_t [NoHashes-1:0] Seeds = cb_filter_pkg::EgSeeds
) (
  input  logic [InpWidth-1:0]     data_i,
  output logic [2**HashWidth-1:0] indicator_o
);

  logic [NoHashes-1:0][2**HashWidth-1:0] hashes;

  for (genvar i = 0; i < NoHashes; i++) begin : gen_hashes
    sub_per_hash #(
      .InpWidth   ( InpWidth             ),
      .HashWidth  ( HashWidth            ),
      .NoRounds   ( NoRounds             ),
      .PermuteKey ( Seeds[i].PermuteSeed ),
      .XorKey     ( Seeds[i].XorSeed     )
    ) i_hash (
      .data_i        ( data_i    ),
      .hash_o        (           ), // not used, because we want the onehot
      .hash_onehot_o ( hashes[i] )
    );
  end

  // output assignment
  always_comb begin : proc_hash_or
    indicator_o = '0;
    for (int unsigned i = 0; i < (2**HashWidth); i++) begin
      for (int unsigned j = 0; j < NoHashes; j++) begin
        indicator_o[i] = indicator_o[i] | hashes[j][i];
      end
    end
  end

  // assertions
  initial begin
    hash_conf: assume (InpWidth > HashWidth) else
      $fatal(1, "%m:\nA Hash Function reduces the width of the input>\nInpWidth: %s\nOUT_WIDTH: %s",
          InpWidth, HashWidth);
  end
endmodule
