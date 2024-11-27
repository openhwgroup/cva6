// (C) 2001-2024 Intel Corporation. All rights reserved.
// Your use of Intel Corporation's design tools, logic functions and other 
// software and tools, and its AMPP partner logic functions, and any output 
// files from any of the foregoing (including device programming or simulation 
// files), and any associated documentation or information are expressly subject 
// to the terms and conditions of the Intel Program License Subscription 
// Agreement, Intel FPGA IP License Agreement, or other applicable 
// license agreement, including, without limitation, that your use is for the 
// sole purpose of programming logic devices manufactured by Intel and sold by 
// Intel or its authorized distributors.  Please refer to the applicable 
// agreement for further details.


// $Id: //acds/main/ip/merlin/altera_merlin_burst_adapter/altera_merlin_burst_adapter.sv#68 $
// $Revision: #68 $
// $Date: 2014/01/23 $

// -------------------------------------------------------
// Merlin Burst Adapter
// -------------------------------------------------------

`timescale 1 ns / 1 ns

// <burstwrap value> + 1
// By definition, burstwrap values are of the form 2^n - 1; adding 1 is a non-ripple operation.
module altera_merlin_burst_adapter_burstwrap_increment #(parameter WIDTH = 8)
  (
    input [WIDTH - 1:0] mask,
    output [WIDTH - 1:0] inc
  );
    assign inc[0] = ~mask[0];

    genvar i;
    generate
        for (i = 1; i < WIDTH; i = i+1) begin : burstwrap_increment_loop
          assign inc[i] = mask[i - 1] & ~mask[i];
        end
    endgenerate
endmodule

module altera_merlin_burst_adapter_adder #(parameter WIDTH = 8) (
    input cin,
    input  [WIDTH-1 : 0] a,
    input  [WIDTH-1 : 0] b,
    output [WIDTH-1 : 0] sum
  );

  genvar i;

  wire [WIDTH-1:0] carry;
  assign sum[0] = a[0] ^ b[0] ^ cin;
  assign carry[0] = a[0] & b[0] | a[0] & cin | b[0] & cin;

  generate
      for (i = 1; i < WIDTH; i = i+1) begin : full_adder_loop
          assign sum[i] = a[i] ^ b[i] ^ carry[i-1];
          assign carry[i] = a[i] & b[i] | a[i] & carry[i-1] | b[i] & carry[i-1];
      end
  endgenerate
endmodule

// a - b = a + ~b + 1
module altera_merlin_burst_adapter_subtractor #(parameter WIDTH = 8) (
    input  [WIDTH-1 : 0] a,
    input  [WIDTH-1 : 0] b,
    output [WIDTH-1 : 0] diff
  );

  altera_merlin_burst_adapter_adder #(.WIDTH (WIDTH)) subtract (
    .cin (1'b1),
    .a (a),
    .b (~b),
    .sum (diff)
  );
endmodule

// Pipeline position:
//   0: register module inputs
//   1: register module output
// I would have expected that with register retiming/duplication turned on, the
// pipeline position parameter would have no effect.  Not so,
// PIPELINE_POSITION=1 is significantly better than PIPELINE_POSITION=0.

module altera_merlin_burst_adapter_min #(parameter PKT_BYTE_CNT_W=8, PKT_BURSTWRAP_W=8, PIPELINE_POSITION = 1)
  (
    input clk,
    input reset,
    input [PKT_BYTE_CNT_W - 1 : 0] a,
    input [PKT_BYTE_CNT_W - 1 : 0] b,
    input [PKT_BURSTWRAP_W - 1 : 0] c,
    input c_enable,
    input [PKT_BYTE_CNT_W - 1 : 0] d,
    output reg [PKT_BYTE_CNT_W - 1 : 0] result
  );

    wire [PKT_BYTE_CNT_W : 0] ab_diff;
    wire [PKT_BYTE_CNT_W : 0] ac_diff;
    wire [PKT_BYTE_CNT_W : 0] bc_diff;
    wire a_lt_b;
    wire a_lt_c;
    wire b_lt_c;

    reg [PKT_BYTE_CNT_W - 1 : 0] a_reg;
    reg [PKT_BYTE_CNT_W - 1 : 0] b_reg;
    reg [PKT_BURSTWRAP_W - 1 : 0] c_reg;
    reg c_enable_reg;
    reg [PKT_BYTE_CNT_W - 1 : 0] d_reg;

    generate
      if (PIPELINE_POSITION == 0) begin
        always_ff @(posedge clk or posedge reset) begin
          if (reset) begin
            a_reg <= '0;
            b_reg <= '0;
            c_reg <= '0;
            c_enable_reg <= '0;
            d_reg <= '0;
          end
          else begin
            a_reg <= a;
            b_reg <= b;
            c_reg <= c;
            c_enable_reg <= c_enable;
            d_reg <= d;
          end
        end
      end
      else begin
        always @* begin
            a_reg = a;
            b_reg = b;
            c_reg = c;
            c_enable_reg = c_enable;
            d_reg = d;
        end
      end
    endgenerate

    altera_merlin_burst_adapter_subtractor #(.WIDTH (PKT_BYTE_CNT_W + 1)) ab_sub (
      .a ({1'b0, a_reg}),
      .b ({1'b0, b_reg}),
      .diff (ab_diff)
    );
    assign a_lt_b = ab_diff[PKT_BYTE_CNT_W];

    altera_merlin_burst_adapter_subtractor #(.WIDTH (PKT_BYTE_CNT_W + 1)) ac_sub (
      .a ({1'b0, a_reg}),
      .b ({{(PKT_BYTE_CNT_W - PKT_BURSTWRAP_W + 1) {1'b0}}, c_reg}),
      .diff (ac_diff)
    );
    assign a_lt_c = ac_diff[PKT_BYTE_CNT_W];

    altera_merlin_burst_adapter_subtractor #(.WIDTH (PKT_BYTE_CNT_W + 1)) bc_sub (
      .a ({1'b0, b_reg}),
      .b ({ {(PKT_BYTE_CNT_W - PKT_BURSTWRAP_W + 1) {1'b0}}, c_reg}),
      .diff (bc_diff)
    );
    assign b_lt_c = bc_diff[PKT_BYTE_CNT_W];

    // If d is greater than any of the values, it'll be greater than the min,
    // certainly.  If d is greater than the min, use d.  Of course, ignore c if
    // !c_enable.

    // Note: d is "number-of-symbols", of width PKT_BYTE_CNT_W. So, a constant,
    // and a power of 2 (until we support non-power-of-2 symbols/interface
    // here).
    // wire use_d = (d > a) || (d > b) || ( (d > c) && c_enable);
    // I think there's something clever I can do with masks, but my head hurts,
    // so try something simpler.
    // wire use_d =
    //   (&(~a[PKT_BYTE_CNT_W - 1:LOG2_NUMSYMBOLS])) ||
    //   (&(~b[PKT_BYTE_CNT_W-1:LOG2_NUMSYMBOLS])) ||
    //   ((&(~c[PKT_BURSTWRAP_W-1:LOG2_NUMSYMBOLS])) && c_enable
    // );
    wire [PKT_BYTE_CNT_W : 0] da_diff;
    wire [PKT_BYTE_CNT_W : 0] db_diff;
    wire [PKT_BYTE_CNT_W : 0] dc_diff;
    wire d_gt_a;
    wire d_gt_b;
    wire d_gt_c;

    altera_merlin_burst_adapter_subtractor #(.WIDTH (PKT_BYTE_CNT_W + 1)) da_sub (
      .a ({1'b0, d_reg}),
      .b ({1'b0, a_reg}),
      .diff (da_diff)
    );
    assign d_gt_a = ~da_diff[PKT_BYTE_CNT_W];

    altera_merlin_burst_adapter_subtractor #(.WIDTH (PKT_BYTE_CNT_W + 1)) db_sub (
      .a ({1'b0, d_reg}),
      .b ({1'b0, b_reg}),
      .diff (db_diff)
    );
    assign d_gt_b = ~db_diff[PKT_BYTE_CNT_W];

    altera_merlin_burst_adapter_subtractor #(.WIDTH (PKT_BYTE_CNT_W + 1)) dc_sub (
      .a ({1'b0, d_reg}),
      .b ({ {(PKT_BYTE_CNT_W - PKT_BURSTWRAP_W + 1) {1'b0}}, c_reg}),
      .diff (dc_diff)
    );
    assign d_gt_c = ~(d_reg < c_reg); // kevtan mod ~dc_diff[PKT_BYTE_CNT_W];

    wire use_d = d_gt_a || d_gt_b || (d_gt_c && c_enable_reg);

    wire [4:0] cmp = {a_lt_b, a_lt_c, b_lt_c, c_enable_reg, use_d};

    reg [PKT_BYTE_CNT_W - 1 : 0] p1_result;
    always @(a_reg or b_reg or c_reg or d_reg or cmp) begin
      casex (cmp)
        5'b00010: p1_result = c_reg;
        5'b00110: p1_result = b_reg;
        5'b01110: p1_result = b_reg;
        5'b10010: p1_result = c_reg;
        5'b11010: p1_result = a_reg;
        5'b11110: p1_result = a_reg;

        5'b00000: p1_result = b_reg;
        5'b00100: p1_result = b_reg;
        5'b01100: p1_result = b_reg;
        5'b10000: p1_result = a_reg;
        5'b11000: p1_result = a_reg;
        5'b11100: p1_result = a_reg;

        5'b????1: p1_result = d_reg;

        default: p1_result = 'X; // don't-care
      endcase
    end

    generate
      if (PIPELINE_POSITION == 1) begin
        always_ff @(posedge clk or posedge reset) begin
          if (reset) begin
            result <= '0;
          end
          else begin
            result <= p1_result;
          end
        end
      end
      else begin
        always @* begin
          result = p1_result;
        end
      end
    endgenerate
endmodule


module altera_merlin_burst_adapter_13_1
#(
  parameter // Merlin packet parameters
    PKT_BEGIN_BURST             = 81,
    PKT_ADDR_H                  = 79,
    PKT_ADDR_L                  = 48,
    PKT_BYTE_CNT_H              = 5,
    PKT_BYTE_CNT_L              = 0,
    PKT_BURSTWRAP_H             = 11,
    PKT_BURSTWRAP_L             = 6,
    PKT_TRANS_COMPRESSED_READ   = 14,
    PKT_TRANS_WRITE             = 13,
    PKT_TRANS_READ              = 12,
    PKT_BYTEEN_H                = 83,
    PKT_BYTEEN_L                = 80,
    PKT_BURST_TYPE_H            = 88,
    PKT_BURST_TYPE_L            = 87,
    PKT_BURST_SIZE_H            = 86,
    PKT_BURST_SIZE_L            = 84,
    PKT_SAI_H                   = 89,
    PKT_SAI_L                   = 89,
    PKT_EOP_OOO                 = 90,
    PKT_SOP_OOO                 = 91,    
    IN_NARROW_SIZE              = 0,
    OUT_NARROW_SIZE             = 0,
    OUT_FIXED                   = 0,
    OUT_COMPLETE_WRAP           = 0,
    ST_DATA_W                   = 92,
    ST_CHANNEL_W                = 8,
    ROLE_BASED_USER             = 0,
    ENABLE_OOO                  = 0,

    // Component-specific parameters
    BYTEENABLE_SYNTHESIS        = 0,
    BURSTWRAP_CONST_MASK        = 0,
    PIPE_INPUTS                 = 0,
    NO_WRAP_SUPPORT             = 0,
    BURSTWRAP_CONST_VALUE       = -1,
    OUT_BYTE_CNT_H              = 5,
    OUT_BURSTWRAP_H             = 11,
    SYNC_RESET                  = 0
)
(

    input clk,
    input reset,

    // -------------------
    // Command Sink (Input)
    // -------------------
    input                           sink0_valid,
    input     [ST_DATA_W-1 : 0]     sink0_data,
    input     [ST_CHANNEL_W-1 : 0]  sink0_channel,
    input                           sink0_startofpacket,
    input                           sink0_endofpacket,
    output reg                      sink0_ready,

    // -------------------
    // Command Source (Output)
    // -------------------
    output reg                      source0_valid,
    output reg [ST_DATA_W-1    : 0] source0_data,
    output reg [ST_CHANNEL_W-1 : 0] source0_channel,
    output reg                      source0_startofpacket,
    output reg                      source0_endofpacket,
    input                           source0_ready
);
  localparam
    PKT_SAI_W               = PKT_SAI_H - PKT_SAI_L + 1,
    PKT_BYTE_CNT_W          = PKT_BYTE_CNT_H - PKT_BYTE_CNT_L + 1,
    PKT_ADDR_W              = PKT_ADDR_H - PKT_ADDR_L + 1,
    PKT_BYTEEN_W            = PKT_BYTEEN_H - PKT_BYTEEN_L + 1,
    OUT_BYTE_CNT_W          = OUT_BYTE_CNT_H - PKT_BYTE_CNT_L + 1,
    OUT_BURSTWRAP_W         = OUT_BURSTWRAP_H - PKT_BURSTWRAP_L + 1,
    PKT_BURSTWRAP_W         = PKT_BURSTWRAP_H - PKT_BURSTWRAP_L + 1,
    OUT_MAX_BYTE_CNT        = 1 << (OUT_BYTE_CNT_W - 1),
    OUT_MAX_BURSTWRAP       = (1 << OUT_BURSTWRAP_W) - 1,
    NUM_SYMBOLS             = PKT_BYTEEN_H - PKT_BYTEEN_L + 1,
    PKT_BURST_SIZE_W        = PKT_BURST_SIZE_H - PKT_BURST_SIZE_L + 1,
    PKT_BURST_TYPE_W        = PKT_BURST_TYPE_H - PKT_BURST_TYPE_L + 1,
    LOG2_NUM_SYMBOLS        = (NUM_SYMBOLS == 1) ? 1 :log2ceil(NUM_SYMBOLS),
    SOP_EOP_W               = PKT_SOP_OOO - PKT_EOP_OOO + 1;    

  // "min" operation on burstwrap values is a bitwise AND.
  // Todo: one input is always set to constant OUT_MAX_BURSTWRAP; this is a
  // number of the form 2^n.  Does this fact yield an optimization?
  function [PKT_BURSTWRAP_W - 1 : 0] altera_merlin_burst_adapter_burstwrap_min(
    input [PKT_BURSTWRAP_W - 1 : 0] a, b
  );
    altera_merlin_burst_adapter_burstwrap_min = a & b;
  endfunction

    // --------------------------------------------------
    // Ceil(log2()) function
    // --------------------------------------------------
    function unsigned[63:0] log2ceil;
        input reg[63:0] val;
        reg [63:0] i;

        begin
            i = 1;
            log2ceil = 0;

            while (i < val) begin
                log2ceil = log2ceil + 1;
                i = i << 1;
            end
        end
    endfunction

  //----------------------------------------------------
  // AXSIZE encoding: run-time  size of the transaction.
  // ---------------------------------------------------
  function reg[511:0] set_byteenable_based_on_size;
      input [PKT_BURST_SIZE_W-1:0] axsize;
           begin
              case (axsize)
                  4'b0000: set_byteenable_based_on_size = 512'h00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001;
                  4'b0001: set_byteenable_based_on_size = 512'h00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003;
                  4'b0010: set_byteenable_based_on_size = 512'h0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000F;
                  4'b0011: set_byteenable_based_on_size = 512'h000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000FF;
                  4'b0100: set_byteenable_based_on_size = 512'h0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000FFFF;
                  4'b0101: set_byteenable_based_on_size = 512'h000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000FFFFFFFF;
                  4'b0110: set_byteenable_based_on_size = 512'h0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000FFFFFFFFFFFFFFFF;
                  4'b0111: set_byteenable_based_on_size = 512'h000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF;
                  4'b1000: set_byteenable_based_on_size = 512'h0000000000000000000000000000000000000000000000000000000000000000FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF;
                  4'b1001: set_byteenable_based_on_size = 512'hFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF;
                  default: set_byteenable_based_on_size = 512'h00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001;
              endcase
          end
  endfunction

  // ---------------------------------------------------
  // STATE MACHINE DEFINITIONS
  // ---------------------------------------------------
  typedef enum bit [2:0] { // int unsigned {
    ST_IDLE         = 3'b000,
    ST_COMP_TRANS   = 3'b001,   // This state is used for compressed transactions
                                // - Address and byte count needs to be calculated for every round internally
    ST_UNCOMP_TRANS = 3'b010,   // This state is used for uncompressed transaction where address is passthrough
                                // and bytecount is decremented based on max
    ST_UNCOMP_WR_SUBBURST = 3'b100
  } t_state;
  t_state state, next_state;

  // ---------------------------------------------------
  // AXI Burst Type Encoding
  // ---------------------------------------------------
  typedef enum bit  [1:0]
    {
        FIXED       = 2'b00,
        INCR        = 2'b01,
        WRAP        = 2'b10,
        RESERVED    = 2'b11
    } AxiBurstType;

  // ------------------------------
  // Note on signal naming convention used
  // in_*       --> These signals are either coming directly from sink or a combi off the sink signals
  //            --> Timing - zero cycle
  // d0_in_*    --> Signals that are to be used in this block. It is off a mux between in_* signals
  //                and the 'saved' version of the signals
  //            --> Timing - zero cycle (IF PIPE_INPUTS == 0)
  // d1_in_*    --> Signals that are output of initial flop stage.
  //            --> Timing - always delayed by 1 clock. (vs the input)

  // ------------------------------
  // CONSTANTS
  // ------------------------------
  wire [PKT_BYTE_CNT_W - 1 : 0] num_symbols_sig         = NUM_SYMBOLS [PKT_BYTE_CNT_W - 1 : 0];
  wire [PKT_BYTE_CNT_W - 1 : 0] out_max_byte_cnt_sig    = OUT_MAX_BYTE_CNT [PKT_BYTE_CNT_W - 1 : 0];

  // quartus integration failure
  wire [63:0]                       log2_numsymbols     = log2ceil(NUM_SYMBOLS);
  wire [PKT_BURST_SIZE_W - 1 : 0]   encoded_numsymbols  = log2_numsymbols[PKT_BURST_SIZE_W-1:0];

    //OOO milestones SOP_EOP chunk generation signals
  wire[SOP_EOP_W-1:0] nxt_sop_eop_chunks;
  wire                in_bytecnt_grt_out;
  wire                sop_end_bytecnt;    
  reg [SOP_EOP_W-1:0] d1_sop_eop_chunks;    
  reg                 chunk_sop;
  reg                 chunk_eop;
  reg                 burst_adapter_split;
        
  // ---------------------------------------------------
  // INPUT STAGE SIGNALS CONDITIONING
  // ---------------------------------------------------

  // Internal wires
  reg [ST_DATA_W - 1 : 0 ]              d1_in_data;
  reg [ST_CHANNEL_W - 1 : 0 ]           d1_in_channel;
  reg [PKT_BURST_SIZE_W - 1 : 0]        d1_in_size;
  reg [PKT_BURST_TYPE_W - 1 : 0]        d1_in_bursttype;
  reg [PKT_BYTEEN_W - 1 : 0]            d1_in_byteen;
  reg [PKT_BURST_SIZE_W - 1 : 0]        d0_in_size;
  reg [PKT_BURSTWRAP_W - 1 : 0]         d0_in_burstwrap;
  reg [PKT_BURST_TYPE_W - 1 : 0]        d0_in_bursttype;
  reg [PKT_ADDR_W - 1 : 0]              d0_in_addr;
  reg [PKT_BYTE_CNT_W - 1 : 0]          d0_in_bytecount;
  reg     d0_in_narrow;
  reg     d0_in_passthru;
  reg     d0_in_valid;
  reg     d0_in_sop;
  reg     d0_in_compressed_read;
  reg     d0_in_write;
  reg     d0_in_uncompressed_read;
  reg     d1_in_eop;
  reg     d1_in_uncompressed_read;
  reg     d1_in_narrow;
  reg     d1_in_passthru;
  reg     in_ready_hold;
  reg [PKT_SAI_W-1:0]  d1_in_sai;

  reg [PKT_BYTE_CNT_W - 1 : 0] the_min_byte_cnt_or_num_sym;

  wire [PKT_BURSTWRAP_W - 1 : 0] wrap_mask;
  wire [PKT_BURSTWRAP_W - 1 : 0] incremented_wrap_mask;
  reg disable_wrap_dist_calc;

  // Input stage registers
  reg [ST_DATA_W - 1 : 0]        in_data_reg;
  reg [ST_CHANNEL_W-1 : 0]       in_channel_reg;
  reg [PKT_BYTEEN_W - 1 : 0]     in_byteen_reg;
  reg [PKT_BURST_SIZE_W - 1 : 0] in_size_reg;
  reg [PKT_BURSTWRAP_W - 1 : 0]  in_burstwrap_reg;
  reg [PKT_BURST_TYPE_W - 1 : 0] in_bursttype_reg;
  reg [PKT_ADDR_W - 1 : 0]       in_addr_reg;
  reg [PKT_BYTE_CNT_W - 1 : 0]   in_bytecount_reg;
  reg in_compressed_read_reg;
  reg in_uncompressed_read_reg;
  reg in_narrow_reg;            // Holds the flag until next burst command.
  reg in_passthru_reg;          // Holds flag until next start of packet command
  reg in_eop_reg;
  reg in_bytecount_reg_zero;
  reg in_write_reg;
  reg in_valid_reg;
  reg in_sop_reg;
  reg [PKT_SAI_W-1:0]in_sai_reg;


  // Length coversion
  reg [PKT_ADDR_W - 1 : 0]       int_nxt_addr_reg;
  reg [PKT_ADDR_W - 1 : 0]       int_nxt_addr_reg_dly;
  reg [PKT_BYTE_CNT_W - 1 : 0]   int_bytes_remaining_reg;
  reg [PKT_BYTE_CNT_W - 1 : 0]   out_uncomp_byte_cnt_reg;
  reg [PKT_BURSTWRAP_W - 1 :0]   int_dist_reg;
  reg                            new_burst_reg;
  reg [PKT_BYTE_CNT_W -1:0]      int_byte_cnt_narrow_reg;

  reg [PKT_ADDR_W - 1 : 0 ]      nxt_addr;
  reg [PKT_ADDR_W - 1 : 0 ]      nxt_addr2;
  reg [PKT_BYTE_CNT_W - 1 : 0]   nxt_byte_cnt;
  reg [PKT_BYTE_CNT_W - 1 : 0]   nxt_uncomp_subburst_byte_cnt;
  reg [PKT_BYTE_CNT_W - 1 : 0]   nxt_byte_remaining;
  reg [PKT_BURSTWRAP_W - 1 : 0]  nxt_dist;
  reg [PKT_ADDR_W - 1 : 0]       extended_burstwrap;

  reg  [PKT_BYTE_CNT_W -1 :0]     d0_int_bytes_remaining;
  reg  [PKT_ADDR_W - 1 : 0 ]      d0_int_nxt_addr;
  reg  [PKT_BURSTWRAP_W - 1 : 0 ] d0_int_dist;

  // Output registers
  reg [PKT_ADDR_W - 1 : 0]      out_addr_reg;
  reg                           out_valid_reg;
  reg                           out_sop_reg;
  reg                           out_eop_reg;
  reg [PKT_BURSTWRAP_W - 1 : 0] out_burstwrap_reg;
  reg [PKT_BYTE_CNT_W - 1 : 0]  out_byte_cnt_reg;
  reg                           nxt_in_ready;
  reg [1:0]                     out_sop_eop_reg;

  wire                           nxt_out_valid;
  wire                           nxt_out_sop;
  wire                           nxt_out_eop;
  wire [PKT_BURSTWRAP_W - 1 : 0] nxt_out_burstwrap;

  // ----------------
  // ALIAS INPUT MAPPINGS
  // -----------------
  // cmd              PKT_TRANS_COMPRESSED_READ  PKT_TRANS_READ PKT_TRANS_WRITE
  // read                                     0               1               0
  // compressed read                          1               1               0
  // write                                    0               0               1
  // N.b. The fabric sets both PKT_TRANS_COMPRESSED_READ and PKT_TRANS_READ ???
  wire in_compressed_read           =   sink0_data [PKT_TRANS_COMPRESSED_READ];
  wire in_write                     =   sink0_data [PKT_TRANS_WRITE];
  wire in_read                      =   sink0_data [PKT_TRANS_READ];
  wire in_uncompressed_read         =   in_read & ~sink0_data [PKT_TRANS_COMPRESSED_READ];
  //AXI-role based user signal SAI
  wire [PKT_SAI_W-1:0] in_sai;       

  wire [ST_DATA_W - 1 : 0] in_data  = sink0_data;
  wire in_valid                     = sink0_valid & in_ready_hold;  // Fbz143820 hold ready and internal valid to zero during reset
  wire in_sop                       = sink0_startofpacket;
  wire in_eop                       = sink0_endofpacket;
  wire [ST_CHANNEL_W - 1 : 0] in_channel       = sink0_channel;

  wire [PKT_ADDR_W - 1 : 0 ]      in_addr      = sink0_data[PKT_ADDR_H : PKT_ADDR_L];
  wire [PKT_BYTEEN_W - 1 : 0]     in_byteen    = sink0_data[PKT_BYTEEN_H : PKT_BYTEEN_L];
  wire [PKT_BYTE_CNT_W - 1 : 0]   in_bytecount = sink0_data[PKT_BYTE_CNT_H : PKT_BYTE_CNT_L];
  wire [PKT_BURST_SIZE_W - 1 : 0] in_size      = IN_NARROW_SIZE ? sink0_data[PKT_BURST_SIZE_H : PKT_BURST_SIZE_L] : encoded_numsymbols;

  // Signals decoded based on inputs
  wire [PKT_BYTE_CNT_W - 1 : 0] in_burstcount  = in_bytecount >> log2_numsymbols[PKT_BYTE_CNT_W -1 :0];
  wire in_narrow                               = in_size < log2_numsymbols[PKT_BYTE_CNT_W -1 :0];
  wire in_passthru                             = in_burstcount <= 16;

  wire [PKT_BURST_TYPE_W - 1 : 0] in_bursttype = sink0_data[PKT_BURST_TYPE_H : PKT_BURST_TYPE_L];
  wire [PKT_BURSTWRAP_W - 1 : 0]  in_burstwrap;

  genvar i;
  generate
    for (i = 0; i < PKT_BURSTWRAP_W; i = i + 1) begin : assign_burstwrap_bit
      if (BURSTWRAP_CONST_MASK[i]) begin
        assign in_burstwrap[i] = BURSTWRAP_CONST_VALUE[i];
      end
      else begin
        assign in_burstwrap[i] = sink0_data[PKT_BURSTWRAP_L + i];
      end
    end
  endgenerate
 
  // Generation of internal reset synchronization
   reg internal_sclr;
   generate if (SYNC_RESET == 1) begin : rst_syncronizer
      always @ (posedge clk) begin
         internal_sclr <= reset;
      end
   end
   endgenerate
   
   //SAI extracting
   generate 
      if(ROLE_BASED_USER)
         assign in_sai =  sink0_data [PKT_SAI_H:PKT_SAI_L];
      else
         assign in_sai = '0;
   endgenerate

  // ----------------------------------
  // Input Load control signals
  // ----------------------------------

generate if (PIPE_INPUTS == 0)
 begin : NON_PIPELINED_INPUTS

  wire load_next_cmd = d0_in_valid & sink0_ready;
  wire load_next_pkt = d0_in_valid & sink0_ready & d0_in_sop;

    if (SYNC_RESET == 0 ) begin:async_rst0
     always_ff @(posedge clk or posedge reset) begin
      if (reset) begin
          in_channel_reg            <= '0;
          in_data_reg               <= '0;
          in_burstwrap_reg          <= '0;
          in_bursttype_reg          <= '0;
          in_byteen_reg             <= '0;
          in_narrow_reg             <= '0;
          in_size_reg               <= '0;
          in_passthru_reg           <= '0;
          in_eop_reg                <= '0;
          in_bytecount_reg_zero     <= '0;
          in_uncompressed_read_reg  <= '0;
          in_sai_reg                <= '0;
          
      end else begin
          if (load_next_cmd) begin
                in_channel_reg            <= in_channel;
                in_data_reg               <= in_data;
                in_burstwrap_reg          <= in_burstwrap;
                in_bursttype_reg          <= in_bursttype;
                in_byteen_reg             <= in_byteen;
                in_narrow_reg             <= in_narrow;
                in_size_reg               <= in_size;
                in_bytecount_reg_zero     <= ~|in_bytecount;
                in_uncompressed_read_reg  <= in_uncompressed_read;
                in_eop_reg                <= in_eop;
                if(in_sop)begin
                    if(ROLE_BASED_USER)
                      in_sai_reg          <= in_sai;
                     else 
                       in_sai_reg         <= '0;
                 end
            end

            if (load_next_pkt) begin
                in_passthru_reg     <= in_passthru;
            end
      end
     end
    end // async_rst0
    else begin // sync_rst0
     always_ff @(posedge clk ) begin
      if (internal_sclr) begin
                  in_channel_reg            <= '0;
                  in_data_reg               <= '0;
                  in_burstwrap_reg          <= '0;
                  in_bursttype_reg          <= '0;
                  in_byteen_reg             <= '0;
                  in_narrow_reg             <= '0;
                  in_size_reg               <= '0;
                  in_passthru_reg           <= '0;
                  in_eop_reg                <= '0;
                  in_bytecount_reg_zero     <= '0;
                  in_uncompressed_read_reg  <= '0;
      end
      else begin
            if (load_next_cmd) begin
                  in_channel_reg           <= in_channel;
                  in_data_reg              <= in_data;
                  in_burstwrap_reg         <= in_burstwrap;
                  in_bursttype_reg         <= in_bursttype;
                  in_byteen_reg            <= in_byteen;
                  in_narrow_reg            <= in_narrow;
                  in_size_reg              <= in_size;
                  in_bytecount_reg_zero    <= ~|in_bytecount;
                  in_uncompressed_read_reg <= in_uncompressed_read;
                  in_eop_reg               <= in_eop;

                if(ROLE_BASED_USER)
                    in_sai_reg       <= in_sai;
                    else 
                    in_sai_reg       <= '0;
                end

            // Passthru is evaluated every transaction
                   if (load_next_pkt) begin
                      in_passthru_reg  <= in_passthru;
                   end
      end
     end
    end // sync_rst0

  assign d0_in_size              = new_burst_reg ? in_size : in_size_reg;
  assign d0_in_addr              = in_addr;
  assign d0_in_bytecount         = in_bytecount;
  assign d0_in_burstwrap         = new_burst_reg ? in_burstwrap : in_burstwrap_reg;
  assign d0_in_bursttype         = new_burst_reg ? in_bursttype : in_bursttype_reg;
  assign d0_in_narrow            = new_burst_reg ? in_narrow    : in_narrow_reg;
  assign d0_in_passthru          = load_next_pkt ? in_passthru  : in_passthru_reg;
  assign d0_in_write             = in_write;
  assign d0_in_compressed_read   = in_compressed_read;
  assign d0_in_uncompressed_read = in_uncompressed_read;
  assign d0_in_valid             = in_valid;
  assign d0_in_sop               = in_sop;
  assign d1_in_eop               = in_eop_reg;
  assign d1_in_data              = in_data_reg;
  assign d1_in_channel           = in_channel_reg;
  assign d1_in_size              = in_size_reg;
  assign d1_in_bursttype         = in_bursttype_reg;
  assign d1_in_byteen            = in_byteen_reg;
  assign d1_in_uncompressed_read = in_uncompressed_read_reg;
  assign d1_in_narrow            = in_narrow_reg;
  assign d1_in_passthru          = in_passthru_reg;
  if (ENABLE_OOO) 
  assign d1_sop_eop_chunks       = {chunk_sop,chunk_eop};
  if(ROLE_BASED_USER)
  assign d1_in_sai               = in_sai_reg; 

 end : NON_PIPELINED_INPUTS

else
 begin : PIPELINED_INPUTS

  reg [PKT_BURST_SIZE_W - 1 : 0]        d0_int_size;
  reg [PKT_BURSTWRAP_W - 1 : 0]         d0_int_burstwrap;
  reg [PKT_BURST_TYPE_W - 1 : 0]        d0_int_bursttype;
  reg d0_int_narrow;
  reg d0_int_passthru;

  if (SYNC_RESET == 0) begin : async_rst1
     always_ff @(posedge clk or posedge reset) begin
           if (reset) begin
               in_channel_reg           <= '0;
               in_data_reg              <= '0;
               in_burstwrap_reg         <= '0;
               in_bursttype_reg         <= '0;
               in_byteen_reg            <= '0;
               in_narrow_reg            <= '0;
               in_size_reg              <= '0;
               in_addr_reg              <= '0;
               in_passthru_reg          <= '0;
               in_eop_reg               <= '0;
               in_bytecount_reg         <= '0;
               in_bytecount_reg_zero    <= '0;
               in_uncompressed_read_reg <= '0;
               in_write_reg             <= '0;
               in_compressed_read_reg   <= '0;
               in_uncompressed_read_reg <= '0;
               in_sop_reg               <= '0;
               in_valid_reg             <= '0;
               d1_in_eop                <= '0;
               d1_in_data               <= '0;
               d1_in_channel            <= '0;
               d1_in_size               <= '0;
               d1_in_bursttype          <= '0;
               d1_in_byteen             <= '0;
               d1_in_uncompressed_read  <= '0;
               d1_in_narrow             <= '0;
               d1_in_passthru           <= '0;
               d1_in_sai                <= '0; 
               d0_int_size              <= '0;
               d0_int_burstwrap         <= '0;
               d0_int_bursttype         <= '0;
               d0_int_narrow            <= '0;
               d0_int_passthru          <= '0;
               d1_sop_eop_chunks        <= '0;
           end
           else begin
                   if (sink0_ready & in_valid) begin
                           in_channel_reg           <= in_channel;
                           in_data_reg              <= in_data;
                           in_burstwrap_reg         <= in_burstwrap;
                           in_bursttype_reg         <= in_bursttype;
                           in_byteen_reg            <= in_byteen;
                           in_narrow_reg            <= in_narrow;
                           in_size_reg              <= in_size;
                           in_addr_reg              <= in_addr;
                           in_bytecount_reg         <= in_bytecount;
                           in_bytecount_reg_zero    <= ~|in_bytecount;
                           in_uncompressed_read_reg <= in_uncompressed_read;
                           in_eop_reg               <= in_eop;
                           in_write_reg             <= in_write;
                           in_compressed_read_reg   <= in_compressed_read;
                           in_uncompressed_read_reg <= in_uncompressed_read;
                           in_sop_reg               <= in_sop;
                           if(in_sop)begin
                              if(ROLE_BASED_USER)
                                 in_sai_reg  <= in_sai;
                           else 
                              in_sai_reg   <= '0;
                           end
                   end
                   // Passthru is evaluated every transaction
                   if (sink0_ready & in_sop & in_valid) begin
                      in_passthru_reg   <= in_passthru;
                   end

            if (sink0_ready) in_valid_reg  <= in_valid;

            if (  ( (state != ST_COMP_TRANS) & (~source0_valid | source0_ready)) |
                  ( (state == ST_COMP_TRANS) & (~source0_valid | source0_ready & source0_endofpacket) ) ) begin
                           d1_in_eop               <= in_eop_reg;
                           d1_in_data              <= in_data_reg;
                           d1_in_channel           <= in_channel_reg;
                           d1_in_size              <= in_size_reg;
                           d1_in_bursttype         <= in_bursttype_reg;
                           d1_in_byteen            <= in_byteen_reg;
                           d1_in_uncompressed_read <= in_uncompressed_read_reg;
                           d1_in_narrow            <= in_narrow_reg;
                           d1_in_passthru          <= in_passthru_reg;
                           if (ENABLE_OOO) 
                           d1_sop_eop_chunks       <= {chunk_sop,chunk_eop};
                           if(ROLE_BASED_USER)begin
                              d1_in_sai            <= in_sai_reg;
                           end
            end

                   if (    ( (state != ST_COMP_TRANS) & (~source0_valid | source0_ready)) |
                           ( (state == ST_COMP_TRANS) & (~source0_valid | source0_ready & source0_endofpacket) ) ) begin
              d0_int_size        <= in_size_reg;
              d0_int_burstwrap   <= in_burstwrap_reg;
              d0_int_bursttype   <= in_bursttype_reg;
              d0_int_narrow      <= in_narrow_reg;
              d0_int_passthru    <= in_passthru_reg;
            end


      end
     end
   end // async_rst1
   else begin // sync_rst1
     always_ff @(posedge clk ) begin
           if (internal_sclr) begin
               in_channel_reg           <= '0;
               in_data_reg              <= '0;
               in_burstwrap_reg         <= '0;
               in_bursttype_reg         <= '0;
               in_byteen_reg            <= '0;
               in_narrow_reg            <= '0;
               in_size_reg              <= '0;
               in_addr_reg              <= '0;
               in_passthru_reg          <= '0;
               in_eop_reg               <= '0;
               in_bytecount_reg         <= '0;
               in_bytecount_reg_zero    <= '0;
               in_uncompressed_read_reg <= '0;
               in_write_reg             <= '0;
               in_compressed_read_reg   <= '0;
               in_uncompressed_read_reg <= '0;
               in_sop_reg               <= '0;
               in_valid_reg             <= '0;
               d1_in_eop                <= '0;
               d1_in_data               <= '0;
               d1_in_channel            <= '0;
               d1_in_size               <= '0;
               d1_in_bursttype          <= '0;
               d1_in_byteen             <= '0;
               d1_in_uncompressed_read  <= '0;
               d1_in_narrow             <= '0;
               d1_in_passthru           <= '0;
               d1_in_sai                <= '0;
               d1_sop_eop_chunks        <= '0;
               d0_int_size              <= '0;
               d0_int_burstwrap         <= '0;
               d0_int_bursttype         <= '0;
               d0_int_narrow            <= '0;
               d0_int_passthru          <= '0;
           end
           else begin
                   if (sink0_ready & in_valid) begin
                           in_channel_reg           <= in_channel;
                           in_data_reg              <= in_data;
                           in_burstwrap_reg         <= in_burstwrap;
                           in_bursttype_reg         <= in_bursttype;
                           in_byteen_reg            <= in_byteen;
                           in_narrow_reg            <= in_narrow;
                           in_size_reg              <= in_size;
                           in_addr_reg              <= in_addr;
                           in_bytecount_reg         <= in_bytecount;
                           in_bytecount_reg_zero    <= ~|in_bytecount;
                           in_uncompressed_read_reg <= in_uncompressed_read;
                           in_eop_reg               <= in_eop;
                           in_write_reg             <= in_write;
                           in_compressed_read_reg   <= in_compressed_read;
                           in_uncompressed_read_reg <= in_uncompressed_read;
                           in_sop_reg               <= in_sop;
                           if(in_sop && ROLE_BASED_USER)begin
                              in_sai_reg            <= in_sai;
                           end   
                   end
                   // Passthru is evaluated every transaction
                   if (sink0_ready & in_sop & in_valid) begin
                      in_passthru_reg <= in_passthru;
                   end

            if (sink0_ready) in_valid_reg <= in_valid;

            if ( ( (state != ST_COMP_TRANS) & (~source0_valid | source0_ready)) |
                 ( (state == ST_COMP_TRANS) & (~source0_valid | source0_ready & source0_endofpacket) ) ) begin
                           d1_in_eop               <= in_eop_reg;
                           d1_in_data              <= in_data_reg;
                           d1_in_channel           <= in_channel_reg;
                           d1_in_size              <= in_size_reg;
                           d1_in_bursttype         <= in_bursttype_reg;
                           d1_in_byteen            <= in_byteen_reg;
                           d1_in_uncompressed_read <= in_uncompressed_read_reg;
                           d1_in_narrow            <= in_narrow_reg;
                           d1_in_passthru          <= in_passthru_reg;
                           if (ENABLE_OOO) 
                           d1_sop_eop_chunks       <= {chunk_sop,chunk_eop};
                           if(ROLE_BASED_USER)
                           d1_in_sai               <= in_sai_reg;
            end

            if ( ( (state != ST_COMP_TRANS) & (~source0_valid | source0_ready)) |
                 ( (state == ST_COMP_TRANS) & (~source0_valid | source0_ready & source0_endofpacket) ) ) begin
              d0_int_size        <= in_size_reg;
              d0_int_burstwrap   <= in_burstwrap_reg;
              d0_int_bursttype   <= in_bursttype_reg;
              d0_int_narrow      <= in_narrow_reg;
              d0_int_passthru    <= in_passthru_reg;
            end


      end
     end
   end // sync_rst1

  assign d0_in_size              = new_burst_reg ? in_size_reg : d0_int_size;
  assign d0_in_addr              = in_addr_reg;
  assign d0_in_bytecount         = in_bytecount_reg;
  assign d0_in_burstwrap         = new_burst_reg ? in_burstwrap_reg : d0_int_burstwrap;
  assign d0_in_bursttype         = new_burst_reg ? in_bursttype_reg : d0_int_bursttype;
  assign d0_in_narrow            = new_burst_reg ? in_narrow_reg : d0_int_narrow;
  assign d0_in_passthru          = new_burst_reg ? in_passthru_reg : d0_int_passthru;
  assign d0_in_write             = in_write_reg;
  assign d0_in_compressed_read   = in_compressed_read_reg;
  assign d0_in_uncompressed_read = in_uncompressed_read_reg;
  assign d0_in_valid             = in_valid_reg;
  assign d0_in_sop               = in_sop_reg;

 end : PIPELINED_INPUTS
endgenerate

  // -------------------------------
  // Length Calculation Input Staging.
  // -------------------------------

  reg [PKT_ADDR_W -1 : 0]       int_nxt_addr_with_offset;

  reg [PKT_BURSTWRAP_W - 1 : 0] no_wrap_dist;

  // These 2 values are part of break up of calculation from pre-flop to post-flop for timing optimization
  assign int_nxt_addr_with_offset  = int_nxt_addr_reg | extended_burstwrap & (int_nxt_addr_reg_dly + int_byte_cnt_narrow_reg);

  // Unaligned address support
  //reg [PKT_ADDR_W + LOG2_NUM_SYMBOLS - 1 : 0 ] d0_in_addr_aligned_full;
  reg [PKT_ADDR_W + log2ceil(NUM_SYMBOLS) - 1 : 0 ] d0_in_addr_aligned_full;
  altera_merlin_address_alignment
    # (
        .ADDR_W             (PKT_ADDR_W),
        .BURSTWRAP_W        (1), // Not used in burst adapter calculation usage of this module
        .TYPE_W             (0), // Not used in burst adapter calculation usage of this module
        .SIZE_W             (PKT_BURST_SIZE_W),
        .INCREMENT_ADDRESS  (0),
        .NUMSYMBOLS         (NUM_SYMBOLS),
        .SYNC_RESET         (SYNC_RESET)
        ) align_address_to_size
        (
            .clk(1'b0), .reset(1'b0), .in_valid(1'b0), .in_sop(1'b0), .in_eop(1'b0), .out_ready(),  // Dummy. Not used in INCREMENT_ADDRESS=0 settings
                                                                                                    // This block is purely combi
            .in_data    ( { d0_in_addr , d0_in_size } ),
            .out_data   ( d0_in_addr_aligned_full )
        );

  // On start of every new burst, take in new input values for calculations
  assign d0_int_bytes_remaining = new_burst_reg ? d0_in_bytecount: int_bytes_remaining_reg - out_byte_cnt_reg;
  assign d0_int_nxt_addr        = new_burst_reg ? d0_in_addr_aligned_full[PKT_ADDR_W-1:0] : int_nxt_addr_with_offset;
  assign d0_int_dist            = NO_WRAP_SUPPORT ? no_wrap_dist : incremented_wrap_mask - ( d0_int_nxt_addr[PKT_BURSTWRAP_W-1:0] & wrap_mask);

generate
 if (OUT_BURSTWRAP_W == 0) begin // Special case: 1-symbol, fixed-burst slave.
  always_comb begin
      no_wrap_dist = ~nxt_out_burstwrap[PKT_BURSTWRAP_W] ? num_symbols_sig : '1;
  end
 end

 else if (OUT_BURSTWRAP_W == 1) begin
  always_comb begin
   no_wrap_dist =  ~nxt_out_burstwrap[PKT_BURSTWRAP_W - 1] ? num_symbols_sig[PKT_BURSTWRAP_W - 1 : 0] : '1;
  end
 end

 else if (LOG2_NUM_SYMBOLS <= OUT_BURSTWRAP_W) begin
  always_comb begin
   no_wrap_dist = (|nxt_out_burstwrap[PKT_BURSTWRAP_W - 1: 0] &  ~nxt_out_burstwrap[PKT_BURSTWRAP_W - 1]) ? num_symbols_sig[PKT_BURSTWRAP_W - 1 : 0] : '1;
  end
 end
  
 else begin
  always_comb begin
     no_wrap_dist = num_symbols_sig;
  end
 end
endgenerate


  // -------------------------------
  // Output Load Control Signals
  // -------------------------------

  // Used by output flops to load in next state when:
  // 1. source has taken command (or ready to accept)
  // 2. if no command is pending (IDLE)
  wire  load_next_out_cmd   = source0_ready | ~source0_valid;

  // ---------------------------------------------------
  // INTERMEDIATE CONTROL FLAGS / HOLDING REGISTERS
  // ---------------------------------------------------

generate  
 if (OUT_BURSTWRAP_W == 0) begin // Special case: 1-symbol, fixed-burst slave.
  always_comb begin  
   disable_wrap_dist_calc      = ~d0_in_burstwrap[OUT_BURSTWRAP_W]; 
   the_min_byte_cnt_or_num_sym = d0_in_narrow ? num_symbols_sig : out_max_byte_cnt_sig;
  end
 end

 else begin
  if (OUT_NARROW_SIZE || OUT_FIXED || OUT_COMPLETE_WRAP) begin  //AXI Slave
   always_comb begin
   // When burst type is "RESERVED" it means that a fix burst wide-to-narrow has occured
   // kevtan : added highest bit of wrap mask
    disable_wrap_dist_calc       = (d0_in_passthru && d0_in_bursttype != RESERVED) | nxt_out_burstwrap[PKT_BURSTWRAP_W - 1];
    the_min_byte_cnt_or_num_sym  = (d0_in_narrow   && ~d0_in_passthru && d0_in_bursttype==WRAP) ? num_symbols_sig : out_max_byte_cnt_sig;
   // kevtan : Fbz140322 : in case of narrow transfer, chop to smallest if it's not passthru
   //                      Calculation is messed up if narrow
   //                    : added term to only chop to smallest in case of wrapping transactions
   end
  end
      
  else if (OUT_BURSTWRAP_W == PKT_BURSTWRAP_W) begin // Sequential slave
   always_comb begin  
    disable_wrap_dist_calc      = d0_in_burstwrap[PKT_BURSTWRAP_W - 1];
    the_min_byte_cnt_or_num_sym = d0_in_narrow ? num_symbols_sig : out_max_byte_cnt_sig;
   end
  end
  else begin
   always_comb begin
    // Dont really have a full story here to tell "Default?"
    // This assumes that OUT_BURSTWRAP_W < PKT_BURSTWRAP_W. Then looks at the slave's wrap boundary.
    // If d0_in_burstwrap[OUT_BURSTWRAP_W] is set, this is sequential?
    // If d0_in_burstwrap[OUT_BURSTWRAP_W - 1] is set, then it needs to be sequential to the slave?
    disable_wrap_dist_calc =  ~d0_in_burstwrap[OUT_BURSTWRAP_W] & d0_in_burstwrap[OUT_BURSTWRAP_W - 1];

    // Default case : Always try to use the slaves max byte count. If a narrow transfer occurs, follow the masters num_symbols_sig
    the_min_byte_cnt_or_num_sym = d0_in_narrow ? num_symbols_sig : out_max_byte_cnt_sig;
   end
  end
    
 end
endgenerate

  // ----------------------------------------------------
  // FSM : Finite State Machine
  // For handling the control signals for burst adapter.
  // Note: Arcs in the SM will only take effect is there's no backpressurring from the source
  // ---------------------------------------------------

  always_comb begin : state_transition
    // default
    next_state = ST_IDLE;

    case (state)
      ST_IDLE : begin
            next_state = ST_IDLE;

            if (d0_in_valid) begin
                  if (d0_in_write | d0_in_uncompressed_read)      next_state = ST_UNCOMP_TRANS;
                  if (d0_in_compressed_read)                      next_state = ST_COMP_TRANS;
            end
      end

      ST_UNCOMP_TRANS : begin
            next_state = ST_UNCOMP_TRANS;

            if (source0_endofpacket) begin
               if (~d0_in_valid) next_state = ST_IDLE;
               else begin
                  if (d0_in_write | d0_in_uncompressed_read)      next_state = ST_UNCOMP_TRANS;
                  if (d0_in_compressed_read)                      next_state = ST_COMP_TRANS;
               end
            end
        else begin
            if (|nxt_uncomp_subburst_byte_cnt)   next_state = ST_UNCOMP_WR_SUBBURST;
        end
      end

      ST_UNCOMP_WR_SUBBURST : begin
        next_state = ST_UNCOMP_WR_SUBBURST;

        if (source0_endofpacket) begin
            if (~d0_in_valid) next_state = ST_IDLE;
            else begin
                if (d0_in_write | d0_in_uncompressed_read)  next_state = ST_UNCOMP_TRANS;
                if (d0_in_compressed_read)                  next_state = ST_COMP_TRANS;
            end
        end
        else begin
            if (~|nxt_uncomp_subburst_byte_cnt)      next_state = ST_UNCOMP_TRANS;
        end
    end

      ST_COMP_TRANS : begin
        next_state = ST_COMP_TRANS;

        if (source0_endofpacket) begin
            if (~d0_in_valid) begin
                next_state = ST_IDLE;
            end
            else begin
                if (d0_in_write | d0_in_uncompressed_read)      next_state = ST_UNCOMP_TRANS;
                if (d0_in_compressed_read)                      next_state = ST_COMP_TRANS;
            end
        end
    end

  endcase
  end

  // ----------------------------------------------------
  // FSM : Controlled output control signals
  // ----------------------------------------------------

  // in_ready is asserted when:
  // 1. IDLE
  // 2. COMPRESSED TRANSACTION        : When not being back pressured by source and sending out last cmd.
  // 3. UNCOMPRESSED TRANSACTION : When not being back pressured by source

  assign nxt_in_ready = (state == ST_COMP_TRANS) ? source0_endofpacket & source0_ready | ~source0_valid :
                              (state == ST_UNCOMP_TRANS | state == ST_UNCOMP_WR_SUBBURST) ? source0_ready | ~source0_valid :
                              in_ready_hold; // Fbz143820 hold ready and internal valid to zero during reset

  // out_valid is asserted:
  // 1. Following sink_valid unless in ST_COMP_TRANS, where it's always one, unless it's endofpacket.
  assign nxt_out_valid = ((state == ST_COMP_TRANS) & ~source0_endofpacket ) ? 1'b1 : d0_in_valid;

  // out_startofpacket
  // 1. Following sink_startofpacket unless in ST_COMP_TRANS, where it's always one for first cycle before accepted.
  assign nxt_out_sop = ( (state == ST_COMP_TRANS) & source0_ready & !new_burst_reg) ? 1'b0 : d0_in_sop;

  // out_endofpacket ??
  // Follows sink_endofpacket unless in ST_COMP_TRANS, where it is a compare of whether this is the last cycle
  assign nxt_out_eop = (state == ST_COMP_TRANS) ? ( source0_ready? new_burst_reg : in_bytecount_reg_zero ) : d1_in_eop;
  
  //chunk sop_eop
    if (ENABLE_OOO) begin
       assign nxt_sop_eop_chunks = (state == ST_COMP_TRANS) ?  {out_sop_reg , new_burst_reg}  : d1_sop_eop_chunks;
    end


     generate
     if (SYNC_RESET == 0) begin : async_rst2
        always_ff @(posedge clk or posedge reset) begin
          if (reset)       begin
              state           <= ST_IDLE;
              out_valid_reg   <= '0;
              out_sop_reg     <= '0;
             in_ready_hold    <= '0;
          end else begin
            if (~source0_valid | source0_ready) begin
              state           <= next_state;
              out_valid_reg   <= nxt_out_valid;
              out_sop_reg     <= nxt_out_sop;
            end
              in_ready_hold   <= 1'b1;
          end
        end
     end // async_rst2
     else begin // sync_rst2
        always_ff @(posedge clk ) begin
          if (internal_sclr)       begin
               state           <= ST_IDLE;
               out_valid_reg   <= '0;
               out_sop_reg     <= '0;
               in_ready_hold   <= '0;
          end else begin
             if (~source0_valid | source0_ready) begin
                state           <= next_state;
                out_valid_reg   <= nxt_out_valid;
                out_sop_reg     <= nxt_out_sop;
             end
                in_ready_hold    <= 1'b1;
          end
        end
     end // sync_rst2
     endgenerate 

  assign sink0_ready = nxt_in_ready; // COMBI OUT??

  // ---------------------------------------------------
  // Converter
  // ---------------------------------------------------

  // ---------------------------------------------------
  // Wrap boundary distance calculation
  // ---------------------------------------------------

  // Wrap mask takes in nxt_out_burstwrap to handle cases where there's a wrapping Avalon slave with boundary < PKT_BURSTWRAP_W
  assign wrap_mask = disable_wrap_dist_calc ? '1 : nxt_out_burstwrap;

  // Must be valid in the cycle prior to each begin-subburst, for calculating begin_subburst_byte_cnt.
  altera_merlin_burst_adapter_burstwrap_increment #(.WIDTH (PKT_BURSTWRAP_W)) the_burstwrap_increment
  (
    .mask (wrap_mask),
    .inc (incremented_wrap_mask)
  );

  // ---------------------------------------------------
  // Length Converter
  // ---------------------------------------------------

  always_comb
   begin : EXT_BURSTWRAP
        extended_burstwrap  = { {(PKT_ADDR_W - PKT_BURSTWRAP_W) {d0_in_burstwrap[PKT_BURSTWRAP_W -1]}}, d0_in_burstwrap };
   end

  altera_merlin_burst_adapter_min #(
    .PKT_BYTE_CNT_W (PKT_BYTE_CNT_W),
    .PKT_BURSTWRAP_W (PKT_BURSTWRAP_W),
    .PIPELINE_POSITION (2) // NO PIPELINE (ALL COMBI)
    )
   the_min (
    .clk (clk),
    .reset (reset),
    .a (d0_int_bytes_remaining),
    .b (the_min_byte_cnt_or_num_sym),
    .c (d0_int_dist),
    .c_enable (~wrap_mask[PKT_BURSTWRAP_W - 1]),
    .d (num_symbols_sig),
    .result (nxt_byte_cnt)
  );

  // ---------------------------------------
  // Next Address Calculation
  // ---------------------------------------
  always_comb
   begin : NXT_ADDR_CALC

        nxt_addr  = d0_int_nxt_addr & ~extended_burstwrap;
       // this part of calculation is moved to post flop (nxt_addr2 = (extended_burstwrap & (d0_int_nxt_addr + nxt_byte_cnt_narrow));

   end

  // ---------------------------------------
  // Length Converter Registers
  // ---------------------------------------
   generate
    if (SYNC_RESET == 0) begin : async_rst3
      always_ff @(posedge clk or posedge reset) begin
       if (reset) begin
             out_byte_cnt_reg         <= '0;
             int_byte_cnt_narrow_reg  <= '0;
             int_bytes_remaining_reg  <= '0;
             int_nxt_addr_reg         <= '0;
             int_nxt_addr_reg_dly     <= '0;
             new_burst_reg            <= '0;
             out_addr_reg             <= '0;
       end
       else begin
          if (load_next_out_cmd) begin
            out_byte_cnt_reg        <= nxt_byte_cnt;
            int_byte_cnt_narrow_reg <= (nxt_byte_cnt >> log2_numsymbols[PKT_BYTE_CNT_W -1 :0]) << d0_in_size;
            int_bytes_remaining_reg      <= d0_int_bytes_remaining;
            int_nxt_addr_reg        <= nxt_addr;
            int_nxt_addr_reg_dly    <= d0_int_nxt_addr;
            // New burst is when next byte count is equal to bytes remaining. (Used only in COMPRESSED transaction)
            new_burst_reg           <= (nxt_byte_cnt == d0_int_bytes_remaining) | next_state != ST_COMP_TRANS;
            // Initial address and non-COMPRESSED transaction address does not use offset.
            out_addr_reg                <= new_burst_reg ? d0_in_addr : int_nxt_addr_with_offset;
          end
       end
      end
    end //async_rst3
    else begin // sync_rst3
      always_ff @(posedge clk ) begin
       if (internal_sclr) begin
             out_byte_cnt_reg         <= '0;
             int_byte_cnt_narrow_reg  <= '0;
             int_bytes_remaining_reg  <= '0;
             int_nxt_addr_reg         <= '0;
            int_nxt_addr_reg_dly      <= '0;
             new_burst_reg            <= '0;
             out_addr_reg             <= '0;
       end
       else begin
          if (load_next_out_cmd) begin
            out_byte_cnt_reg        <= nxt_byte_cnt;
            int_byte_cnt_narrow_reg <= (nxt_byte_cnt >> log2_numsymbols[PKT_BYTE_CNT_W -1 :0]) << d0_in_size;
            int_bytes_remaining_reg <= d0_int_bytes_remaining;
            int_nxt_addr_reg        <= nxt_addr;
            int_nxt_addr_reg_dly    <= d0_int_nxt_addr;
            // New burst is when next byte count is equal to bytes remaining. (Used only in COMPRESSED transaction)
            new_burst_reg           <= (nxt_byte_cnt == d0_int_bytes_remaining) | next_state != ST_COMP_TRANS;
            // Initial address and non-COMPRESSED transaction address does not use offset.
            out_addr_reg                <= new_burst_reg ? d0_in_addr : int_nxt_addr_with_offset;
          end
       end
      end
    end
   endgenerate
 // ----------------------------------------------------
 // Uncompressed transaction calculations
 // Address       : No changes, just pass through (handled in the flop in for out_addr_reg) // Make it to the output?
 // Byte count       : For reads, this will be just the num_symbols_sig
 //                 : For writes, it will need to decrement for subsequent reads unless it's 0,
 //               in which the next calculated byte count is used.
 // ----------------------------------------------------

  always_comb
      begin : UNCOMPRESSED_SUBBURST_BYTE_CNT_CALC

      // During start of uncompressed transaction, load the nxt_uncomp_subburst_byte_cnt with the "current output byte count - num_symbols_sig"
      // After that, on subsequent cycles, load in the 'saved' byte count value - num_symbols_sig
      // This signal is used also for transition of the state machine to ensure we will reload the byte count with the results from
      // length converter if we decremented to zero.
      // In essence, the wrap boundary is still observed and maintained. [Hence the use of the current output byte count when in ST_UNCOMP_TRANS.

      nxt_uncomp_subburst_byte_cnt  =
            (state == ST_UNCOMP_TRANS) ?
                  ( (source0_valid & source0_ready) ? out_byte_cnt_reg - num_symbols_sig : out_uncomp_byte_cnt_reg ) :
                  out_uncomp_byte_cnt_reg - ( (source0_valid & source0_ready)? num_symbols_sig : '0)  ;

   end

  generate
  if (SYNC_RESET == 0 ) begin : async_rst4
  always_ff @(posedge clk or posedge reset) begin
    if (reset) begin
            out_uncomp_byte_cnt_reg <= '0;
    end
    else begin
      if (load_next_out_cmd) begin
            out_uncomp_byte_cnt_reg <= nxt_uncomp_subburst_byte_cnt;
      end
    end
  end
 end // async_rst4
 else begin // sync_rst4
   always_ff @(posedge clk ) begin
    if (internal_sclr) begin
            out_uncomp_byte_cnt_reg <= '0;
    end
    else begin
      if (load_next_out_cmd) begin
            out_uncomp_byte_cnt_reg <= nxt_uncomp_subburst_byte_cnt;
      end
    end
  end
 end // sync_rst4
 endgenerate
  // ---------------------------------------------------
  // Burst Type Generation
  // AXI/Avalon masters - Avalon slave      - This is pass through from packet to slave
  // AXI/Avalon masters - AXI slave            - It will always be converted to INCR type
  // ---------------------------------------------------
  reg [PKT_BURST_TYPE_W - 1 : 0 ] out_bursttype;

  // bursttype will switch to INCR if repeated wraps detected (NOTE: ??)
  assign out_bursttype = ((d1_in_bursttype == RESERVED)| (~d1_in_passthru & OUT_NARROW_SIZE)) ? INCR : d1_in_bursttype;

  // ---------------------------------------------------
  // Burst Wrap Generation
  // Burst wrap is taken to be just the MIN between OUT_MAX_BURSTWRAP and the input burstwrap
  // This is to handle cases where the slave's wrapping boundary is different from the master's
  // Essentially, the master transaction characteristics are honored, but the burst wrap is modified.
  // (Arguably, this can be handled by the slave)
  // NOTE: Internally, this is used to generate the wrap_mask, so to calculate the correct wrapping distance.
  // ---------------------------------------------------

  assign nxt_out_burstwrap = altera_merlin_burst_adapter_burstwrap_min(OUT_MAX_BURSTWRAP, d0_in_burstwrap);

 generate
 if (SYNC_RESET == 0) begin : async_rst5
    always_ff @(posedge clk or posedge reset) begin
        if (reset) out_burstwrap_reg <= '0;
        else
           if ( ( (state != ST_COMP_TRANS) & (~source0_valid | source0_ready)) |
                ( (state == ST_COMP_TRANS) & (~source0_valid | source0_ready & source0_endofpacket) ) ) begin
                   out_burstwrap_reg <= nxt_out_burstwrap;
           end
    end
 end // async_rst5
 else begin // sync_rst5
    always_ff @(posedge clk ) begin
        if (internal_sclr)       out_burstwrap_reg <= '0;
        else
           if ( ( (state != ST_COMP_TRANS) & (~source0_valid | source0_ready)) |
                ( (state == ST_COMP_TRANS) & (~source0_valid | source0_ready & source0_endofpacket) ) ) begin
                   out_burstwrap_reg <= nxt_out_burstwrap;
           end
    end
 end // sync_rst5
 endgenerate
  // ---------------------------------------------------
  // Byte enable generation
  // Follow unless : in compressed transaction.
  // ---------------------------------------------------
  reg  [LOG2_NUM_SYMBOLS - 1 : 0 ] out_addr_masked;
  wire [511:0 ] d1_initial_byteen = set_byteenable_based_on_size(d1_in_size);   // To fix quartus integration error.
                                                                                // Unused bits are expected to be synthesized away
  reg  [PKT_BYTEEN_W - 1 : 0 ] out_byteen;

  // Unaligned address changes.
  // NOTE : Assumption : Byte enable is calculated for all cycles coming out from BA, and needs to be based on aligned address.
  //                     Hence, it cannot take directly output address of BA (which sends out unaligned address for 1st cycle)
  
   generate 
   if (SYNC_RESET == 0) begin : async_rst6
    always_ff @(posedge clk or posedge reset) begin
        if (reset)                  out_addr_masked <= '0;
        else
            if (load_next_out_cmd)  out_addr_masked <= new_burst_reg ? d0_in_addr_aligned_full[LOG2_NUM_SYMBOLS-1:0] : int_nxt_addr_with_offset[LOG2_NUM_SYMBOLS-1:0];
    end
   end
   else begin // sync_rst6
    always_ff @(posedge clk ) begin
        if (internal_sclr)          out_addr_masked <= '0;
        else
            if (load_next_out_cmd)  out_addr_masked <= new_burst_reg ? d0_in_addr_aligned_full[LOG2_NUM_SYMBOLS-1:0] : int_nxt_addr_with_offset[LOG2_NUM_SYMBOLS-1:0];
    end
  end // sync_rst6
  endgenerate

  always_comb begin
      if (BYTEENABLE_SYNTHESIS == 1 && d1_in_narrow == 1 && (state == ST_COMP_TRANS) )
            out_byteen   = d1_initial_byteen [NUM_SYMBOLS-1:0] << out_addr_masked;
      else
            out_byteen   = d1_in_byteen;
  end


  // ---------------------------------------------------
  // Mapping of output signals. This will help to see what is comb out or flop out
  // ---------------------------------------------------

  always_comb begin : source0_out_assignments

      source0_valid          = out_valid_reg;
      source0_startofpacket  = out_sop_reg;
      source0_endofpacket    = nxt_out_eop;       // COMBI

      // Generic assign to all data
      source0_data           = d1_in_data;
      source0_channel        = d1_in_channel;
      if (ENABLE_OOO) begin
        source0_data [PKT_SOP_OOO : PKT_EOP_OOO] = nxt_sop_eop_chunks;
      end
          // Override fields the component is aware of.
          source0_data[PKT_BYTE_CNT_H : PKT_BYTE_CNT_L]       = d1_in_uncompressed_read ? num_symbols_sig :
                                                                (state == ST_UNCOMP_WR_SUBBURST) ? out_uncomp_byte_cnt_reg :
                                                                out_byte_cnt_reg; // COMBI
          source0_data[PKT_ADDR_H : PKT_ADDR_L]               = out_addr_reg;
          source0_data[PKT_BURSTWRAP_H : PKT_BURSTWRAP_L]     = out_burstwrap_reg;
          source0_data[PKT_BURST_TYPE_H : PKT_BURST_TYPE_L]   = out_bursttype;    // COMBI
          source0_data[PKT_BYTEEN_H: PKT_BYTEEN_L]            = out_byteen;       // COMBI
      if(ROLE_BASED_USER)
          source0_data[PKT_SAI_H:PKT_SAI_L]                   = d1_in_sai;
  end



// chunk SOP & EOP generated for OOO commands to identify partial vs full command
// Based on three criteria Commands are getting splited inside BA
// 1) Fixed Burst type - if burst size is greater then boundary- incoming bursttype will be changed from 2'b00 to 2'b11
// 2) Wrap  Burst type - if burst size is greater then out max byte count and if less than max_byte count but crossed the wrap boundary 
// 3) Incr  Burst type - splits the command if its cross the out max byte count boundary
// 
generate
 if(ENABLE_OOO == 1) begin 
      assign in_bytecnt_grt_out = in_sop ? ((in_bytecount > OUT_MAX_BYTE_CNT) ? 1'b1 : (~wrap_mask[PKT_BURSTWRAP_W - 1] && d0_int_bytes_remaining != d0_int_dist )) : 1'b0;
      assign sop_end_bytecnt = (source0_valid && source0_ready) ? source0_data[PKT_BYTE_CNT_H : PKT_BYTE_CNT_L] == num_symbols_sig : 1'b0;
      if (SYNC_RESET == 0 ) begin:async_rst0
          always_ff @(posedge clk or posedge reset) begin
            if(reset)begin
               chunk_sop <= 0;
               chunk_eop <= 0;
               burst_adapter_split <= 0;
            end
            else begin
                    if(in_sop && sink0_ready && in_valid)
                       chunk_sop <= 1'b1;
                    else if (chunk_sop && sop_end_bytecnt)
                       chunk_sop <= 1'b0;
                       
                 if (sink0_ready && in_valid) begin    
                    if(in_bytecnt_grt_out )
                       burst_adapter_split <= 1'b1;
                    else if(in_eop)
                       burst_adapter_split <= 1'b0;      
                    
                    if(burst_adapter_split|| in_bytecnt_grt_out)
                       chunk_eop <= in_eop;
                    else 
                       chunk_eop <= 1'b1;
                end
            end
          end
      end // async_rst0
      else begin:async_rst0
          always_ff @(posedge clk) begin
            if(internal_sclr)begin
               chunk_sop <= 0;
               chunk_eop <= 0;
               burst_adapter_split <= 0;
            end
            else begin
               if(in_sop && sink0_ready && in_valid)
                  chunk_sop <= 1'b1;
               else if (chunk_sop && sop_end_bytecnt)
                  chunk_sop <= 1'b0;
                       
               if (sink0_ready && in_valid) begin    
                  if(in_bytecnt_grt_out )
                     burst_adapter_split <= 1'b1;
                  else if(in_eop)
                     burst_adapter_split <= 1'b0;      
                  
                  if(burst_adapter_split|| in_bytecnt_grt_out)
                     chunk_eop <= in_eop;
                  else 
                     chunk_eop <= 1'b1;
               end
            end
          end
      end // sync_rst0
end
endgenerate
endmodule


`ifdef QUESTA_INTEL_OEM
`pragma questa_oem_00 "GdrtC8041f37ha52Ko+Jde808iDyKA+ht5m5AuKQCsm3cRPQscDvF+wBgbawWOxUtCRI9a/tnC6AChwO+BxfmEV2UK9ncMFAL//YMEMfhylNbbg+DkYNRltJ3oLac/x0CKLYUz0kP213IDPHPJdDrn2XWjqkg2d8WjL/DUsL13IJgiL6ltB1LI/UYnSBUYY+yK6OwicfHT3EuyorZ8lWql/zzL2Fl1behLT6A47M1qiBb4i9YsdwGMYzE61vAElw5vv1m616hPHHmBDBpkJ0749UkjxM7iwKr/Gc3rGNZqtxL6EsB0ijIqvckNvu1y+PQvPThpv5fkTCeL/WcpBxmdZy8iujUGnWjcflr4QitV1OVkes+nk8HHy8lUFQ2O8d4LdWhQo2Wgc+JJK/8jHXzGe1ZCDVSOLqX735EqUS0Aweq+S0IeM9EspAx+loorwoXnF0KtVSz0NzGIrf1NT5domM1Nm13qVycHg6TYrxuKbJee7Am7rNj76PZ3VokChnyHJdXQrKOdGQDvQn611umz/XaRmpI6aAvzGt4FLVN4pXYBVX75OjxcjNahGvyZozOY9clcg5oTPtN1r8NbdnrIlR/WDo7+vDe7s4Ob9vElLM8tVOr38ZAv0U+tfApHYmDoadmpbtDP/goaDYSNRtuJKHxKMA04ERqZNwBh2XOVG4D/MXDnH6Z8pa5riDpBAmwfrmzUpW38iAKgUj5IoK5ccADqDXi7Xjcn5jjsKh1dRZQyPuUFyZOWyUAeVbQNV0F5FxJIMET/MmOZ7fkPEYJuxlJnc5u9/zPodiQuQs8z4QuxFB6ydTUaah1bW7pxaqUJPrR+KW/33t89d7Hus3lQFBw7A1VZUIqMGdqX82ze76b2IXhOe9xmxv68NZQcW4nrRmXd7JMFccLHOIEa6iVNBAnG9l98sWxjv1zLhfYj87HK/ntcJ1ay0YdBslC/NiL2aU5QHz74FlZGOVCedFuGuqfU+w+EzUdAgJroRlVMQw8Cm/ue39F0EBH6cBNlvG"
`endif