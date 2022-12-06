// Copyright 2019 ETH Zurich and University of Bologna.
//
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Author: Stefan Mach <smach@iis.ee.ethz.ch>

`include "common_cells/registers.svh"

module fpnew_cast_multi #(
  parameter fpnew_pkg::fmt_logic_t   FpFmtConfig  = '1,
  parameter fpnew_pkg::ifmt_logic_t  IntFmtConfig = '1,
  // FPU configuration
  parameter int unsigned             NumPipeRegs = 0,
  parameter fpnew_pkg::pipe_config_t PipeConfig  = fpnew_pkg::BEFORE,
  parameter type                     TagType     = logic,
  parameter type                     AuxType     = logic,
  // Do not change
  localparam int unsigned WIDTH = fpnew_pkg::maximum(fpnew_pkg::max_fp_width(FpFmtConfig),
                                                     fpnew_pkg::max_int_width(IntFmtConfig)),
  localparam int unsigned NUM_FORMATS = fpnew_pkg::NUM_FP_FORMATS
) (
  input  logic                   clk_i,
  input  logic                   rst_ni,
  // Input signals
  input  logic [WIDTH-1:0]       operands_i, // 1 operand
  input  logic [NUM_FORMATS-1:0] is_boxed_i, // 1 operand
  input  fpnew_pkg::roundmode_e  rnd_mode_i,
  input  fpnew_pkg::operation_e  op_i,
  input  logic                   op_mod_i,
  input  fpnew_pkg::fp_format_e  src_fmt_i,
  input  fpnew_pkg::fp_format_e  dst_fmt_i,
  input  fpnew_pkg::int_format_e int_fmt_i,
  input  TagType                 tag_i,
  input  AuxType                 aux_i,
  // Input Handshake
  input  logic                   in_valid_i,
  output logic                   in_ready_o,
  input  logic                   flush_i,
  // Output signals
  output logic [WIDTH-1:0]       result_o,
  output fpnew_pkg::status_t     status_o,
  output logic                   extension_bit_o,
  output TagType                 tag_o,
  output AuxType                 aux_o,
  // Output handshake
  output logic                   out_valid_o,
  input  logic                   out_ready_i,
  // Indication of valid data in flight
  output logic                   busy_o
);

  // ----------
  // Constants
  // ----------
  localparam int unsigned NUM_INT_FORMATS = fpnew_pkg::NUM_INT_FORMATS;
  localparam int unsigned MAX_INT_WIDTH   = fpnew_pkg::max_int_width(IntFmtConfig);

  localparam fpnew_pkg::fp_encoding_t SUPER_FORMAT = fpnew_pkg::super_format(FpFmtConfig);

  localparam int unsigned SUPER_EXP_BITS = SUPER_FORMAT.exp_bits;
  localparam int unsigned SUPER_MAN_BITS = SUPER_FORMAT.man_bits;
  localparam int unsigned SUPER_BIAS     = 2**(SUPER_EXP_BITS - 1) - 1;

  // The internal mantissa includes normal bit or an entire integer
  localparam int unsigned INT_MAN_WIDTH = fpnew_pkg::maximum(SUPER_MAN_BITS + 1, MAX_INT_WIDTH);
  // If needed, there will be a LZC for renormalization
  localparam int unsigned LZC_RESULT_WIDTH = $clog2(INT_MAN_WIDTH);
  // The internal exponent must be able to represent the smallest denormal input value as signed
  // or the number of bits in an integer
  localparam int unsigned INT_EXP_WIDTH = fpnew_pkg::maximum($clog2(MAX_INT_WIDTH),
      fpnew_pkg::maximum(SUPER_EXP_BITS, $clog2(SUPER_BIAS + SUPER_MAN_BITS))) + 1;
  // Pipelines
  localparam NUM_INP_REGS = PipeConfig == fpnew_pkg::BEFORE
                            ? NumPipeRegs
                            : (PipeConfig == fpnew_pkg::DISTRIBUTED
                               ? ((NumPipeRegs + 1) / 3) // Second to get distributed regs
                               : 0); // no regs here otherwise
  localparam NUM_MID_REGS = PipeConfig == fpnew_pkg::INSIDE
                          ? NumPipeRegs
                          : (PipeConfig == fpnew_pkg::DISTRIBUTED
                             ? ((NumPipeRegs + 2) / 3) // First to get distributed regs
                             : 0); // no regs here otherwise
  localparam NUM_OUT_REGS = PipeConfig == fpnew_pkg::AFTER
                            ? NumPipeRegs
                            : (PipeConfig == fpnew_pkg::DISTRIBUTED
                               ? (NumPipeRegs / 3) // Last to get distributed regs
                               : 0); // no regs here otherwise

  // ---------------
  // Input pipeline
  // ---------------
  // Selected pipeline output signals as non-arrays
  logic [WIDTH-1:0]       operands_q;
  logic [NUM_FORMATS-1:0] is_boxed_q;
  logic                   op_mod_q;
  fpnew_pkg::fp_format_e  src_fmt_q;
  fpnew_pkg::fp_format_e  dst_fmt_q;
  fpnew_pkg::int_format_e int_fmt_q;

  // Input pipeline signals, index i holds signal after i register stages
  logic                   [0:NUM_INP_REGS][WIDTH-1:0]       inp_pipe_operands_q;
  logic                   [0:NUM_INP_REGS][NUM_FORMATS-1:0] inp_pipe_is_boxed_q;
  fpnew_pkg::roundmode_e  [0:NUM_INP_REGS]                  inp_pipe_rnd_mode_q;
  fpnew_pkg::operation_e  [0:NUM_INP_REGS]                  inp_pipe_op_q;
  logic                   [0:NUM_INP_REGS]                  inp_pipe_op_mod_q;
  fpnew_pkg::fp_format_e  [0:NUM_INP_REGS]                  inp_pipe_src_fmt_q;
  fpnew_pkg::fp_format_e  [0:NUM_INP_REGS]                  inp_pipe_dst_fmt_q;
  fpnew_pkg::int_format_e [0:NUM_INP_REGS]                  inp_pipe_int_fmt_q;
  TagType                 [0:NUM_INP_REGS]                  inp_pipe_tag_q;
  AuxType                 [0:NUM_INP_REGS]                  inp_pipe_aux_q;
  logic                   [0:NUM_INP_REGS]                  inp_pipe_valid_q;
  // Ready signal is combinatorial for all stages
  logic [0:NUM_INP_REGS] inp_pipe_ready;

  // Input stage: First element of pipeline is taken from inputs
  assign inp_pipe_operands_q[0] = operands_i;
  assign inp_pipe_is_boxed_q[0] = is_boxed_i;
  assign inp_pipe_rnd_mode_q[0] = rnd_mode_i;
  assign inp_pipe_op_q[0]       = op_i;
  assign inp_pipe_op_mod_q[0]   = op_mod_i;
  assign inp_pipe_src_fmt_q[0]  = src_fmt_i;
  assign inp_pipe_dst_fmt_q[0]  = dst_fmt_i;
  assign inp_pipe_int_fmt_q[0]  = int_fmt_i;
  assign inp_pipe_tag_q[0]      = tag_i;
  assign inp_pipe_aux_q[0]      = aux_i;
  assign inp_pipe_valid_q[0]    = in_valid_i;
  // Input stage: Propagate pipeline ready signal to updtream circuitry
  assign in_ready_o = inp_pipe_ready[0];
  // Generate the register stages
  for (genvar i = 0; i < NUM_INP_REGS; i++) begin : gen_input_pipeline
    // Internal register enable for this stage
    logic reg_ena;
    // Determine the ready signal of the current stage - advance the pipeline:
    // 1. if the next stage is ready for our data
    // 2. if the next stage only holds a bubble (not valid) -> we can pop it
    assign inp_pipe_ready[i] = inp_pipe_ready[i+1] | ~inp_pipe_valid_q[i+1];
    // Valid: enabled by ready signal, synchronous clear with the flush signal
    `FFLARNC(inp_pipe_valid_q[i+1], inp_pipe_valid_q[i], inp_pipe_ready[i], flush_i, 1'b0, clk_i, rst_ni)
    // Enable register if pipleine ready and a valid data item is present
    assign reg_ena = inp_pipe_ready[i] & inp_pipe_valid_q[i];
    // Generate the pipeline registers within the stages, use enable-registers
    `FFL(inp_pipe_operands_q[i+1], inp_pipe_operands_q[i], reg_ena, '0)
    `FFL(inp_pipe_is_boxed_q[i+1], inp_pipe_is_boxed_q[i], reg_ena, '0)
    `FFL(inp_pipe_rnd_mode_q[i+1], inp_pipe_rnd_mode_q[i], reg_ena, fpnew_pkg::RNE)
    `FFL(inp_pipe_op_q[i+1],       inp_pipe_op_q[i],       reg_ena, fpnew_pkg::FMADD)
    `FFL(inp_pipe_op_mod_q[i+1],   inp_pipe_op_mod_q[i],   reg_ena, '0)
    `FFL(inp_pipe_src_fmt_q[i+1],  inp_pipe_src_fmt_q[i],  reg_ena, fpnew_pkg::fp_format_e'(0))
    `FFL(inp_pipe_dst_fmt_q[i+1],  inp_pipe_dst_fmt_q[i],  reg_ena, fpnew_pkg::fp_format_e'(0))
    `FFL(inp_pipe_int_fmt_q[i+1],  inp_pipe_int_fmt_q[i],  reg_ena, fpnew_pkg::int_format_e'(0))
    `FFL(inp_pipe_tag_q[i+1],      inp_pipe_tag_q[i],      reg_ena, TagType'('0))
    `FFL(inp_pipe_aux_q[i+1],      inp_pipe_aux_q[i],      reg_ena, AuxType'('0))
  end
  // Output stage: assign selected pipe outputs to signals for later use
  assign operands_q = inp_pipe_operands_q[NUM_INP_REGS];
  assign is_boxed_q = inp_pipe_is_boxed_q[NUM_INP_REGS];
  assign op_mod_q   = inp_pipe_op_mod_q[NUM_INP_REGS];
  assign src_fmt_q  = inp_pipe_src_fmt_q[NUM_INP_REGS];
  assign dst_fmt_q  = inp_pipe_dst_fmt_q[NUM_INP_REGS];
  assign int_fmt_q  = inp_pipe_int_fmt_q[NUM_INP_REGS];

  // -----------------
  // Input processing
  // -----------------
  logic src_is_int, dst_is_int; // if 0, it's a float

  assign src_is_int = (inp_pipe_op_q[NUM_INP_REGS] == fpnew_pkg::I2F);
  assign dst_is_int = (inp_pipe_op_q[NUM_INP_REGS] == fpnew_pkg::F2I);

  logic [INT_MAN_WIDTH-1:0] encoded_mant; // input mantissa with implicit bit

  logic        [NUM_FORMATS-1:0]                    fmt_sign;
  logic signed [NUM_FORMATS-1:0][INT_EXP_WIDTH-1:0] fmt_exponent;
  logic        [NUM_FORMATS-1:0][INT_MAN_WIDTH-1:0] fmt_mantissa;
  logic signed [NUM_FORMATS-1:0][INT_EXP_WIDTH-1:0] fmt_shift_compensation; // for LZC

  fpnew_pkg::fp_info_t [NUM_FORMATS-1:0] info;

  logic [NUM_INT_FORMATS-1:0][INT_MAN_WIDTH-1:0] ifmt_input_val;
  logic                                          int_sign;
  logic [INT_MAN_WIDTH-1:0]                      int_value, int_mantissa;

  // FP Input initialization
  for (genvar fmt = 0; fmt < int'(NUM_FORMATS); fmt++) begin : fmt_init_inputs
    // Set up some constants
    localparam int unsigned FP_WIDTH = fpnew_pkg::fp_width(fpnew_pkg::fp_format_e'(fmt));
    localparam int unsigned EXP_BITS = fpnew_pkg::exp_bits(fpnew_pkg::fp_format_e'(fmt));
    localparam int unsigned MAN_BITS = fpnew_pkg::man_bits(fpnew_pkg::fp_format_e'(fmt));

    if (FpFmtConfig[fmt]) begin : active_format
      // Classify input
      fpnew_classifier #(
        .FpFormat    ( fpnew_pkg::fp_format_e'(fmt) ),
        .NumOperands ( 1                            )
      ) i_fpnew_classifier (
        .operands_i ( operands_q[FP_WIDTH-1:0] ),
        .is_boxed_i ( is_boxed_q[fmt]          ),
        .info_o     ( info[fmt]                )
      );

      assign fmt_sign[fmt]     = operands_q[FP_WIDTH-1];
      assign fmt_exponent[fmt] = signed'({1'b0, operands_q[MAN_BITS+:EXP_BITS]});
      assign fmt_mantissa[fmt] = {info[fmt].is_normal, operands_q[MAN_BITS-1:0]}; // zero pad
      // Compensation for the difference in mantissa widths used for leading-zero count
      assign fmt_shift_compensation[fmt] = signed'(INT_MAN_WIDTH - 1 - MAN_BITS);
    end else begin : inactive_format
      assign info[fmt]                   = '{default: fpnew_pkg::DONT_CARE}; // format disabled
      assign fmt_sign[fmt]               = fpnew_pkg::DONT_CARE;             // format disabled
      assign fmt_exponent[fmt]           = '{default: fpnew_pkg::DONT_CARE}; // format disabled
      assign fmt_mantissa[fmt]           = '{default: fpnew_pkg::DONT_CARE}; // format disabled
      assign fmt_shift_compensation[fmt] = '{default: fpnew_pkg::DONT_CARE}; // format disabled
    end
  end

  // Sign-extend INT input
  for (genvar ifmt = 0; ifmt < int'(NUM_INT_FORMATS); ifmt++) begin : gen_sign_extend_int
    // Set up some constants
    localparam int unsigned INT_WIDTH = fpnew_pkg::int_width(fpnew_pkg::int_format_e'(ifmt));

    if (IntFmtConfig[ifmt]) begin : active_format // only active formats
      always_comb begin : sign_ext_input
        // sign-extend value only if it's signed
        ifmt_input_val[ifmt]                = '{default: operands_q[INT_WIDTH-1] & ~op_mod_q};
        ifmt_input_val[ifmt][INT_WIDTH-1:0] = operands_q[INT_WIDTH-1:0];
      end
    end else begin : inactive_format
      assign ifmt_input_val[ifmt] = '{default: fpnew_pkg::DONT_CARE}; // format disabled
    end
  end

  // Construct input mantissa from integer
  assign int_value    = ifmt_input_val[int_fmt_q];
  assign int_sign     = int_value[INT_MAN_WIDTH-1] & ~op_mod_q; // only signed ints are negative
  assign int_mantissa = int_sign ? unsigned'(-int_value) : int_value; // get magnitude of negative

  // select mantissa with source format
  assign encoded_mant = src_is_int ? int_mantissa : fmt_mantissa[src_fmt_q];

  // --------------
  // Normalization
  // --------------
  logic signed [INT_EXP_WIDTH-1:0] src_bias;      // src format bias
  logic signed [INT_EXP_WIDTH-1:0] src_exp;       // src format exponent (biased)
  logic signed [INT_EXP_WIDTH-1:0] src_subnormal; // src is subnormal
  logic signed [INT_EXP_WIDTH-1:0] src_offset;    // src offset within mantissa

  assign src_bias      = signed'(fpnew_pkg::bias(src_fmt_q));
  assign src_exp       = fmt_exponent[src_fmt_q];
  assign src_subnormal = signed'({1'b0, info[src_fmt_q].is_subnormal});
  assign src_offset    = fmt_shift_compensation[src_fmt_q];

  logic                            input_sign;   // input sign
  logic signed [INT_EXP_WIDTH-1:0] input_exp;    // unbiased true exponent
  logic        [INT_MAN_WIDTH-1:0] input_mant;   // normalized input mantissa
  logic                            mant_is_zero; // for integer zeroes

  logic signed [INT_EXP_WIDTH-1:0] fp_input_exp;
  logic signed [INT_EXP_WIDTH-1:0] int_input_exp;

  // Input mantissa needs to be normalized
  logic [LZC_RESULT_WIDTH-1:0] renorm_shamt;     // renormalization shift amount
  logic [LZC_RESULT_WIDTH:0]   renorm_shamt_sgn; // signed form for calculations

  // Leading-zero counter is needed for renormalization
  lzc #(
    .WIDTH ( INT_MAN_WIDTH ),
    .MODE  ( 1             ) // MODE = 1 counts leading zeroes
  ) i_lzc (
    .in_i    ( encoded_mant ),
    .cnt_o   ( renorm_shamt ),
    .empty_o ( mant_is_zero )
  );
  assign renorm_shamt_sgn = signed'({1'b0, renorm_shamt});

  // Get the sign from the proper source
  assign input_sign = src_is_int ? int_sign : fmt_sign[src_fmt_q];
  // Realign input mantissa, append zeroes if destination is wider
  assign input_mant = encoded_mant << renorm_shamt;
  // Unbias exponent and compensate for shift
  assign fp_input_exp  = signed'(src_exp + src_subnormal - src_bias -
                                 renorm_shamt_sgn + src_offset); // compensate for shift
  assign int_input_exp = signed'(INT_MAN_WIDTH - 1 - renorm_shamt_sgn);

  assign input_exp     = src_is_int ? int_input_exp : fp_input_exp;

  logic signed [INT_EXP_WIDTH-1:0] destination_exp;  // re-biased exponent for destination

  // Rebias the exponent
  assign destination_exp = input_exp + signed'(fpnew_pkg::bias(dst_fmt_q));

  // ---------------
  // Internal pipeline
  // ---------------
  // Pipeline output signals as non-arrays
  logic                            input_sign_q;
  logic signed [INT_EXP_WIDTH-1:0] input_exp_q;
  logic [INT_MAN_WIDTH-1:0]        input_mant_q;
  logic signed [INT_EXP_WIDTH-1:0] destination_exp_q;
  logic                            src_is_int_q;
  logic                            dst_is_int_q;
  fpnew_pkg::fp_info_t             info_q;
  logic                            mant_is_zero_q;
  logic                            op_mod_q2;
  fpnew_pkg::roundmode_e           rnd_mode_q;
  fpnew_pkg::fp_format_e           src_fmt_q2;
  fpnew_pkg::fp_format_e           dst_fmt_q2;
  fpnew_pkg::int_format_e          int_fmt_q2;
  // Internal pipeline signals, index i holds signal after i register stages


  logic                   [0:NUM_MID_REGS]                    mid_pipe_input_sign_q;
  logic signed            [0:NUM_MID_REGS][INT_EXP_WIDTH-1:0] mid_pipe_input_exp_q;
  logic                   [0:NUM_MID_REGS][INT_MAN_WIDTH-1:0] mid_pipe_input_mant_q;
  logic signed            [0:NUM_MID_REGS][INT_EXP_WIDTH-1:0] mid_pipe_dest_exp_q;
  logic                   [0:NUM_MID_REGS]                    mid_pipe_src_is_int_q;
  logic                   [0:NUM_MID_REGS]                    mid_pipe_dst_is_int_q;
  fpnew_pkg::fp_info_t    [0:NUM_MID_REGS]                    mid_pipe_info_q;
  logic                   [0:NUM_MID_REGS]                    mid_pipe_mant_zero_q;
  logic                   [0:NUM_MID_REGS]                    mid_pipe_op_mod_q;
  fpnew_pkg::roundmode_e  [0:NUM_MID_REGS]                    mid_pipe_rnd_mode_q;
  fpnew_pkg::fp_format_e  [0:NUM_MID_REGS]                    mid_pipe_src_fmt_q;
  fpnew_pkg::fp_format_e  [0:NUM_MID_REGS]                    mid_pipe_dst_fmt_q;
  fpnew_pkg::int_format_e [0:NUM_MID_REGS]                    mid_pipe_int_fmt_q;
  TagType                 [0:NUM_MID_REGS]                    mid_pipe_tag_q;
  AuxType                 [0:NUM_MID_REGS]                    mid_pipe_aux_q;
  logic                   [0:NUM_MID_REGS]                    mid_pipe_valid_q;
  // Ready signal is combinatorial for all stages
  logic [0:NUM_MID_REGS] mid_pipe_ready;

  // Input stage: First element of pipeline is taken from upstream logic
  assign mid_pipe_input_sign_q[0] = input_sign;
  assign mid_pipe_input_exp_q[0]  = input_exp;
  assign mid_pipe_input_mant_q[0] = input_mant;
  assign mid_pipe_dest_exp_q[0]   = destination_exp;
  assign mid_pipe_src_is_int_q[0] = src_is_int;
  assign mid_pipe_dst_is_int_q[0] = dst_is_int;
  assign mid_pipe_info_q[0]       = info[src_fmt_q];
  assign mid_pipe_mant_zero_q[0]  = mant_is_zero;
  assign mid_pipe_op_mod_q[0]     = op_mod_q;
  assign mid_pipe_rnd_mode_q[0]   = inp_pipe_rnd_mode_q[NUM_INP_REGS];
  assign mid_pipe_src_fmt_q[0]    = src_fmt_q;
  assign mid_pipe_dst_fmt_q[0]    = dst_fmt_q;
  assign mid_pipe_int_fmt_q[0]    = int_fmt_q;
  assign mid_pipe_tag_q[0]        = inp_pipe_tag_q[NUM_INP_REGS];
  assign mid_pipe_aux_q[0]        = inp_pipe_aux_q[NUM_INP_REGS];
  assign mid_pipe_valid_q[0]      = inp_pipe_valid_q[NUM_INP_REGS];
  // Input stage: Propagate pipeline ready signal to input pipe
  assign inp_pipe_ready[NUM_INP_REGS] = mid_pipe_ready[0];

  // Generate the register stages
  for (genvar i = 0; i < NUM_MID_REGS; i++) begin : gen_inside_pipeline
    // Internal register enable for this stage
    logic reg_ena;
    // Determine the ready signal of the current stage - advance the pipeline:
    // 1. if the next stage is ready for our data
    // 2. if the next stage only holds a bubble (not valid) -> we can pop it
    assign mid_pipe_ready[i] = mid_pipe_ready[i+1] | ~mid_pipe_valid_q[i+1];
    // Valid: enabled by ready signal, synchronous clear with the flush signal
    `FFLARNC(mid_pipe_valid_q[i+1], mid_pipe_valid_q[i], mid_pipe_ready[i], flush_i, 1'b0, clk_i, rst_ni)
    // Enable register if pipleine ready and a valid data item is present
    assign reg_ena = mid_pipe_ready[i] & mid_pipe_valid_q[i];
    // Generate the pipeline registers within the stages, use enable-registers
    `FFL(mid_pipe_input_sign_q[i+1], mid_pipe_input_sign_q[i], reg_ena, '0)
    `FFL(mid_pipe_input_exp_q[i+1],  mid_pipe_input_exp_q[i],  reg_ena, '0)
    `FFL(mid_pipe_input_mant_q[i+1], mid_pipe_input_mant_q[i], reg_ena, '0)
    `FFL(mid_pipe_dest_exp_q[i+1],   mid_pipe_dest_exp_q[i],   reg_ena, '0)
    `FFL(mid_pipe_src_is_int_q[i+1], mid_pipe_src_is_int_q[i], reg_ena, '0)
    `FFL(mid_pipe_dst_is_int_q[i+1], mid_pipe_dst_is_int_q[i], reg_ena, '0)
    `FFL(mid_pipe_info_q[i+1],       mid_pipe_info_q[i],       reg_ena, '0)
    `FFL(mid_pipe_mant_zero_q[i+1],  mid_pipe_mant_zero_q[i],  reg_ena, '0)
    `FFL(mid_pipe_op_mod_q[i+1],     mid_pipe_op_mod_q[i],     reg_ena, '0)
    `FFL(mid_pipe_rnd_mode_q[i+1],   mid_pipe_rnd_mode_q[i],   reg_ena, fpnew_pkg::RNE)
    `FFL(mid_pipe_src_fmt_q[i+1],    mid_pipe_src_fmt_q[i],    reg_ena, fpnew_pkg::fp_format_e'(0))
    `FFL(mid_pipe_dst_fmt_q[i+1],    mid_pipe_dst_fmt_q[i],    reg_ena, fpnew_pkg::fp_format_e'(0))
    `FFL(mid_pipe_int_fmt_q[i+1],    mid_pipe_int_fmt_q[i],    reg_ena, fpnew_pkg::int_format_e'(0))
    `FFL(mid_pipe_tag_q[i+1],        mid_pipe_tag_q[i],        reg_ena, TagType'('0))
    `FFL(mid_pipe_aux_q[i+1],        mid_pipe_aux_q[i],        reg_ena, AuxType'('0))
  end
  // Output stage: assign selected pipe outputs to signals for later use
  assign input_sign_q      = mid_pipe_input_sign_q[NUM_MID_REGS];
  assign input_exp_q       = mid_pipe_input_exp_q[NUM_MID_REGS];
  assign input_mant_q      = mid_pipe_input_mant_q[NUM_MID_REGS];
  assign destination_exp_q = mid_pipe_dest_exp_q[NUM_MID_REGS];
  assign src_is_int_q      = mid_pipe_src_is_int_q[NUM_MID_REGS];
  assign dst_is_int_q      = mid_pipe_dst_is_int_q[NUM_MID_REGS];
  assign info_q            = mid_pipe_info_q[NUM_MID_REGS];
  assign mant_is_zero_q    = mid_pipe_mant_zero_q[NUM_MID_REGS];
  assign op_mod_q2         = mid_pipe_op_mod_q[NUM_MID_REGS];
  assign rnd_mode_q        = mid_pipe_rnd_mode_q[NUM_MID_REGS];
  assign src_fmt_q2        = mid_pipe_src_fmt_q[NUM_MID_REGS];
  assign dst_fmt_q2        = mid_pipe_dst_fmt_q[NUM_MID_REGS];
  assign int_fmt_q2        = mid_pipe_int_fmt_q[NUM_MID_REGS];

  // --------
  // Casting
  // --------
  logic [INT_EXP_WIDTH-1:0] final_exp;        // after eventual adjustments

  logic [2*INT_MAN_WIDTH:0]  preshift_mant;    // mantissa before final shift
  logic [2*INT_MAN_WIDTH:0]  destination_mant; // mantissa from shifter, with rnd bit
  logic [SUPER_MAN_BITS-1:0] final_mant;       // mantissa after adjustments
  logic [MAX_INT_WIDTH-1:0]  final_int;        // integer shifted in position

  logic [$clog2(INT_MAN_WIDTH+1)-1:0] denorm_shamt; // shift amount for denormalization

  logic [1:0] fp_round_sticky_bits, int_round_sticky_bits, round_sticky_bits;
  logic       of_before_round, uf_before_round;


  // Perform adjustments to mantissa and exponent
  always_comb begin : cast_value
    // Default assignment
    final_exp       = unsigned'(destination_exp_q); // take exponent as is, only look at lower bits
    preshift_mant   = '0;  // initialize mantissa container with zeroes
    denorm_shamt    = SUPER_MAN_BITS - fpnew_pkg::man_bits(dst_fmt_q2); // right of mantissa
    of_before_round = 1'b0;
    uf_before_round = 1'b0;

    // Place mantissa to the left of the shifter
    preshift_mant = input_mant_q << (INT_MAN_WIDTH + 1);

    // Handle INT casts
    if (dst_is_int_q) begin
      // By default right shift mantissa to be an integer
      denorm_shamt = unsigned'(MAX_INT_WIDTH - 1 - input_exp_q);
      // overflow: when converting to unsigned the range is larger by one
      if (input_exp_q >= signed'(fpnew_pkg::int_width(int_fmt_q2) - 1 + op_mod_q2)) begin
        denorm_shamt    = '0; // prevent shifting
        of_before_round = 1'b1;
      // underflow
      end else if (input_exp_q < -1) begin
        denorm_shamt    = MAX_INT_WIDTH + 1; // all bits go to the sticky
        uf_before_round = 1'b1;
      end
    // Handle FP over-/underflows
    end else begin
      // Overflow or infinities (for proper rounding)
      if ((destination_exp_q >= signed'(2**fpnew_pkg::exp_bits(dst_fmt_q2))-1) ||
          (~src_is_int_q && info_q.is_inf)) begin
        final_exp       = unsigned'(2**fpnew_pkg::exp_bits(dst_fmt_q2)-2); // largest normal value
        preshift_mant   = '1;                           // largest normal value and RS bits set
        of_before_round = 1'b1;
      // Denormalize underflowing values
      end else if (destination_exp_q < 1 &&
                   destination_exp_q >= -signed'(fpnew_pkg::man_bits(dst_fmt_q2))) begin
        final_exp       = '0; // denormal result
        denorm_shamt    = unsigned'(denorm_shamt + 1 - destination_exp_q); // adjust right shifting
        uf_before_round = 1'b1;
      // Limit the shift to retain sticky bits
      end else if (destination_exp_q < -signed'(fpnew_pkg::man_bits(dst_fmt_q2))) begin
        final_exp       = '0; // denormal result
        denorm_shamt    = unsigned'(denorm_shamt + 2 + fpnew_pkg::man_bits(dst_fmt_q2)); // to sticky
        uf_before_round = 1'b1;
      end
    end
  end

  localparam NUM_FP_STICKY  = 2 * INT_MAN_WIDTH - SUPER_MAN_BITS - 1; // removed mantissa, 1. and R
  localparam NUM_INT_STICKY = 2 * INT_MAN_WIDTH - MAX_INT_WIDTH; // removed int and R

  // Mantissa adjustment shift
  assign destination_mant = preshift_mant >> denorm_shamt;
  // Extract final mantissa and round bit, discard the normal bit (for FP)
  assign {final_mant, fp_round_sticky_bits[1]} =
      destination_mant[2*INT_MAN_WIDTH-1-:SUPER_MAN_BITS+1];
  assign {final_int, int_round_sticky_bits[1]} = destination_mant[2*INT_MAN_WIDTH-:MAX_INT_WIDTH+1];
  // Collapse sticky bits
  assign fp_round_sticky_bits[0]  = (| {destination_mant[NUM_FP_STICKY-1:0]});
  assign int_round_sticky_bits[0] = (| {destination_mant[NUM_INT_STICKY-1:0]});

  // select RS bits for destination operation
  assign round_sticky_bits = dst_is_int_q ? int_round_sticky_bits : fp_round_sticky_bits;

  // ----------------------------
  // Rounding and classification
  // ----------------------------
  logic [WIDTH-1:0] pre_round_abs;  // absolute value of result before rnd
  logic             of_after_round; // overflow
  logic             uf_after_round; // underflow

  logic [NUM_FORMATS-1:0][WIDTH-1:0] fmt_pre_round_abs; // per format
  logic [NUM_FORMATS-1:0]            fmt_of_after_round;
  logic [NUM_FORMATS-1:0]            fmt_uf_after_round;

  logic [NUM_INT_FORMATS-1:0][WIDTH-1:0] ifmt_pre_round_abs; // per format

  logic             rounded_sign;
  logic [WIDTH-1:0] rounded_abs; // absolute value of result after rounding
  logic             result_true_zero;

  logic [WIDTH-1:0] rounded_int_res; // after possible inversion
  logic             rounded_int_res_zero; // after rounding


  // Pack exponent and mantissa into proper rounding form
  for (genvar fmt = 0; fmt < int'(NUM_FORMATS); fmt++) begin : gen_res_assemble
    // Set up some constants
    localparam int unsigned EXP_BITS = fpnew_pkg::exp_bits(fpnew_pkg::fp_format_e'(fmt));
    localparam int unsigned MAN_BITS = fpnew_pkg::man_bits(fpnew_pkg::fp_format_e'(fmt));

    if (FpFmtConfig[fmt]) begin : active_format
      always_comb begin : assemble_result
        fmt_pre_round_abs[fmt] = {final_exp[EXP_BITS-1:0], final_mant[MAN_BITS-1:0]}; // 0-extend
      end
    end else begin : inactive_format
      assign fmt_pre_round_abs[fmt] = '{default: fpnew_pkg::DONT_CARE};
    end
  end

  // Sign-extend integer result
  for (genvar ifmt = 0; ifmt < int'(NUM_INT_FORMATS); ifmt++) begin : gen_int_res_sign_ext
    // Set up some constants
    localparam int unsigned INT_WIDTH = fpnew_pkg::int_width(fpnew_pkg::int_format_e'(ifmt));

    if (IntFmtConfig[ifmt]) begin : active_format
      always_comb begin : assemble_result
        // sign-extend reusult
        ifmt_pre_round_abs[ifmt]                = '{default: final_int[INT_WIDTH-1]};
        ifmt_pre_round_abs[ifmt][INT_WIDTH-1:0] = final_int[INT_WIDTH-1:0];
      end
    end else begin : inactive_format
      assign ifmt_pre_round_abs[ifmt] = '{default: fpnew_pkg::DONT_CARE};
    end
  end

  // Select output with destination format and operation
  assign pre_round_abs = dst_is_int_q ? ifmt_pre_round_abs[int_fmt_q2] : fmt_pre_round_abs[dst_fmt_q2];

  fpnew_rounding #(
    .AbsWidth ( WIDTH )
  ) i_fpnew_rounding (
    .abs_value_i             ( pre_round_abs     ),
    .sign_i                  ( input_sign_q      ), // source format
    .round_sticky_bits_i     ( round_sticky_bits ),
    .rnd_mode_i              ( rnd_mode_q        ),
    .effective_subtraction_i ( 1'b0              ), // no operation happened
    .abs_rounded_o           ( rounded_abs       ),
    .sign_o                  ( rounded_sign      ),
    .exact_zero_o            ( result_true_zero  )
  );

  logic [NUM_FORMATS-1:0][WIDTH-1:0] fmt_result;

  // Detect overflows and inject sign
  for (genvar fmt = 0; fmt < int'(NUM_FORMATS); fmt++) begin : gen_sign_inject
    // Set up some constants
    localparam int unsigned FP_WIDTH = fpnew_pkg::fp_width(fpnew_pkg::fp_format_e'(fmt));
    localparam int unsigned EXP_BITS = fpnew_pkg::exp_bits(fpnew_pkg::fp_format_e'(fmt));
    localparam int unsigned MAN_BITS = fpnew_pkg::man_bits(fpnew_pkg::fp_format_e'(fmt));

    if (FpFmtConfig[fmt]) begin : active_format
      always_comb begin : post_process
        // detect of / uf
        fmt_uf_after_round[fmt] = rounded_abs[EXP_BITS+MAN_BITS-1:MAN_BITS] == '0; // denormal
        fmt_of_after_round[fmt] = rounded_abs[EXP_BITS+MAN_BITS-1:MAN_BITS] == '1; // inf exp.

        // Assemble regular result, nan box short ones. Int zeroes need to be detected`
        fmt_result[fmt]               = '1;
        fmt_result[fmt][FP_WIDTH-1:0] = src_is_int_q & mant_is_zero_q
                                        ? '0
                                        : {rounded_sign, rounded_abs[EXP_BITS+MAN_BITS-1:0]};
      end
    end else begin : inactive_format
      assign fmt_uf_after_round[fmt] = fpnew_pkg::DONT_CARE;
      assign fmt_of_after_round[fmt] = fpnew_pkg::DONT_CARE;
      assign fmt_result[fmt]         = '{default: fpnew_pkg::DONT_CARE};
    end
  end

  // Classification after rounding select by destination format
  assign uf_after_round = fmt_uf_after_round[dst_fmt_q2];
  assign of_after_round = fmt_of_after_round[dst_fmt_q2];

  // Negative integer result needs to be brought into two's complement
  assign rounded_int_res      = rounded_sign ? unsigned'(-rounded_abs) : rounded_abs;
  assign rounded_int_res_zero = (rounded_int_res == '0);

  // -------------------------
  // FP Special case handling
  // -------------------------
  logic [WIDTH-1:0]   fp_special_result;
  fpnew_pkg::status_t fp_special_status;
  logic               fp_result_is_special;

  logic [NUM_FORMATS-1:0][WIDTH-1:0] fmt_special_result;

  // Special result construction
  for (genvar fmt = 0; fmt < int'(NUM_FORMATS); fmt++) begin : gen_special_results
    // Set up some constants
    localparam int unsigned FP_WIDTH = fpnew_pkg::fp_width(fpnew_pkg::fp_format_e'(fmt));
    localparam int unsigned EXP_BITS = fpnew_pkg::exp_bits(fpnew_pkg::fp_format_e'(fmt));
    localparam int unsigned MAN_BITS = fpnew_pkg::man_bits(fpnew_pkg::fp_format_e'(fmt));

    localparam logic [EXP_BITS-1:0] QNAN_EXPONENT = '1;
    localparam logic [MAN_BITS-1:0] QNAN_MANTISSA = 2**(MAN_BITS-1);

    if (FpFmtConfig[fmt]) begin : active_format
      always_comb begin : special_results
        logic [FP_WIDTH-1:0] special_res;
        special_res = info_q.is_zero
                      ? input_sign_q << FP_WIDTH-1 // signed zero
                      : {1'b0, QNAN_EXPONENT, QNAN_MANTISSA}; // qNaN

        // Initialize special result with ones (NaN-box)
        fmt_special_result[fmt]               = '1;
        fmt_special_result[fmt][FP_WIDTH-1:0] = special_res;
      end
    end else begin : inactive_format
      assign fmt_special_result[fmt] = '{default: fpnew_pkg::DONT_CARE};
    end
  end

  // Detect special case from source format, I2F casts don't produce a special result
  assign fp_result_is_special = ~src_is_int_q & (info_q.is_zero |
                                                 info_q.is_nan |
                                                 ~info_q.is_boxed);

  // Signalling input NaNs raise invalid flag, otherwise no flags set
  assign fp_special_status = '{NV: info_q.is_signalling, default: 1'b0};

  // Assemble result according to destination format
  assign fp_special_result = fmt_special_result[dst_fmt_q2]; // destination format

  // --------------------------
  // INT Special case handling
  // --------------------------
  logic [WIDTH-1:0]   int_special_result;
  fpnew_pkg::status_t int_special_status;
  logic               int_result_is_special;

  logic [NUM_INT_FORMATS-1:0][WIDTH-1:0] ifmt_special_result;

  // Special result construction
  for (genvar ifmt = 0; ifmt < int'(NUM_INT_FORMATS); ifmt++) begin : gen_special_results_int
    // Set up some constants
    localparam int unsigned INT_WIDTH = fpnew_pkg::int_width(fpnew_pkg::int_format_e'(ifmt));

    if (IntFmtConfig[ifmt]) begin : active_format
      always_comb begin : special_results
        automatic logic [INT_WIDTH-1:0] special_res;

        // Default is overflow to positive max, which is 2**INT_WIDTH-1 or 2**(INT_WIDTH-1)-1
        special_res[INT_WIDTH-2:0] = '1;       // alone yields 2**(INT_WIDTH-1)-1
        special_res[INT_WIDTH-1]   = op_mod_q2; // for unsigned casts yields 2**INT_WIDTH-1

        // Negative special case (except for nans) tie to -max or 0
        if (input_sign_q && !info_q.is_nan)
          special_res = ~special_res;

        // Initialize special result with sign-extension
        ifmt_special_result[ifmt]                = '{default: special_res[INT_WIDTH-1]};
        ifmt_special_result[ifmt][INT_WIDTH-1:0] = special_res;
      end
    end else begin : inactive_format
      assign ifmt_special_result[ifmt] = '{default: fpnew_pkg::DONT_CARE};
    end
  end

  // Detect special case from source format (inf, nan, overflow, nan-boxing or negative unsigned)
  assign int_result_is_special = info_q.is_nan | info_q.is_inf |
                                 of_before_round | ~info_q.is_boxed |
                                 (input_sign_q & op_mod_q2 & ~rounded_int_res_zero);

  // All integer special cases are invalid
  assign int_special_status = '{NV: 1'b1, default: 1'b0};

  // Assemble result according to destination format
  assign int_special_result = ifmt_special_result[int_fmt_q2]; // destination format

  // -----------------
  // Result selection
  // -----------------
  fpnew_pkg::status_t int_regular_status, fp_regular_status;

  logic [WIDTH-1:0]   fp_result, int_result;
  fpnew_pkg::status_t fp_status, int_status;

  assign fp_regular_status.NV = src_is_int_q & (of_before_round | of_after_round); // overflow is invalid for I2F casts
  assign fp_regular_status.DZ = 1'b0; // no divisions
  assign fp_regular_status.OF = ~src_is_int_q & (~info_q.is_inf & (of_before_round | of_after_round)); // inf casts no OF
  assign fp_regular_status.UF = uf_after_round & fp_regular_status.NX;
  assign fp_regular_status.NX = src_is_int_q ? (| fp_round_sticky_bits) // overflow is invalid in i2f
            : (| fp_round_sticky_bits) | (~info_q.is_inf & (of_before_round | of_after_round));
  assign int_regular_status = '{NX: (| int_round_sticky_bits), default: 1'b0};

  assign fp_result  = fp_result_is_special  ? fp_special_result  : fmt_result[dst_fmt_q2];
  assign fp_status  = fp_result_is_special  ? fp_special_status  : fp_regular_status;
  assign int_result = int_result_is_special ? int_special_result : rounded_int_res;
  assign int_status = int_result_is_special ? int_special_status : int_regular_status;

  // Final results for output pipeline
  logic [WIDTH-1:0]   result_d;
  fpnew_pkg::status_t status_d;
  logic               extension_bit;

  // Select output depending on special case detection
  assign result_d = dst_is_int_q ? int_result : fp_result;
  assign status_d = dst_is_int_q ? int_status : fp_status;

  // MSB of int result decides extension, otherwise NaN box
  assign extension_bit = dst_is_int_q ? int_result[WIDTH-1] : 1'b1;

  // ----------------
  // Output Pipeline
  // ----------------
  // Output pipeline signals, index i holds signal after i register stages
  logic               [0:NUM_OUT_REGS][WIDTH-1:0] out_pipe_result_q;
  fpnew_pkg::status_t [0:NUM_OUT_REGS]            out_pipe_status_q;
  logic               [0:NUM_OUT_REGS]            out_pipe_ext_bit_q;
  TagType             [0:NUM_OUT_REGS]            out_pipe_tag_q;
  AuxType             [0:NUM_OUT_REGS]            out_pipe_aux_q;
  logic               [0:NUM_OUT_REGS]            out_pipe_valid_q;
  // Ready signal is combinatorial for all stages
  logic [0:NUM_OUT_REGS] out_pipe_ready;

  // Input stage: First element of pipeline is taken from inputs
  assign out_pipe_result_q[0]  = result_d;
  assign out_pipe_status_q[0]  = status_d;
  assign out_pipe_ext_bit_q[0] = extension_bit;
  assign out_pipe_tag_q[0]     = mid_pipe_tag_q[NUM_MID_REGS];
  assign out_pipe_aux_q[0]     = mid_pipe_aux_q[NUM_MID_REGS];
  assign out_pipe_valid_q[0]   = mid_pipe_valid_q[NUM_MID_REGS];
  // Input stage: Propagate pipeline ready signal to inside pipe
  assign mid_pipe_ready[NUM_MID_REGS] = out_pipe_ready[0];
  // Generate the register stages
  for (genvar i = 0; i < NUM_OUT_REGS; i++) begin : gen_output_pipeline
    // Internal register enable for this stage
    logic reg_ena;
    // Determine the ready signal of the current stage - advance the pipeline:
    // 1. if the next stage is ready for our data
    // 2. if the next stage only holds a bubble (not valid) -> we can pop it
    assign out_pipe_ready[i] = out_pipe_ready[i+1] | ~out_pipe_valid_q[i+1];
    // Valid: enabled by ready signal, synchronous clear with the flush signal
    `FFLARNC(out_pipe_valid_q[i+1], out_pipe_valid_q[i], out_pipe_ready[i], flush_i, 1'b0, clk_i, rst_ni)
    // Enable register if pipleine ready and a valid data item is present
    assign reg_ena = out_pipe_ready[i] & out_pipe_valid_q[i];
    // Generate the pipeline registers within the stages, use enable-registers
    `FFL(out_pipe_result_q[i+1],  out_pipe_result_q[i],  reg_ena, '0)
    `FFL(out_pipe_status_q[i+1],  out_pipe_status_q[i],  reg_ena, '0)
    `FFL(out_pipe_ext_bit_q[i+1], out_pipe_ext_bit_q[i], reg_ena, '0)
    `FFL(out_pipe_tag_q[i+1],     out_pipe_tag_q[i],     reg_ena, TagType'('0))
    `FFL(out_pipe_aux_q[i+1],     out_pipe_aux_q[i],     reg_ena, AuxType'('0))
  end
  // Output stage: Ready travels backwards from output side, driven by downstream circuitry
  assign out_pipe_ready[NUM_OUT_REGS] = out_ready_i;
  // Output stage: assign module outputs
  assign result_o        = out_pipe_result_q[NUM_OUT_REGS];
  assign status_o        = out_pipe_status_q[NUM_OUT_REGS];
  assign extension_bit_o = out_pipe_ext_bit_q[NUM_OUT_REGS];
  assign tag_o           = out_pipe_tag_q[NUM_OUT_REGS];
  assign aux_o           = out_pipe_aux_q[NUM_OUT_REGS];
  assign out_valid_o     = out_pipe_valid_q[NUM_OUT_REGS];
  assign busy_o          = (| {inp_pipe_valid_q, mid_pipe_valid_q, out_pipe_valid_q});
endmodule
