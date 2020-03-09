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

module fpnew_opgroup_fmt_slice #(
  parameter fpnew_pkg::opgroup_e     OpGroup       = fpnew_pkg::ADDMUL,
  parameter fpnew_pkg::fp_format_e   FpFormat      = fpnew_pkg::fp_format_e'(0),
  // FPU configuration
  parameter int unsigned             Width         = 32,
  parameter logic                    EnableVectors = 1'b1,
  parameter int unsigned             NumPipeRegs   = 0,
  parameter fpnew_pkg::pipe_config_t PipeConfig    = fpnew_pkg::BEFORE,
  parameter type                     TagType       = logic,
  // Do not change
  localparam int unsigned NUM_OPERANDS = fpnew_pkg::num_operands(OpGroup)
) (
  input logic                               clk_i,
  input logic                               rst_ni,
  // Input signals
  input logic [NUM_OPERANDS-1:0][Width-1:0] operands_i,
  input logic [NUM_OPERANDS-1:0]            is_boxed_i,
  input fpnew_pkg::roundmode_e              rnd_mode_i,
  input fpnew_pkg::operation_e              op_i,
  input logic                               op_mod_i,
  input logic                               vectorial_op_i,
  input TagType                             tag_i,
  // Input Handshake
  input  logic                              in_valid_i,
  output logic                              in_ready_o,
  input  logic                              flush_i,
  // Output signals
  output logic [Width-1:0]                  result_o,
  output fpnew_pkg::status_t                status_o,
  output logic                              extension_bit_o,
  output TagType                            tag_o,
  // Output handshake
  output logic                              out_valid_o,
  input  logic                              out_ready_i,
  // Indication of valid data in flight
  output logic                              busy_o
);

  localparam int unsigned FP_WIDTH  = fpnew_pkg::fp_width(FpFormat);
  localparam int unsigned NUM_LANES = fpnew_pkg::num_lanes(Width, FpFormat, EnableVectors);


  logic [NUM_LANES-1:0] lane_in_ready, lane_out_valid; // Handshake signals for the lanes
  logic                 vectorial_op;

  logic [NUM_LANES*FP_WIDTH-1:0] slice_result;
  logic [Width-1:0]              slice_regular_result, slice_class_result, slice_vec_class_result;

  fpnew_pkg::status_t    [NUM_LANES-1:0] lane_status;
  logic                  [NUM_LANES-1:0] lane_ext_bit; // only the first one is actually used
  fpnew_pkg::classmask_e [NUM_LANES-1:0] lane_class_mask;
  TagType                [NUM_LANES-1:0] lane_tags; // only the first one is actually used
  logic                  [NUM_LANES-1:0] lane_vectorial, lane_busy, lane_is_class; // dito

  logic result_is_vector, result_is_class;

  // -----------
  // Input Side
  // -----------
  assign in_ready_o   = lane_in_ready[0]; // Upstream ready is given by first lane
  assign vectorial_op = vectorial_op_i & EnableVectors; // only do vectorial stuff if enabled

  // ---------------
  // Generate Lanes
  // ---------------
  for (genvar lane = 0; lane < int'(NUM_LANES); lane++) begin : gen_num_lanes
    logic [FP_WIDTH-1:0] local_result; // lane-local results
    logic                local_sign;

    // Generate instances only if needed, lane 0 always generated
    if ((lane == 0) || EnableVectors) begin : active_lane
      logic in_valid, out_valid, out_ready; // lane-local handshake

      logic [NUM_OPERANDS-1:0][FP_WIDTH-1:0] local_operands; // lane-local operands
      logic [FP_WIDTH-1:0]                   op_result;      // lane-local results
      fpnew_pkg::status_t                    op_status;

      assign in_valid = in_valid_i & ((lane == 0) | vectorial_op); // upper lanes only for vectors
      // Slice out the operands for this lane
      always_comb begin : prepare_input
        for (int i = 0; i < int'(NUM_OPERANDS); i++) begin
          local_operands[i] = operands_i[i][(unsigned'(lane)+1)*FP_WIDTH-1:unsigned'(lane)*FP_WIDTH];
        end
      end

      // Instantiate the operation from the selected opgroup
      if (OpGroup == fpnew_pkg::ADDMUL) begin : lane_instance
        fpnew_fma #(
          .FpFormat    ( FpFormat    ),
          .NumPipeRegs ( NumPipeRegs ),
          .PipeConfig  ( PipeConfig  ),
          .TagType     ( TagType     ),
          .AuxType     ( logic       )
        ) i_fma (
          .clk_i,
          .rst_ni,
          .operands_i      ( local_operands               ),
          .is_boxed_i      ( is_boxed_i[NUM_OPERANDS-1:0] ),
          .rnd_mode_i,
          .op_i,
          .op_mod_i,
          .tag_i,
          .aux_i           ( vectorial_op         ), // Remember whether operation was vectorial
          .in_valid_i      ( in_valid             ),
          .in_ready_o      ( lane_in_ready[lane]  ),
          .flush_i,
          .result_o        ( op_result            ),
          .status_o        ( op_status            ),
          .extension_bit_o ( lane_ext_bit[lane]   ),
          .tag_o           ( lane_tags[lane]      ),
          .aux_o           ( lane_vectorial[lane] ),
          .out_valid_o     ( out_valid            ),
          .out_ready_i     ( out_ready            ),
          .busy_o          ( lane_busy[lane]      )
        );
        assign lane_is_class[lane]   = 1'b0;
        assign lane_class_mask[lane] = fpnew_pkg::NEGINF;
      end else if (OpGroup == fpnew_pkg::DIVSQRT) begin : lane_instance
        // fpnew_divsqrt #(
        //   .FpFormat   (FpFormat),
        //   .NumPipeRegs(NumPipeRegs),
        //   .PipeConfig (PipeConfig),
        //   .TagType    (TagType),
        //   .AuxType    (logic)
        // ) i_divsqrt (
        //   .clk_i,
        //   .rst_ni,
        //   .operands_i      ( local_operands               ),
        //   .is_boxed_i      ( is_boxed_i[NUM_OPERANDS-1:0] ),
        //   .rnd_mode_i,
        //   .op_i,
        //   .op_mod_i,
        //   .tag_i,
        //   .aux_i           ( vectorial_op         ), // Remember whether operation was vectorial
        //   .in_valid_i      ( in_valid             ),
        //   .in_ready_o      ( lane_in_ready[lane]  ),
        //   .flush_i,
        //   .result_o        ( op_result            ),
        //   .status_o        ( op_status            ),
        //   .extension_bit_o ( lane_ext_bit[lane]   ),
        //   .tag_o           ( lane_tags[lane]      ),
        //   .aux_o           ( lane_vectorial[lane] ),
        //   .out_valid_o     ( out_valid            ),
        //   .out_ready_i     ( out_ready            ),
        //   .busy_o          ( lane_busy[lane]      )
        // );
        // assign lane_is_class[lane] = 1'b0;
      end else if (OpGroup == fpnew_pkg::NONCOMP) begin : lane_instance
        fpnew_noncomp #(
          .FpFormat   (FpFormat),
          .NumPipeRegs(NumPipeRegs),
          .PipeConfig (PipeConfig),
          .TagType    (TagType),
          .AuxType    (logic)
        ) i_noncomp (
          .clk_i,
          .rst_ni,
          .operands_i      ( local_operands               ),
          .is_boxed_i      ( is_boxed_i[NUM_OPERANDS-1:0] ),
          .rnd_mode_i,
          .op_i,
          .op_mod_i,
          .tag_i,
          .aux_i           ( vectorial_op          ), // Remember whether operation was vectorial
          .in_valid_i      ( in_valid              ),
          .in_ready_o      ( lane_in_ready[lane]   ),
          .flush_i,
          .result_o        ( op_result             ),
          .status_o        ( op_status             ),
          .extension_bit_o ( lane_ext_bit[lane]    ),
          .class_mask_o    ( lane_class_mask[lane] ),
          .is_class_o      ( lane_is_class[lane]   ),
          .tag_o           ( lane_tags[lane]       ),
          .aux_o           ( lane_vectorial[lane]  ),
          .out_valid_o     ( out_valid             ),
          .out_ready_i     ( out_ready             ),
          .busy_o          ( lane_busy[lane]       )
        );
      end // ADD OTHER OPTIONS HERE

      // Handshakes are only done if the lane is actually used
      assign out_ready            = out_ready_i & ((lane == 0) | result_is_vector);
      assign lane_out_valid[lane] = out_valid   & ((lane == 0) | result_is_vector);

      // Properly NaN-box or sign-extend the slice result if not in use
      assign local_result      = lane_out_valid[lane] ? op_result : '{default: lane_ext_bit[0]};
      assign lane_status[lane] = lane_out_valid[lane] ? op_status : '0;

    // Otherwise generate constant sign-extension
    end else begin
      assign lane_out_valid[lane] = 1'b0; // unused lane
      assign lane_in_ready[lane]  = 1'b0; // unused lane
      assign local_result         = '{default: lane_ext_bit[0]}; // sign-extend/nan box
      assign lane_status[lane]    = '0;
      assign lane_busy[lane]      = 1'b0;
      assign lane_is_class[lane]  = 1'b0;
    end

    // Insert lane result into slice result
    assign slice_result[(unsigned'(lane)+1)*FP_WIDTH-1:unsigned'(lane)*FP_WIDTH] = local_result;

    // Create Classification results
    if ((lane+1)*8 <= Width) begin : vectorial_class // vectorial class blocks are 8bits in size
      assign local_sign = (lane_class_mask[lane] == fpnew_pkg::NEGINF ||
                           lane_class_mask[lane] == fpnew_pkg::NEGNORM ||
                           lane_class_mask[lane] == fpnew_pkg::NEGSUBNORM ||
                           lane_class_mask[lane] == fpnew_pkg::NEGZERO);
      // Write the current block segment
      assign slice_vec_class_result[(lane+1)*8-1:lane*8] = {
        local_sign,  // BIT 7
        ~local_sign, // BIT 6
        lane_class_mask[lane] == fpnew_pkg::QNAN, // BIT 5
        lane_class_mask[lane] == fpnew_pkg::SNAN, // BIT 4
        lane_class_mask[lane] == fpnew_pkg::POSZERO
            || lane_class_mask[lane] == fpnew_pkg::NEGZERO, // BIT 3
        lane_class_mask[lane] == fpnew_pkg::POSSUBNORM
            || lane_class_mask[lane] == fpnew_pkg::NEGSUBNORM, // BIT 2
        lane_class_mask[lane] == fpnew_pkg::POSNORM
            || lane_class_mask[lane] == fpnew_pkg::NEGNORM, // BIT 1
        lane_class_mask[lane] == fpnew_pkg::POSINF
            || lane_class_mask[lane] == fpnew_pkg::NEGINF // BIT 0
      };
    end
  end

  // ------------
  // Output Side
  // ------------
  assign result_is_vector = lane_vectorial[0];
  assign result_is_class  = lane_is_class[0];

  assign slice_regular_result = $signed({extension_bit_o, slice_result});

  localparam int unsigned CLASS_VEC_BITS = (NUM_LANES*8 > Width) ? 8 * (Width / 8) : NUM_LANES*8;

  // Pad out unused vec_class bits
  if (CLASS_VEC_BITS < Width) begin : pad_vectorial_class
    assign slice_vec_class_result[Width-1:CLASS_VEC_BITS] = '0;
  end

  // localparam logic [Width-1:0] CLASS_VEC_MASK = 2**CLASS_VEC_BITS - 1;

  assign slice_class_result = result_is_vector ? slice_vec_class_result : lane_class_mask[0];

  // Select the proper result
  assign result_o = result_is_class ? slice_class_result : slice_regular_result;

  assign extension_bit_o                              = lane_ext_bit[0]; // upper lanes unused
  assign tag_o                                        = lane_tags[0];    // upper lanes unused
  assign busy_o                                       = (| lane_busy);
  assign out_valid_o                                  = lane_out_valid[0]; // upper lanes unused


  // Collapse the lane status
  always_comb begin : output_processing
    // Collapse the status
    automatic fpnew_pkg::status_t temp_status;
    temp_status = '0;
    for (int i = 0; i < int'(NUM_LANES); i++)
      temp_status |= lane_status[i];
    status_o = temp_status;
  end
endmodule
