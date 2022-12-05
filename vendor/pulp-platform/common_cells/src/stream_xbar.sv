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

/// Fully connected stream crossbar.
///
/// Handshaking rules as defined by the `AMBA AXI` standard on default.
module stream_xbar #(
  /// Number of inputs into the crossbar (`> 0`).
  parameter int unsigned NumInp      = 32'd0,
  /// Number of outputs from the crossbar (`> 0`).
  parameter int unsigned NumOut      = 32'd0,
  /// Data width of the stream. Can be overwritten by defining the type parameter `payload_t`.
  parameter int unsigned DataWidth   = 32'd1,
  /// Payload type of the data ports, only usage of parameter `DataWidth`.
  parameter type         payload_t   = logic [DataWidth-1:0],
  /// Adds a spill register stage at each output.
  parameter bit          OutSpillReg = 1'b0,
  /// Use external priority for the individual `rr_arb_trees`.
  parameter int unsigned ExtPrio     = 1'b0,
  /// Use strict AXI valid ready handshaking.
  /// To be protocol conform also the parameter `LockIn` has to be set.
  parameter int unsigned AxiVldRdy   = 1'b1,
  /// Lock in the arbitration decision of the `rr_arb_tree`.
  /// When this is set, valids have to be asserted until the corresponding transaction is indicated
  /// by ready.
  parameter int unsigned LockIn      = 1'b1,
  /// Derived parameter, do **not** overwrite!
  ///
  /// Width of the output selection signal.
  parameter int unsigned SelWidth = (NumOut > 32'd1) ? unsigned'($clog2(NumOut)) : 32'd1,
  /// Derived parameter, do **not** overwrite!
  ///
  /// Signal type definition for selecting the output at the inputs.
  parameter type sel_oup_t = logic[SelWidth-1:0],
  /// Derived parameter, do **not** overwrite!
  ///
  /// Width of the input index signal.
  parameter int unsigned IdxWidth = (NumInp > 32'd1) ? unsigned'($clog2(NumInp)) : 32'd1,
  /// Derived parameter, do **not** overwrite!
  ///
  /// Signal type definition indicating from which input the output came.
  parameter type idx_inp_t = logic[IdxWidth-1:0]
) (
  /// Clock, positive edge triggered.
  input  logic                  clk_i,
  /// Asynchronous reset, active low.
  input  logic                  rst_ni,
  /// Flush the state of the internal `rr_arb_tree` modules.
  /// If not used set to `0`.
  /// Flush should only be used if there are no active `valid_i`, otherwise it will
  /// not adhere to the AXI handshaking.
  input  logic                  flush_i,
  /// Provide an external state for the `rr_arb_tree` models.
  /// Will only do something if ExtPrio is `1` otherwise tie to `0`.
  input  idx_inp_t [NumOut-1:0] rr_i,
  /// Input data ports.
  /// Has to be stable as long as `valid_i` is asserted when parameter `AxiVldRdy` is set.
  input  payload_t [NumInp-1:0] data_i,
  /// Selection of the output port where the data should be routed.
  /// Has to be stable as long as `valid_i` is asserted and parameter `AxiVldRdy` is set.
  input  sel_oup_t [NumInp-1:0] sel_i,
  /// Input is valid.
  input  logic     [NumInp-1:0] valid_i,
  /// Input is ready to accept data.
  output logic     [NumInp-1:0] ready_o,
  /// Output data ports. Valid if `valid_o = 1`
  output payload_t [NumOut-1:0] data_o,
  /// Index of the input port where data came from.
  output idx_inp_t [NumOut-1:0] idx_o,
  /// Output is valid.
  output logic     [NumOut-1:0] valid_o,
  /// Output can be accepted.
  input  logic     [NumOut-1:0] ready_i
);
  typedef struct packed {
    payload_t data;
    idx_inp_t idx;
  } spill_data_t;

  logic     [NumInp-1:0][NumOut-1:0] inp_valid;
  logic     [NumInp-1:0][NumOut-1:0] inp_ready;

  payload_t [NumOut-1:0][NumInp-1:0] out_data;
  logic     [NumOut-1:0][NumInp-1:0] out_valid;
  logic     [NumOut-1:0][NumInp-1:0] out_ready;

  // Generate the input selection
  for (genvar i = 0; unsigned'(i) < NumInp; i++) begin : gen_inps
    stream_demux #(
      .N_OUP ( NumOut )
    ) i_stream_demux (
      .inp_valid_i ( valid_i[i]   ),
      .inp_ready_o ( ready_o[i]   ),
      .oup_sel_i   ( sel_i[i]     ),
      .oup_valid_o ( inp_valid[i] ),
      .oup_ready_i ( inp_ready[i] )
    );

    // Do the switching cross of the signals.
    for (genvar j = 0; unsigned'(j) < NumOut; j++) begin : gen_cross
      // Propagate the data from this input to all outputs.
      assign out_data[j][i]  = data_i[i];
      // switch handshaking
      assign out_valid[j][i] = inp_valid[i][j];
      assign inp_ready[i][j] = out_ready[j][i];
    end
  end

  // Generate the output arbitration.
  for (genvar j = 0; unsigned'(j) < NumOut; j++) begin : gen_outs
    spill_data_t arb;
    logic        arb_valid, arb_ready;

    rr_arb_tree #(
      .NumIn     ( NumInp    ),
      .DataType  ( payload_t ),
      .ExtPrio   ( ExtPrio   ),
      .AxiVldRdy ( AxiVldRdy ),
      .LockIn    ( LockIn    )
    ) i_rr_arb_tree (
      .clk_i,
      .rst_ni,
      .flush_i,
      .rr_i    ( rr_i[j]      ),
      .req_i   ( out_valid[j] ),
      .gnt_o   ( out_ready[j] ),
      .data_i  ( out_data[j]  ),
      .req_o   ( arb_valid    ),
      .gnt_i   ( arb_ready    ),
      .data_o  ( arb.data     ),
      .idx_o   ( arb.idx      )
    );

    spill_data_t spill;

    spill_register #(
      .T      ( spill_data_t ),
      .Bypass ( !OutSpillReg )
    ) i_spill_register (
      .clk_i,
      .rst_ni,
      .valid_i ( arb_valid  ),
      .ready_o ( arb_ready  ),
      .data_i  ( arb        ),
      .valid_o ( valid_o[j] ),
      .ready_i ( ready_i[j] ),
      .data_o  ( spill      )
    );
    // Assign the outputs (deaggregate the data).
    assign data_o[j] = spill.data;
    assign idx_o[j]  = spill.idx;
  end

  // Assertions
  // Make sure that the handshake and payload is stable
  // pragma translate_off
  `ifndef VERILATOR
  default disable iff rst_ni;
  for (genvar i = 0; unsigned'(i) < NumInp; i++) begin : gen_sel_assertions
    assert property (@(posedge clk_i) (valid_i[i] |-> sel_i[i] < sel_oup_t'(NumOut))) else
        $fatal(1, "Non-existing output is selected!");
  end

  if (AxiVldRdy) begin : gen_handshake_assertions
    for (genvar i = 0; unsigned'(i) < NumInp; i++) begin : gen_inp_assertions
      assert property (@(posedge clk_i) (valid_i[i] && !ready_o[i] |=> $stable(data_i[i]))) else
          $error("data_i is unstable at input: %0d", i);
      assert property (@(posedge clk_i) (valid_i[i] && !ready_o[i] |=> $stable(sel_i[i]))) else
          $error("sel_i is unstable at input: %0d", i);
      assert property (@(posedge clk_i) (valid_i[i] && !ready_o[i] |=> valid_i[i])) else
          $error("valid_i at input %0d has been taken away without a ready.", i);
    end
    for (genvar i = 0; unsigned'(i) < NumOut; i++) begin : gen_out_assertions
      assert property (@(posedge clk_i) (valid_o[i] && !ready_i[i] |=> $stable(data_o[i]))) else
          $error("data_o is unstable at output: %0d Check that parameter LockIn is set.", i);
      assert property (@(posedge clk_i) (valid_o[i] && !ready_i[i] |=> $stable(idx_o[i]))) else
          $error("idx_o is unstable at output: %0d Check that parameter LockIn is set.", i);
      assert property (@(posedge clk_i) (valid_o[i] && !ready_i[i] |=> valid_o[i])) else
          $error("valid_o at output %0d has been taken away without a ready.", i);
    end
  end

  initial begin : proc_parameter_assertions
    assert (NumInp > 32'd0) else $fatal(1, "NumInp has to be > 0!");
    assert (NumOut > 32'd0) else $fatal(1, "NumOut has to be > 0!");
  end
  `endif
  // pragma translate_on
endmodule
