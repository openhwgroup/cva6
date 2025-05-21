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

/// Omega network using multiple `stream_xbar` as switches.
///
/// An omega network is isomorphic to a butterfly network.
///
/// Handshaking rules as defined by the `AMBA AXI` standard on default.
module stream_omega_net #(
  /// Number of inputs into the network (`> 0`).
  parameter int unsigned NumInp      = 32'd0,
  /// Number of outputs from the network (`> 0`).
  parameter int unsigned NumOut      = 32'd0,
  /// Radix of the individual switch points of the network.
  /// Currently supported are `32'd2` and `32'd4`.
  parameter int unsigned Radix       = 32'd2,
  /// Data width of the stream. Can be overwritten by defining the type parameter `payload_t`.
  parameter int unsigned DataWidth   = 32'd1,
  /// Payload type of the data ports, only usage of parameter `DataWidth`.
  parameter type         payload_t   = logic [DataWidth-1:0],
  /// Adds a spill register stage at each output.
  parameter bit          SpillReg = 1'b0,
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
  if (NumInp <= Radix && NumOut <= Radix) begin : gen_degenerate_omega_net
    // If both Number of inputs and number of outputs are smaller or the same as the radix
    // just instantiate a `stream_xbar`.
    stream_xbar #(
      .NumInp      ( NumInp    ),
      .NumOut      ( NumOut    ),
      .payload_t   ( payload_t ),
      .OutSpillReg ( SpillReg  ),
      .ExtPrio     ( ExtPrio   ),
      .AxiVldRdy   ( AxiVldRdy ),
      .LockIn      ( LockIn    )
    ) i_stream_xbar (
      .clk_i,
      .rst_ni,
      .flush_i,
      .rr_i    ( rr_i    ),
      .data_i  ( data_i  ),
      .sel_i   ( sel_i   ),
      .valid_i ( valid_i ),
      .ready_o ( ready_o ),
      .data_o  ( data_o  ),
      .idx_o   ( idx_o   ),
      .valid_o ( valid_o ),
      .ready_i ( ready_i )
    );
  end else begin : gen_omega_net
    // Find the next power of radix of either the number of inputs or number of outputs.
    // This normalizes the network to a power of the radix. Unused inputs and outputs are tied off.
    // If the radix is poorly chosen with respect to the number of input/outputs ports
    // will lead to an explosion of tied off lanes, which will be removed during optimization.
    // Can lead however to RTL simulation overhead.
    // Dividing through the log base 2 of `Radix` leads to a change of base.
    localparam int unsigned NumLanes = (NumOut > NumInp) ?
        unsigned'(Radix**(cf_math_pkg::ceil_div($clog2(NumOut), $clog2(Radix)))) :
        unsigned'(Radix**(cf_math_pkg::ceil_div($clog2(NumInp), $clog2(Radix))));

    // Find the number of routing levels needed.
    localparam int unsigned NumLevels = unsigned'(($clog2(NumLanes)+$clog2(Radix)-1)/$clog2(Radix));

    // Find the number of routes per network stage. Can use a normal division here, as
    // `NumLanes % Radix == 0`.
    localparam int unsigned NumRouters = NumLanes / Radix;

    // Define the type of sel signal to send through the network. It has to be sliced for the
    // individual sel signals of a stage. This slicing has to align with `$clog2(Radix)`.
    // For example `Radix = 4`, `NumOut = 17` will lead to the sel signal of an individual stage to
    // be 2 bit wide, whereas signal `sel_i` of the module will be 5 bit wide.
    // To prevent slicing into an undefined field the overall sel signal is then defined with
    // width 6.
    typedef logic [$clog2(NumLanes)-1:0] sel_dst_t;

    // Selection signal type of an individual router
    localparam int unsigned SelW = unsigned'($clog2(Radix));
    initial begin : proc_selw
      $display("SelW is:    %0d", SelW);
      $display("SelDstW is: %0d", $bits(sel_dst_t));
    end
    typedef logic [SelW-1:0] sel_t;

    // Define the payload which should be routed through the network.
    typedef struct packed {
      sel_dst_t sel_oup; // Selection of output, where it should be routed
      payload_t payload; // External payload data
      idx_inp_t idx_inp; // Index of the input of this packet
    } omega_data_t;

    // signal definitions
    omega_data_t [NumLevels-1:0][NumRouters-1:0][Radix-1:0] inp_router_data;
    logic        [NumLevels-1:0][NumRouters-1:0][Radix-1:0] inp_router_valid, inp_router_ready;
    omega_data_t [NumLevels-1:0][NumRouters-1:0][Radix-1:0] out_router_data;
    logic        [NumLevels-1:0][NumRouters-1:0][Radix-1:0] out_router_valid, out_router_ready;

    // Generate the shuffling between the routers
    for (genvar i = 0; unsigned'(i) < NumLevels-1; i++) begin : gen_shuffle_levels
      for (genvar j = 0; unsigned'(j) < NumRouters; j++) begin : gen_shuffle_routers
        for (genvar k = 0; unsigned'(k) < Radix; k++) begin : gen_shuffle_radix
          // This parameter is from `0` to `NumLanes-1`
          localparam int unsigned IdxLane = Radix * j + k;
          // Do the perfect shuffle
          assign inp_router_data[i+1][IdxLane%NumRouters][IdxLane/NumRouters] =
              out_router_data[i][j][k];

          assign inp_router_valid[i+1][IdxLane%NumRouters][IdxLane/NumRouters] =
              out_router_valid[i][j][k];

          assign out_router_ready[i][j][k] =
              inp_router_ready[i+1][IdxLane%NumRouters][IdxLane/NumRouters];

          // Do the first input shuffle of layer 0.
          // The inputs are connected in reverse. The reason is that then the optimization
          // leaves then the biggest possible network diameter.
          if (i == 0) begin : gen_shuffle_inp
            // Reverse the order of the input ports
            if ((NumLanes-IdxLane) <= NumInp) begin : gen_inp_ports
              localparam int unsigned IdxInp = NumLanes - IdxLane - 32'd1;
              assign inp_router_data[0][IdxLane%NumRouters][IdxLane/NumRouters] = '{
                    sel_oup: sel_dst_t'(sel_i[IdxInp]),
                    payload: data_i[IdxInp],
                    idx_inp: idx_inp_t'(IdxInp)
                  };

              assign inp_router_valid[0][IdxLane%NumRouters][IdxLane/NumRouters] = valid_i[IdxInp];
              assign ready_o[IdxInp] = inp_router_ready[0][IdxLane%NumRouters][IdxLane/NumRouters];

            end else begin : gen_tie_off
              assign inp_router_data[0][IdxLane%NumRouters][IdxLane/NumRouters] = '{ default: '0};
              assign inp_router_valid[0][IdxLane%NumRouters][IdxLane/NumRouters] = 1'b0;
            end
          end
        end
      end
    end

    // Generate the `stream_xbar_routers`
    for (genvar i = 0; unsigned'(i) < NumLevels; i++) begin : gen_router_levels
      for (genvar j = 0; unsigned'(j) < NumRouters; j++) begin : gen_routers
        sel_t [Radix-1:0] sel_router;
        for (genvar k = 0; unsigned'(k) < Radix; k++) begin : gen_router_sel
          // For the inter stage routing some bits of the overall selection are important.
          // The `MSB` is for stage `0`, `MSB-1` for stage `1` and so on for the `Radix=2` case.
          // For higher radices's a bit slice following the same pattern is used.
          // This is the reason that the internal network is expanded to a power of two, so that
          // the selection slicing always has a valid index.
          assign sel_router[k] = inp_router_data[i][j][k].sel_oup[SelW*(NumLevels-i-1)+:SelW];
        end

        stream_xbar #(
          .NumInp      ( Radix        ),
          .NumOut      ( Radix        ),
          .payload_t   ( omega_data_t ),
          .OutSpillReg ( SpillReg     ),
          .ExtPrio     ( 1'b0         ),
          .AxiVldRdy   ( AxiVldRdy    ),
          .LockIn      ( LockIn       )
        ) i_stream_xbar (
          .clk_i,
          .rst_ni,
          .flush_i,
          .rr_i    ( '0                     ),
          .data_i  ( inp_router_data[i][j]  ),
          .sel_i   ( sel_router             ),
          .valid_i ( inp_router_valid[i][j] ),
          .ready_o ( inp_router_ready[i][j] ),
          .data_o  ( out_router_data[i][j]  ),
          .idx_o   ( /* not used */         ),
          .valid_o ( out_router_valid[i][j] ),
          .ready_i ( out_router_ready[i][j] )
        );
      end
    end

    // outputs are on the last level
    for (genvar i = 0; unsigned'(i) < NumLanes; i++) begin : gen_outputs
      if (i < NumOut) begin : gen_connect
        assign data_o[i]  = out_router_data[NumLevels-1][i/Radix][i%Radix].payload;
        assign idx_o[i]   = out_router_data[NumLevels-1][i/Radix][i%Radix].idx_inp;
        assign valid_o[i] = out_router_valid[NumLevels-1][i/Radix][i%Radix];
        assign out_router_ready[NumLevels-1][i/Radix][i%Radix] = ready_i[i];
      end else begin : gen_tie_off
        assign out_router_ready[NumLevels-1][i/Radix][i%Radix] = 1'b0;
      end
    end

    initial begin : proc_debug_print
      $display("NumInp:     %0d", NumInp);
      $display("NumOut:     %0d", NumOut);
      $display("Radix:      %0d", Radix);
      $display("NumLanes:   %0d", NumLanes);
      $display("NumLevels:  %0d", NumLevels);
      $display("NumRouters: %0d", NumRouters);
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
      assert ((2**$clog2(Radix) == Radix) && (Radix > 32'd1)) else
          $fatal(1, "Radix %0d is not power of two.", Radix);
      assert (2**$clog2(NumRouters) == NumRouters) else
          $fatal(1, "NumRouters %0d is not power of two.", NumRouters);
      assert ($clog2(NumLanes) % SelW == 0) else
          $fatal(1, "Bit slicing of the internal selection signal is broken.");
    end
    `endif
    // pragma translate_on
  end
endmodule
