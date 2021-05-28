// Copyright 2019 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Author: Michael Schaffner <schaffner@iis.ee.ethz.ch>, ETH Zurich
// Date: 02.04.2019
// Description: logarithmic arbitration tree with round robin arbitration scheme.
//
// The rr_arb_tree employs fair round robin arbitration - i.e. the priorities
// rotate each cycle.
//
// The `LockIn` option prevents the arbiter from changing the arbitration
// decision when the arbiter is disabled. I.e., the index of the first request
// that wins the arbitration will be locked in case the destination is not
// able to grant the request in the same cycle.
//
// The `ExtPrio` option allows to override the internal round robin counter via the
// `rr_i` signal. This can be useful in case multiple arbiters need to have
// rotating priorities that are operating in lock-step. If static priority arbitration
// is needed, just connect `rr_i` to '0.
//
// If `AxiVldRdy` is set, the req/gnt signals are compliant with the AXI style vld/rdy
// handshake. Namely, upstream vld (req) must not depend on rdy (gnt), as it can be deasserted
// again even though vld is asserted. Enabling `AxiVldRdy` leads to a reduction of arbiter
// delay and area.
//

module rr_arb_tree #(
  parameter int unsigned NumIn      = 64,
  parameter int unsigned DataWidth  = 32,
  parameter type         DataType   = logic [DataWidth-1:0],
  parameter bit          ExtPrio    = 1'b0, // set to 1'b1 to enable
  parameter bit          AxiVldRdy  = 1'b0, // treat req/gnt as vld/rdy
  parameter bit          LockIn     = 1'b0  // set to 1'b1 to enable
) (
  input  logic                             clk_i,
  input  logic                             rst_ni,
  input  logic                             flush_i, // clears the arbiter state
  input  logic [$clog2(NumIn)-1:0]         rr_i,    // external RR prio (needs to be enabled above)
  // input requests and data
  input  logic [NumIn-1:0]                 req_i,
  /* verilator lint_off UNOPTFLAT */
  output logic [NumIn-1:0]                 gnt_o,
  /* verilator lint_on UNOPTFLAT */
  input  DataType [NumIn-1:0]              data_i,
  // arbitrated output
  input  logic                             gnt_i,
  output logic                             req_o,
  output DataType                          data_o,
  output logic [$clog2(NumIn)-1:0]         idx_o
);
  // just pass through in this corner case
  if (NumIn == unsigned'(1)) begin
    assign req_o    = req_i[0];
    assign gnt_o[0] = gnt_i;
    assign data_o   = data_i[0];
    assign idx_o    = '0;
  // non-degenerate cases
  end else begin
    localparam int unsigned NumLevels = $clog2(NumIn);

    /* verilator lint_off UNOPTFLAT */
    logic [2**NumLevels-2:0][NumLevels-1:0]  index_nodes; // used to propagate the indices
    DataType [2**NumLevels-2:0]              data_nodes;  // used to propagate the data
    logic [2**NumLevels-2:0]                 gnt_nodes;   // used to propagate the grant to masters
    logic [2**NumLevels-2:0]                 req_nodes;   // used to propagate the requests to slave
    /* lint_off */
    logic [NumLevels-1:0]                    rr_q;
    logic [NumIn-1:0]                        req_d;

    // the final arbitration decision can be taken from the root of the tree
    assign req_o        = req_nodes[0];
    assign data_o       = data_nodes[0];
    assign idx_o        = index_nodes[0];

    if (ExtPrio) begin : gen_ext_rr
      assign rr_q       = rr_i;
      assign req_d      = req_i;
    end else begin : gen_int_rr
      logic [NumLevels-1:0] rr_d;

      // lock arbiter decision in case we got at least one req and no acknowledge
      if (LockIn) begin : gen_lock
        logic  lock_d, lock_q;
        logic [NumIn-1:0]     req_q;

        assign lock_d     = req_o & ~gnt_i;
        assign req_d      = (lock_q) ? req_q : req_i;

        always_ff @(posedge clk_i or negedge rst_ni) begin : p_lock_reg
          if (!rst_ni) begin
            lock_q <= '0;
          end else begin
            if (flush_i) begin
              lock_q <= '0;
            end else begin
              lock_q <= lock_d;
            end
          end
        end

        // pragma translate_off
        `ifndef VERILATOR
          lock: assert property(
            @(posedge clk_i) disable iff (!rst_ni) LockIn |-> req_o && !gnt_i |=> idx_o == $past(idx_o))
              else $fatal (1, "Lock implies same arbiter decision in next cycle if output is not ready.");

          logic [NumIn-1:0] req_tmp;
          assign req_tmp = req_q & req_i;
          lock_req: assert property(
            @(posedge clk_i) disable iff (!rst_ni) LockIn |-> lock_d |=> req_tmp == req_q)
              else $fatal (1, "It is disallowed to deassert unserved request signals when LockIn is enabled.");
        `endif
        // pragma translate_on

        always_ff @(posedge clk_i or negedge rst_ni) begin : p_req_regs
          if (!rst_ni) begin
            req_q  <= '0;
          end else begin
            if (flush_i) begin
              req_q  <= '0;
            end else begin
              req_q  <= req_d;
            end
          end
        end
      end else begin : gen_no_lock
        assign req_d = req_i;
      end

      assign rr_d       = (gnt_i && req_o) ? ((rr_q == NumLevels'(NumIn-1)) ? '0 : rr_q + 1'b1) : rr_q;

      always_ff @(posedge clk_i or negedge rst_ni) begin : p_rr_regs
        if (!rst_ni) begin
          rr_q   <= '0;
        end else begin
          if (flush_i) begin
            rr_q   <= '0;
          end else begin
            rr_q   <= rr_d;
          end
        end
      end
    end

    assign gnt_nodes[0] = gnt_i;

    // arbiter tree
    for (genvar level = 0; unsigned'(level) < NumLevels; level++) begin : gen_levels
      for (genvar l = 0; l < 2**level; l++) begin : gen_level
        // local select signal
        logic sel;
        // index calcs
        localparam int unsigned idx0 = 2**level-1+l;// current node
        localparam int unsigned idx1 = 2**(level+1)-1+l*2;
        //////////////////////////////////////////////////////////////
        // uppermost level where data is fed in from the inputs
        if (unsigned'(level) == NumLevels-1) begin : gen_first_level
          // if two successive indices are still in the vector...
          if (unsigned'(l) * 2 < NumIn-1) begin
            assign req_nodes[idx0]   = req_d[l*2] | req_d[l*2+1];

            // arbitration: round robin
            assign sel =  ~req_d[l*2] | req_d[l*2+1] & rr_q[NumLevels-1-level];

            assign index_nodes[idx0] = NumLevels'(sel);
            assign data_nodes[idx0]  = (sel) ? data_i[l*2+1] : data_i[l*2];
            assign gnt_o[l*2]        = gnt_nodes[idx0] & (AxiVldRdy | req_d[l*2])   & ~sel;
            assign gnt_o[l*2+1]      = gnt_nodes[idx0] & (AxiVldRdy | req_d[l*2+1]) & sel;
          end
          // if only the first index is still in the vector...
          if (unsigned'(l) * 2 == NumIn-1) begin
            assign req_nodes[idx0]   = req_d[l*2];
            assign index_nodes[idx0] = '0;// always zero in this case
            assign data_nodes[idx0]  = data_i[l*2];
            assign gnt_o[l*2]        = gnt_nodes[idx0] & (AxiVldRdy | req_d[l*2]);
          end
          // if index is out of range, fill up with zeros (will get pruned)
          if (unsigned'(l) * 2 > NumIn-1) begin
            assign req_nodes[idx0]   = 1'b0;
            assign index_nodes[idx0] = DataType'('0);
            assign data_nodes[idx0]  = DataType'('0);
          end
        //////////////////////////////////////////////////////////////
        // general case for other levels within the tree
        end else begin : gen_other_levels
          assign req_nodes[idx0]   = req_nodes[idx1] | req_nodes[idx1+1];

          // arbitration: round robin
          assign sel =  ~req_nodes[idx1] | req_nodes[idx1+1] & rr_q[NumLevels-1-level];

          assign index_nodes[idx0] = (sel) ? NumLevels'({1'b1, index_nodes[idx1+1][NumLevels-unsigned'(level)-2:0]}) :
                                             NumLevels'({1'b0, index_nodes[idx1][NumLevels-unsigned'(level)-2:0]});
          assign data_nodes[idx0]  = (sel) ? data_nodes[idx1+1] : data_nodes[idx1];
          assign gnt_nodes[idx1]   = gnt_nodes[idx0] & ~sel;
          assign gnt_nodes[idx1+1] = gnt_nodes[idx0] & sel;
        end
        //////////////////////////////////////////////////////////////
      end
    end

    // pragma translate_off
    `ifndef VERILATOR
    initial begin : p_assert
      assert(NumIn)
        else $fatal("Input must be at least one element wide.");
      assert(!(LockIn && ExtPrio))
        else $fatal(1,"Cannot use LockIn feature together with external ExtPrio.");
    end

    hot_one : assert property(
      @(posedge clk_i) disable iff (!rst_ni) $onehot0(gnt_o))
        else $fatal (1, "Grant signal must be hot1 or zero.");

    gnt0 : assert property(
      @(posedge clk_i) disable iff (!rst_ni) |gnt_o |-> gnt_i)
        else $fatal (1, "Grant out implies grant in.");

    gnt1 : assert property(
      @(posedge clk_i) disable iff (!rst_ni) req_o |-> gnt_i |-> |gnt_o)
        else $fatal (1, "Req out and grant in implies grant out.");

    gnt_idx : assert property(
      @(posedge clk_i) disable iff (!rst_ni) req_o |->  gnt_i |-> gnt_o[idx_o])
        else $fatal (1, "Idx_o / gnt_o do not match.");

    req0 : assert property(
      @(posedge clk_i) disable iff (!rst_ni) |req_i |-> req_o)
        else $fatal (1, "Req in implies req out.");

    req1 : assert property(
      @(posedge clk_i) disable iff (!rst_ni) |req_o |-> req_i)
        else $fatal (1, "Req out implies req in.");
    `endif
    // pragma translate_on
  end

endmodule : rr_arb_tree
