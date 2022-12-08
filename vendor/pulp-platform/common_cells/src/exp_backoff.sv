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
// Date: 10.04.2019
// Description: exponential backoff counter with randomization.
//
// For each failed trial (set_i pulsed), this unit exponentially increases the
// (average) backoff time by masking an LFSR with a shifted mask in order to
// create the backoff counter initial value.
//
// The shift register mask and the counter value are both reset to '0 in case of
// a successful trial (clr_i).
//

module exp_backoff #(
  /// Seed for 16bit LFSR
  parameter int unsigned Seed   = 'hffff,
  /// 2**MaxExp-1 determines the maximum range from which random wait counts are drawn
  parameter int unsigned MaxExp = 16
) (
  input  logic clk_i,
  input  logic rst_ni,
  /// Sets the backoff counter (pulse) -> use when trial did not succeed
  input  logic set_i,
  /// Clears the backoff counter (pulse) -> use when trial succeeded
  input  logic clr_i,
  /// Indicates whether the backoff counter is equal to zero and a new trial can be launched
  output logic is_zero_o
);

  // leave this constant
  localparam int unsigned WIDTH = 16;

  logic [WIDTH-1:0] lfsr_d, lfsr_q, cnt_d, cnt_q, mask_d, mask_q;
  logic lfsr;

  // generate random wait counts
  // note: we use a flipped lfsr here to
  // avoid strange correlation effects between
  // the (left-shifted) mask and the lfsr
  assign lfsr = lfsr_q[15-15] ^
                lfsr_q[15-13] ^
                lfsr_q[15-12] ^
                lfsr_q[15-10];

  assign lfsr_d = (set_i) ? {lfsr, lfsr_q[$high(lfsr_q):1]} :
                            lfsr_q;

  // mask the wait counts with exponentially increasing mask (shift reg)
  assign mask_d = (clr_i) ? '0                                :
                  (set_i) ? {{(WIDTH-MaxExp){1'b0}},mask_q[MaxExp-2:0], 1'b1} :
                            mask_q;

  assign cnt_d =  (clr_i)      ? '0                :
                  (set_i)      ? (mask_q & lfsr_q) :
                  (!is_zero_o) ? cnt_q - 1'b1      : '0;

  assign is_zero_o = (cnt_q=='0);

  always_ff @(posedge clk_i or negedge rst_ni) begin : p_regs
    if (!rst_ni) begin
      lfsr_q <= WIDTH'(Seed);
      mask_q <= '0;
      cnt_q  <= '0;
    end else begin
      lfsr_q <= lfsr_d;
      mask_q <= mask_d;
      cnt_q  <= cnt_d;
    end
  end

///////////////////////////////////////////////////////
// assertions
///////////////////////////////////////////////////////

//pragma translate_off
`ifndef VERILATOR
  initial begin
    // assert wrong parameterizations
    assert (MaxExp>0)
      else $fatal(1,"MaxExp must be greater than 0");
    assert (MaxExp<=16)
      else $fatal(1,"MaxExp cannot be greater than 16");
    assert (Seed>0)
      else $fatal(1,"Zero seed is not allowed for LFSR");
  end
`endif
//pragma translate_on

endmodule // exp_backoff
