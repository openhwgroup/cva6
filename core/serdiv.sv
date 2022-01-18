// Copyright 2018 ETH Zurich and University of Bologna.
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
//         Andreas Traber    <traber@iis.ee.ethz.ch>, ETH Zurich
//
// Date: 18.10.2018
// Description: simple 64bit serial divider


module serdiv import ariane_pkg::*; #(
  parameter WIDTH       = 64
) (
  input  logic                      clk_i,
  input  logic                      rst_ni,
  // input IF
  input  logic [TRANS_ID_BITS-1:0]  id_i,
  input  logic [WIDTH-1:0]          op_a_i,
  input  logic [WIDTH-1:0]          op_b_i,
  input  logic [1:0]                opcode_i, // 0: udiv, 2: urem, 1: div, 3: rem
  // handshake
  input  logic                      in_vld_i, // there is a cycle delay from in_rdy_o->in_vld_i, see issue_read_operands.sv stage
  output logic                      in_rdy_o,
  input  logic                      flush_i,
  // output IF
  output logic                      out_vld_o,
  input  logic                      out_rdy_i,
  output logic [TRANS_ID_BITS-1:0]  id_o,
  output logic [WIDTH-1:0]          res_o
);

/////////////////////////////////////
// signal declarations
/////////////////////////////////////

  enum logic [1:0] {IDLE, DIVIDE, FINISH} state_d, state_q;

  logic [WIDTH-1:0]       res_q, res_d;
  logic [WIDTH-1:0]       op_a_q, op_a_d;
  logic [WIDTH-1:0]       op_b_q, op_b_d;
  logic                   op_a_sign, op_b_sign;
  logic                   op_b_zero, op_b_zero_q, op_b_zero_d;

  logic [TRANS_ID_BITS-1:0] id_q, id_d;

  logic rem_sel_d, rem_sel_q;
  logic comp_inv_d, comp_inv_q;
  logic res_inv_d, res_inv_q;

  logic [WIDTH-1:0] add_mux;
  logic [WIDTH-1:0] add_out;
  logic [WIDTH-1:0] add_tmp;
  logic [WIDTH-1:0] b_mux;
  logic [WIDTH-1:0] out_mux;

  logic [$clog2(WIDTH+1)-1:0] cnt_q, cnt_d;
  logic cnt_zero;

  logic [WIDTH-1:0] lzc_a_input, lzc_b_input, op_b;
  logic [$clog2(WIDTH)-1:0] lzc_a_result, lzc_b_result;
  logic [$clog2(WIDTH+1)-1:0] shift_a;
  logic [$clog2(WIDTH+1):0] div_shift;

  logic a_reg_en, b_reg_en, res_reg_en, ab_comp, pm_sel, load_en;
  logic lzc_a_no_one, lzc_b_no_one;
  logic div_res_zero_d, div_res_zero_q;


/////////////////////////////////////
// align the input operands
// for faster division
/////////////////////////////////////

  assign op_b_zero = (op_b_i == 0);
  assign op_a_sign = op_a_i[$high(op_a_i)];
  assign op_b_sign = op_b_i[$high(op_b_i)];

  assign lzc_a_input = (opcode_i[0] & op_a_sign & (op_a_i == -$signed(1)))? {~op_a_i, 1'b1} : (opcode_i[0] & op_a_sign) ? {~op_a_i, 1'b0} : op_a_i; 
  // This change in lzc_a_input equation helps to fix erronous results for DIV and REM for -1/1.
  assign lzc_b_input = (opcode_i[0] & op_b_sign) ? ~op_b_i         : op_b_i;

  lzc #(
    .MODE    ( 1          ), // count leading zeros
    .WIDTH   ( WIDTH      )
  ) i_lzc_a (
    .in_i    ( lzc_a_input  ),
    .cnt_o   ( lzc_a_result ),
    .empty_o ( lzc_a_no_one )
  );

  lzc #(
    .MODE    ( 1          ), // count leading zeros
    .WIDTH   ( WIDTH      )
  ) i_lzc_b (
    .in_i    ( lzc_b_input  ),
    .cnt_o   ( lzc_b_result ),
    .empty_o ( lzc_b_no_one )
  );

  assign shift_a      = (lzc_a_no_one) ? WIDTH : lzc_a_result;
  assign div_shift    = (lzc_b_no_one) ? WIDTH : lzc_b_result-shift_a;

  assign op_b         = op_b_i <<< $unsigned(div_shift);

  // the division is zero if |opB| > |opA| and can be terminated
  assign div_res_zero_d = (load_en) ? ($signed(div_shift) < 0) : div_res_zero_q;

/////////////////////////////////////
// Datapath
/////////////////////////////////////

  assign pm_sel      = load_en & ~(opcode_i[0] & (op_a_sign ^ op_b_sign));

  // muxes
  assign add_mux     = (load_en)   ? op_a_i  : op_b_q;

  // attention: logical shift by one in case of negative operand B!
  assign b_mux       = (load_en)   ? op_b : {comp_inv_q, (op_b_q[$high(op_b_q):1])};

  // in case of bad timing, we could output from regs -> needs a cycle more in the FSM
  assign out_mux     = (rem_sel_q) ? op_a_q : res_q;
  // assign out_mux     = (rem_sel_q) ? op_a_d : res_d;

  // invert if necessary
  assign res_o       = (res_inv_q) ? -$signed(out_mux) : out_mux;

  // main comparator
  assign ab_comp     = ((op_a_q == op_b_q) | ((op_a_q > op_b_q) ^ comp_inv_q)) & ((|op_a_q) | op_b_zero_q);

  // main adder
  assign add_tmp     = (load_en) ? 0 : op_a_q;
  assign add_out     = (pm_sel)  ? add_tmp + add_mux : add_tmp - $signed(add_mux);

/////////////////////////////////////
// FSM, counter
/////////////////////////////////////

  assign cnt_zero = (cnt_q == 0);
  assign cnt_d    = (load_en)   ? div_shift  :
                    (~cnt_zero) ? cnt_q - 1  : cnt_q;

  always_comb begin : p_fsm
    // default
    state_d        = state_q;
    in_rdy_o       = 1'b0;
    out_vld_o      = 1'b0;
    load_en        = 1'b0;
    a_reg_en       = 1'b0;
    b_reg_en       = 1'b0;
    res_reg_en     = 1'b0;

    unique case (state_q)
      IDLE: begin
        in_rdy_o    = 1'b1;

        if (in_vld_i) begin
          in_rdy_o  = 1'b0;// there is a cycle delay until the valid signal is asserted by the id stage
          a_reg_en  = 1'b1;
          b_reg_en  = 1'b1;
          load_en   = 1'b1;
          state_d   = DIVIDE;
        end
      end
      DIVIDE: begin
        if(~div_res_zero_q) begin
          a_reg_en     = ab_comp;
          b_reg_en     = 1'b1;
          res_reg_en   = 1'b1;
        end
        // can end the division now if the result is clearly 0
        if(div_res_zero_q) begin
          out_vld_o = 1'b1;
          state_d   = FINISH;
          if(out_rdy_i) begin
            // in_rdy_o = 1'b1;// there is a cycle delay until the valid signal is asserted by the id stage
            state_d  = IDLE;
          end
        end else if (cnt_zero) begin
          state_d   = FINISH;
        end
      end
      FINISH: begin
        out_vld_o = 1'b1;

        if (out_rdy_i) begin
          // in_rdy_o = 1'b1;// there is a cycle delay until the valid signal is asserted by the id stage
          state_d  = IDLE;
        end
      end
      default : state_d = IDLE;
    endcase

    if (flush_i) begin
        in_rdy_o   = 1'b0;
        out_vld_o  = 1'b0;
        a_reg_en   = 1'b0;
        b_reg_en   = 1'b0;
        load_en    = 1'b0;
        state_d    = IDLE;
    end
  end

/////////////////////////////////////
// regs, flags
/////////////////////////////////////

  // get flags
  assign rem_sel_d    = (load_en) ? opcode_i[1]               : rem_sel_q;
  assign comp_inv_d   = (load_en) ? opcode_i[0] & op_b_sign   : comp_inv_q;
  assign op_b_zero_d  = (load_en) ? op_b_zero                 : op_b_zero_q;
  assign res_inv_d    = (load_en) ? (~op_b_zero | opcode_i[1]) & opcode_i[0] & (op_a_sign ^ op_b_sign) : res_inv_q;

  // transaction id
  assign id_d = (load_en) ? id_i : id_q;
  assign id_o = id_q;

  assign op_a_d   = (a_reg_en)   ? add_out : op_a_q;
  assign op_b_d   = (b_reg_en)   ? b_mux   : op_b_q;
  assign res_d    = (load_en)   ? '0       :
                    (res_reg_en) ? {res_q[$high(res_q)-1:0], ab_comp} : res_q;

  always_ff @(posedge clk_i or negedge rst_ni) begin : p_regs
    if (~rst_ni) begin
      state_q        <= IDLE;
      op_a_q         <= '0;
      op_b_q         <= '0;
      res_q          <= '0;
      cnt_q          <= '0;
      id_q           <= '0;
      rem_sel_q      <= 1'b0;
      comp_inv_q     <= 1'b0;
      res_inv_q      <= 1'b0;
      op_b_zero_q    <= 1'b0;
      div_res_zero_q <= 1'b0;
    end else begin
      state_q        <= state_d;
      op_a_q         <= op_a_d;
      op_b_q         <= op_b_d;
      res_q          <= res_d;
      cnt_q          <= cnt_d;
      id_q           <= id_d;
      rem_sel_q      <= rem_sel_d;
      comp_inv_q     <= comp_inv_d;
      res_inv_q      <= res_inv_d;
      op_b_zero_q    <= op_b_zero_d;
      div_res_zero_q <= div_res_zero_d;
    end
  end

endmodule
