// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

///////////////////////////////////////////////////////////////////////////////
// File       : Simple Serial Divider
// Ver        : 1.0
// Date       : 15.03.2016
///////////////////////////////////////////////////////////////////////////////
//
// Description: this is a simple serial divider for signed integers (int32).
//
///////////////////////////////////////////////////////////////////////////////
//
// Authors    : Michael Schaffner (schaffner@iis.ee.ethz.ch)
//              Andreas Traber    (atraber@iis.ee.ethz.ch)
//
///////////////////////////////////////////////////////////////////////////////

module riscv_alu_div
#(
   parameter C_WIDTH     = 32,
   parameter C_LOG_WIDTH = 6
)
(
    input  logic                    Clk_CI,
    input  logic                    Rst_RBI,
    // input IF
    input  logic [C_WIDTH-1:0]      OpA_DI,
    input  logic [C_WIDTH-1:0]      OpB_DI,
    input  logic [C_LOG_WIDTH-1:0]  OpBShift_DI,
    input  logic                    OpBIsZero_SI,
    //
    input  logic                    OpBSign_SI, // gate this to 0 in case of unsigned ops
    input  logic [1:0]              OpCode_SI,  // 0: udiv, 2: urem, 1: div, 3: rem
    // handshake
    input  logic                    InVld_SI,
    // output IF
    input  logic                    OutRdy_SI,
    output logic                    OutVld_SO,
    output logic [C_WIDTH-1:0]      Res_DO
  );

  ///////////////////////////////////////////////////////////////////////////////
  // signal declarations
  ///////////////////////////////////////////////////////////////////////////////

  logic [C_WIDTH-1:0] ResReg_DP, ResReg_DN;
  logic [C_WIDTH-1:0] ResReg_DP_rev;
  logic [C_WIDTH-1:0] AReg_DP, AReg_DN;
  logic [C_WIDTH-1:0] BReg_DP, BReg_DN;

  logic RemSel_SN, RemSel_SP;
  logic CompInv_SN, CompInv_SP;
  logic ResInv_SN, ResInv_SP;

  logic [C_WIDTH-1:0] AddMux_D;
  logic [C_WIDTH-1:0] AddOut_D;
  logic [C_WIDTH-1:0] AddTmp_D;
  logic [C_WIDTH-1:0] BMux_D;
  logic [C_WIDTH-1:0] OutMux_D;

  logic [C_LOG_WIDTH-1:0] Cnt_DP, Cnt_DN;
  logic CntZero_S;

  logic ARegEn_S, BRegEn_S, ResRegEn_S, ABComp_S, PmSel_S, LoadEn_S;

  enum logic [1:0] {IDLE, DIVIDE, FINISH} State_SN, State_SP;


  ///////////////////////////////////////////////////////////////////////////////
  // datapath
  ///////////////////////////////////////////////////////////////////////////////

  assign PmSel_S     = LoadEn_S & ~(OpCode_SI[0] & (OpA_DI[$high(OpA_DI)] ^ OpBSign_SI));

  // muxes
  assign AddMux_D    = (LoadEn_S) ? OpA_DI  : BReg_DP;

  // attention: logical shift in case of negative operand B!
  assign BMux_D      = (LoadEn_S) ? OpB_DI : {CompInv_SP, (BReg_DP[$high(BReg_DP):1])};

  genvar index;
  generate
      for(index = 0; index < C_WIDTH; index++ )
      begin : bit_swapping
          assign ResReg_DP_rev[index] = ResReg_DP[C_WIDTH-1-index];
      end
  endgenerate

  assign OutMux_D    = (RemSel_SP) ? AReg_DP : ResReg_DP_rev;

  // invert if necessary
  assign Res_DO      = (ResInv_SP) ? -$signed(OutMux_D) : OutMux_D;

  // main comparator
  assign ABComp_S    = ((AReg_DP == BReg_DP) | ((AReg_DP > BReg_DP) ^ CompInv_SP)) & ((|AReg_DP) | OpBIsZero_SI);

  // main adder
  assign AddTmp_D    = (LoadEn_S) ? 0 : AReg_DP;
  assign AddOut_D    = (PmSel_S)  ? AddTmp_D + AddMux_D : AddTmp_D - $signed(AddMux_D);

  ///////////////////////////////////////////////////////////////////////////////
  // counter
  ///////////////////////////////////////////////////////////////////////////////

  assign Cnt_DN      = (LoadEn_S)   ? OpBShift_DI :
                       (~CntZero_S) ? Cnt_DP - 1  : Cnt_DP;

  assign CntZero_S   = ~(|Cnt_DP);

  ///////////////////////////////////////////////////////////////////////////////
  // FSM
  ///////////////////////////////////////////////////////////////////////////////

  always_comb
  begin : p_fsm
    // default
    State_SN       = State_SP;

    OutVld_SO      = 1'b0;

    LoadEn_S       = 1'b0;

    ARegEn_S       = 1'b0;
    BRegEn_S       = 1'b0;
    ResRegEn_S     = 1'b0;

    case (State_SP)
      /////////////////////////////////
      IDLE: begin
        OutVld_SO    = 1'b1;

        if(InVld_SI) begin
          OutVld_SO  = 1'b0;
          ARegEn_S   = 1'b1;
          BRegEn_S   = 1'b1;
          LoadEn_S   = 1'b1;
          State_SN   = DIVIDE;
        end
      end
      /////////////////////////////////
      DIVIDE: begin

        ARegEn_S     = ABComp_S;
        BRegEn_S     = 1'b1;
        ResRegEn_S   = 1'b1;

        // calculation finished
        // one more divide cycle (32nd divide cycle)
        if (CntZero_S) begin
          State_SN   = FINISH;
        end
      end
      /////////////////////////////////
      FINISH: begin
        OutVld_SO = 1'b1;

        if(OutRdy_SI) begin
          State_SN  = IDLE;
        end
      end
      /////////////////////////////////
      default : /* default */ ;
      /////////////////////////////////
    endcase
  end


  ///////////////////////////////////////////////////////////////////////////////
  // regs
  ///////////////////////////////////////////////////////////////////////////////

  // get flags
  assign RemSel_SN  = (LoadEn_S) ? OpCode_SI[1] : RemSel_SP;
  assign CompInv_SN = (LoadEn_S) ? OpBSign_SI   : CompInv_SP;
  assign ResInv_SN  = (LoadEn_S) ? (~OpBIsZero_SI | OpCode_SI[1]) & OpCode_SI[0] & (OpA_DI[$high(OpA_DI)] ^ OpBSign_SI) : ResInv_SP;

  assign AReg_DN   = (ARegEn_S)   ? AddOut_D : AReg_DP;
  assign BReg_DN   = (BRegEn_S)   ? BMux_D   : BReg_DP;
  assign ResReg_DN = (LoadEn_S)   ? '0       :
                     (ResRegEn_S) ? {ABComp_S, ResReg_DP[$high(ResReg_DP):1]} : ResReg_DP;

  always_ff @(posedge Clk_CI or negedge Rst_RBI) begin : p_regs
    if(~Rst_RBI) begin
       State_SP   <= IDLE;
       AReg_DP    <= '0;
       BReg_DP    <= '0;
       ResReg_DP  <= '0;
       Cnt_DP     <= '0;
       RemSel_SP  <= 1'b0;
       CompInv_SP <= 1'b0;
       ResInv_SP  <= 1'b0;
    end else begin
       State_SP   <= State_SN;
       AReg_DP    <= AReg_DN;
       BReg_DP    <= BReg_DN;
       ResReg_DP  <= ResReg_DN;
       Cnt_DP     <= Cnt_DN;
       RemSel_SP  <= RemSel_SN;
       CompInv_SP <= CompInv_SN;
       ResInv_SP  <= ResInv_SN;
    end
  end

  ///////////////////////////////////////////////////////////////////////////////
  // assertions
  ///////////////////////////////////////////////////////////////////////////////

`ifndef SYNTHESIS
  initial
  begin : p_assertions
    assert (C_LOG_WIDTH == $clog2(C_WIDTH+1)) else $error("C_LOG_WIDTH must be $clog2(C_WIDTH+1)");
  end
`endif

endmodule // serDiv
