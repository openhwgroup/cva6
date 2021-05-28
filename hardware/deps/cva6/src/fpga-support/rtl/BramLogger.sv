// Copyright 2016 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

/**
 * BRAM Logger
 *
 * Module that logs timestamped events on a user-defined synchronous trigger and with user-defined
 * meta data to a BRAM array.
 *
 * Port Description:
 *
 *  Clk_CI            All logging and control operations are synchronous to this clock.
 *  TimestampClk_CI   The timestamp counter is synchronous to this clock.
 *  Rst_RBI           Synchronous active-low reset for control logic and registers.  Does NOT reset
 *                    the cells of the internal BRAM.
 *
 *  LogData_DI        Meta data to be stored for each event.
 *  LogTrigger_SI     If this signal is high during a rising edge of `Clk_CI` (and the logger is
 *                    enabled), a log entry is added.
 *
 *  Clear_SI          Start signal to clear the internal BRAM.
 *  LogEn_SI          Enables logging.
 *
 *  Full_SO           Active if the BRAM is nearly or completely full.
 *  Ready_SO          Active if the logger is ready to log events.  Inactive during clearing.
 *
 *  Bram_PS           Slave interface to access the internal BRAM (e.g., over AXI via an AXI BRAM
 *                    Controller).
 *
 * In the BRAM, events are stored consecutively in multiple words each.  The first word of a log
 * entry is the 32-bit wide timestamp.  All other words are defined by the user via `LogData_DI`.
 *
 * For the memory consumption by the internal BRAM, refer to the documentation of the employed BRAM
 * module.
 *
 * During clearing, the logging memory is traversed sequentially.  Thus, clearing takes
 * `NUM_LOG_ENTRIES` clock cycles.
 *
 * Current Maintainers:
 * - Andreas Kurth  <akurth@iis.ee.ethz.ch>
 * - Pirmin Vogel   <vogelpi@iis.ee.ethz.ch>
 */

import CfMath::ceil_div, CfMath::log2;

module BramLogger

  // Parameters {{{
  #(

    // Width (in bits) of one log data payload.  Value should be a multiple of 32.
    parameter LOG_DATA_BITW   =    32,

    // Number of entries in the log.  Value must be >= 1024, should be a multiple of 1024, and is
    // upper-bound by the available memory.
    parameter NUM_LOG_ENTRIES = 16384

  )
  // }}}

  // Ports {{{
  (

    input  logic                        Clk_CI,
    input  logic                        TimestampClk_CI,
    input  logic                        Rst_RBI,

    // Logging Input
    input  logic [LOG_DATA_BITW-1:0]    LogData_DI,
    input  logic                        LogTrigger_SI,

    // Control Input
    input  logic                        Clear_SI,
    input  logic                        LogEn_SI,

    // Status Output
    output logic                        Full_SO,
    output logic                        Ready_SO,

    // Interface to Internal BRAM
    BramPort.Slave                      Bram_PS

  );
  // }}}

  // Module-Wide Constants {{{

  // Properties of the data entries in the log
  localparam integer TIMESTAMP_BITW         = 32;
  localparam integer LOG_ENTRY_BITW         = ceil_div(TIMESTAMP_BITW+LOG_DATA_BITW, 32) * 32;
  localparam integer LOG_ENTRY_BYTEW        = LOG_ENTRY_BITW / 8;
  localparam integer TIMESTAMP_LOW          = 0;
  localparam integer TIMESTAMP_HIGH         = TIMESTAMP_LOW + TIMESTAMP_BITW - 1;
  localparam integer LOG_DATA_LOW           = TIMESTAMP_HIGH + 1;
  localparam integer LOG_DATA_HIGH          = LOG_DATA_LOW + LOG_DATA_BITW - 1;

  // Properties used when addressing the BRAM array
  localparam integer LOGGING_CNT_BITW       = log2(NUM_LOG_ENTRIES);
  localparam integer LOGGING_CNT_MAX        = NUM_LOG_ENTRIES-1;
  localparam integer LOGGING_ADDR_WORD_BITO = log2(LOG_ENTRY_BYTEW);
  localparam integer LOGGING_ADDR_BITW      = LOGGING_CNT_BITW + LOGGING_ADDR_WORD_BITO;

  // }}}

  // Signal Declarations {{{
  logic                           Rst_R;

  enum reg [1:0]  {READY, CLEARING, FULL}
                                  State_SP,     State_SN;

  reg   [LOGGING_CNT_BITW -1:0]   WrCntA_SP,    WrCntA_SN;
  logic [LOG_ENTRY_BITW   -1:0]   WrA_D;
  logic [LOG_ENTRY_BYTEW  -1:0]   WrEnA_S;

  reg   [TIMESTAMP_BITW-1:0]      Timestamp_SP, Timestamp_SN;
  // }}}

  // Permanent Signal Assignments {{{
  assign Rst_R = ~Rst_RBI;
  // }}}

  // Internal BRAM Interfaces {{{
  BramPort #(
      .DATA_BITW(LOG_ENTRY_BITW),
      .ADDR_BITW(LOGGING_ADDR_BITW)
    ) BramLog_P ();
  assign BramLog_P.Clk_C  = Clk_CI;
  assign BramLog_P.Rst_R  = Rst_R;
  assign BramLog_P.En_S   = WrEnA_S;
  always_comb begin
    BramLog_P.Addr_S = '0;
    BramLog_P.Addr_S[LOGGING_ADDR_BITW-1:0] = (WrCntA_SP << LOGGING_ADDR_WORD_BITO);
  end
  assign BramLog_P.Wr_D   = WrA_D;
  assign BramLog_P.WrEn_S = WrEnA_S;

  BramPort #(
      .DATA_BITW(LOG_ENTRY_BITW),
      .ADDR_BITW(LOGGING_ADDR_BITW)
    ) BramDwc_P ();
  // }}}

  // Instantiation of True Dual-Port BRAM Array {{{
  TdpBramArray #(
      .DATA_BITW(LOG_ENTRY_BITW),
      .NUM_ENTRIES(NUM_LOG_ENTRIES)
    ) bramArr (
      .A_PS(BramLog_P),
      .B_PS(BramDwc_P)
    );
  // }}}

  // Instantiation of Data Width Converter {{{
  BramDwc
    #(
      .ADDR_BITW      (Bram_PS.ADDR_BITW),
      .MST_DATA_BITW  (32),
      .SLV_DATA_BITW  (LOG_ENTRY_BITW)
    ) bramDwc (
      .FromMaster_PS(Bram_PS),
      .ToSlave_PM   (BramDwc_P)
    );
  // }}}

  // Control FSM {{{

  always_comb begin
    // Default Assignments
    Full_SO   = 0;
    Ready_SO  = 0;
    WrCntA_SN = WrCntA_SP;
    WrEnA_S   = '0;
    State_SN  = State_SP;

    case (State_SP)

      READY: begin
        Ready_SO = 1;
        if (LogEn_SI && LogTrigger_SI && ~Clear_SI) begin
          WrCntA_SN = WrCntA_SP + 1;
          WrEnA_S   = '1;
        end
        // Raise "Full" output if BRAMs are nearly full (i.e., 1024 entries earlier).
        if (WrCntA_SP >= (LOGGING_CNT_MAX-1024)) begin
          Full_SO = 1;
        end
        if (WrCntA_SP == LOGGING_CNT_MAX) begin
          State_SN = FULL;
        end
        if (Clear_SI && WrCntA_SP != 0) begin
          WrCntA_SN = 0;
          State_SN  = CLEARING;
        end
      end

      CLEARING: begin
        WrCntA_SN = WrCntA_SP + 1;
        WrEnA_S   = '1;
        if (WrCntA_SP == LOGGING_CNT_MAX) begin
          WrCntA_SN = 0;
          State_SN  = READY;
        end
      end

      FULL: begin
        Full_SO = 1;
        if (Clear_SI) begin
          WrCntA_SN = 0;
          State_SN  = CLEARING;
        end
      end

    endcase
  end

  // }}}

  // Log Data Formatting {{{
  always_comb begin
    WrA_D = '0;
    if (State_SP != CLEARING) begin
      WrA_D[TIMESTAMP_HIGH:TIMESTAMP_LOW] = Timestamp_SP;
      WrA_D[ LOG_DATA_HIGH: LOG_DATA_LOW] = LogData_DI;
    end
  end
  // }}}

  // Timestamp Counter {{{
  always_comb
  begin
    Timestamp_SN = Timestamp_SP + 1;
    if (Timestamp_SP == {TIMESTAMP_BITW{1'b1}}) begin
      Timestamp_SN = 0;
    end
  end
  // }}}

  // Flip-Flops {{{

  always_ff @ (posedge Clk_CI)
  begin
    State_SP    <= READY;
    WrCntA_SP   <= 0;
    if (Rst_RBI) begin
      State_SP    <= State_SN;
      WrCntA_SP   <= WrCntA_SN;
    end
  end

  always_ff @ (posedge TimestampClk_CI)
  begin
    Timestamp_SP  <= 0;
    if (Rst_RBI) begin
      Timestamp_SP  <= Timestamp_SN;
    end
  end

  // }}}

endmodule

// vim: nosmartindent autoindent foldmethod=marker
