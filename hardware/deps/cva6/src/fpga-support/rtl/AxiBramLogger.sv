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
 * AXI BRAM Logger
 *
 * Module that logs AXI accesses with timestamps.  This module is built on top of `BramLogger`, and
 * all ports that are not the logged AXI inputs are documented there, along with other properties.
 *
 * Log Format:
 *  - first word: 32-bit timestamp
 *  - second word:  lowest `AXI_LEN_BITW` bits: AxiLen_DI
 *                  all following bits: AxiId_DI
 *  - third word (and fourth word for 64-bit addresses): AxiAddr_DI
 *
 * Current Maintainers:
 * - Andreas Kurth  <akurth@iis.ee.ethz.ch>
 * - Pirmin Vogel   <vogelpi@iis.ee.ethz.ch>
 */

import CfMath::ceil_div;

module AxiBramLogger

  // Parameters {{{
  #(

    // Width (in bits) of the logged AXI ID.  Value must be in [1, 24].
    parameter AXI_ID_BITW     =     8,

    // Width (in bits) of the logged AXI address.  Value must be either 32 or 64.
    parameter AXI_ADDR_BITW   =    32,

    // Number of entries in the log.  Value must be >= 1024, should be a multiple of 1024, and is
    // upper-bound by the available memory.
    parameter NUM_LOG_ENTRIES = 16384,

    // The following "parameters" must not be changed from their given value.  They are solely
    // declared here because they define the width of some of the ports.
    parameter AXI_LEN_BITW    =     8

  )
  // }}}

  // Ports {{{
  (
    input  logic                        Clk_CI,
    input  logic                        TimestampClk_CI,
    input  logic                        Rst_RBI,

    // AXI Input
    input  logic                        AxiValid_SI,
    input  logic                        AxiReady_SI,
    input  logic  [AXI_ID_BITW  -1:0]   AxiId_DI,
    input  logic  [AXI_ADDR_BITW-1:0]   AxiAddr_DI,
    input  logic  [AXI_LEN_BITW -1:0]   AxiLen_DI,

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
  localparam integer META_BITW              = ceil_div(AXI_LEN_BITW+AXI_ID_BITW, 32) * 32;
  localparam integer LOGGING_DATA_BITW      = ceil_div(META_BITW+AXI_ADDR_BITW, 32) * 32;
  localparam integer AXI_LEN_LOW            = 0;
  localparam integer AXI_LEN_HIGH           = AXI_LEN_LOW + AXI_LEN_BITW - 1;
  localparam integer AXI_ID_LOW             = AXI_LEN_HIGH + 1;
  localparam integer AXI_ID_HIGH            = AXI_ID_LOW + AXI_ID_BITW - 1;
  localparam integer AXI_ADDR_LOW           = META_BITW;
  localparam integer AXI_ADDR_HIGH          = AXI_ADDR_LOW + AXI_ADDR_BITW - 1;

  // }}}

  // BRAM Logger Instantiation {{{

  logic LogTrigger_S;
  assign LogTrigger_S = AxiValid_SI && AxiReady_SI;

  logic [LOGGING_DATA_BITW-1:0] LogData_D;
  always_comb begin
    LogData_D = '0;
    LogData_D[ AXI_LEN_HIGH: AXI_LEN_LOW] = AxiLen_DI;
    LogData_D[  AXI_ID_HIGH:  AXI_ID_LOW] = AxiId_DI;
    LogData_D[AXI_ADDR_HIGH:AXI_ADDR_LOW] = AxiAddr_DI;
  end

  BramLogger #(
    .LOG_DATA_BITW    (LOGGING_DATA_BITW),
    .NUM_LOG_ENTRIES  (NUM_LOG_ENTRIES)
  ) bramLogger (
    .Clk_CI           (Clk_CI),
    .TimestampClk_CI  (TimestampClk_CI),
    .Rst_RBI          (Rst_RBI),
    .LogData_DI       (LogData_D),
    .LogTrigger_SI    (LogTrigger_S),
    .Clear_SI         (Clear_SI),
    .LogEn_SI         (LogEn_SI),
    .Full_SO          (Full_SO),
    .Ready_SO         (Ready_SO),
    .Bram_PS          (Bram_PS)
  );

  // }}}

endmodule

// vim: nosmartindent autoindent foldmethod=marker
