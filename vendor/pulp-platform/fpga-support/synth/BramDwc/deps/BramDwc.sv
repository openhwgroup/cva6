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
 * BRAM Data Width Converter
 *
 * This module performs data width conversion between a narrow master and a wide slave interface.
 *
 * Port Description:
 *  FromMaster_PS   Slave BRAM Port interface through which master control signals go to the BRAM.
 *  ToSlave_PM      Master BRAM Port interface at which the slave BRAM is connected.
 *
 * The data signal of the master interface must be narrower than that of the slave interface.  The
 * reverse situation would require handshaking and buffering and is not supported by the simple BRAM
 * Port interface.
 *
 * Parameter Description:
 *  ADDR_BITW       The width (in bits) of the address signals.  Both ports must have the same
 *                  address width.
 *  MST_DATA_BITW   The width (in bits) of the data signal coming from the master controller.
 *  SLV_DATA_BITW   The width (in bits) of the data signal of the slave BRAM.
 *
 *  The value of all parameters must match the connected interfaces.  DO NOT rely on the default
 *  values for these parameters, but explicitly set the parameters so that they are correct for your
 *  setup!  If one or more values do not match, the behavior of this module is undefined.
 *
 * Compatibility Information:
 *  ModelSim    >= 10.0b
 *  Vivado      >= 2016.1
 *
 *  Earlier versions of the tools are either untested or known to fail for this module.
 *
 * Current Maintainers:
 * - Andreas Kurth  <akurth@iis.ee.ethz.ch>
 * - Pirmin Vogel   <vogelpi@iis.ee.ethz.ch>
 */

import CfMath::ceil_div, CfMath::log2;

module BramDwc

  // Parameters {{{
  #(
    parameter integer ADDR_BITW     = 32,
    parameter integer MST_DATA_BITW = 32,
    parameter integer SLV_DATA_BITW = 96
  )
  // }}}

  // Ports {{{
  (
    BramPort.Slave  FromMaster_PS,
    BramPort.Master ToSlave_PM
  );
  // }}}

  // Module-Wide Constants {{{
  localparam integer  MST_DATA_BYTEW      = MST_DATA_BITW/8;
  localparam integer  MST_ADDR_WORD_BITO  = log2(MST_DATA_BYTEW);
  localparam integer  MST_ADDR_WORD_BITW  = ADDR_BITW - MST_ADDR_WORD_BITO;

  localparam integer  SLV_DATA_BYTEW      = SLV_DATA_BITW/8;
  localparam integer  SLV_ADDR_WORD_BITO  = log2(SLV_DATA_BYTEW);
  localparam integer  SLV_ADDR_WORD_BITW  = ADDR_BITW - SLV_ADDR_WORD_BITO;

  localparam integer  PAR_IDX_MAX_VAL     = ceil_div(SLV_DATA_BITW, MST_DATA_BITW) - 1;
  localparam integer  PAR_IDX_BITW        = log2(PAR_IDX_MAX_VAL+1);
  // }}}

  // Initial Assertions {{{
  initial begin
    assert (SLV_DATA_BITW >= MST_DATA_BITW)
      else $fatal(1, "Downconversion of the data bitwidth from master to slave is not possible!");
    assert (MST_DATA_BITW == FromMaster_PS.DATA_BITW)
      else $fatal(1, "Parameter for data width of master does not match connected interface!");
    assert (SLV_DATA_BITW == ToSlave_PM.DATA_BITW)
      else $fatal(1, "Parameter for data width of slave does not match connected interface!");
    assert ((ADDR_BITW == FromMaster_PS.ADDR_BITW) && (ADDR_BITW == ToSlave_PM.ADDR_BITW))
      else $fatal(1, "Parameter for address width does not match connected interfaces!");
  end
  // }}}

  // Register the Addr_S of master interface to make sure the address stays
  // stable for word selection on reads
  logic [ADDR_BITW-1:0] Addr_SN, Addr_SP;
  assign Addr_SN = FromMaster_PS.Addr_S;

  always_ff @ (posedge FromMaster_PS.Clk_C)
  begin
    if (FromMaster_PS.Rst_R == 1'b1) begin
      Addr_SP <= 'b0;
    end else if (FromMaster_PS.En_S == 1'b1) begin
      Addr_SP <= Addr_SN;
    end
  end

  // Pass clock, reset, and enable through. {{{
  assign ToSlave_PM.Clk_C = FromMaster_PS.Clk_C;
  assign ToSlave_PM.Rst_R = FromMaster_PS.Rst_R;
  assign ToSlave_PM.En_S  = FromMaster_PS.En_S;
  // }}}

  // Data Width Conversion {{{

  logic [MST_ADDR_WORD_BITW-1:0] MstWordAddr_S, MstWordAddrReg_S;
  assign MstWordAddr_S    = Addr_SN[(MST_ADDR_WORD_BITW-1)+MST_ADDR_WORD_BITO:MST_ADDR_WORD_BITO];
  assign MstWordAddrReg_S = Addr_SP[(MST_ADDR_WORD_BITW-1)+MST_ADDR_WORD_BITO:MST_ADDR_WORD_BITO];

  logic [SLV_ADDR_WORD_BITW-1:0] ToWordAddr_S;
  assign ToWordAddr_S = MstWordAddr_S / (PAR_IDX_MAX_VAL+1);

  always_comb begin
    ToSlave_PM.Addr_S = '0;
    ToSlave_PM.Addr_S[(SLV_ADDR_WORD_BITW-1)+SLV_ADDR_WORD_BITO:SLV_ADDR_WORD_BITO] = ToWordAddr_S;
  end

  logic [PAR_IDX_BITW-1:0] ParIdxRd_S, ParIdxWr_S;
  assign ParIdxWr_S = MstWordAddr_S    % (PAR_IDX_MAX_VAL+1);
  assign ParIdxRd_S = MstWordAddrReg_S % (PAR_IDX_MAX_VAL+1); // based on address applied with En_S

  logic [PAR_IDX_MAX_VAL:0] [MST_DATA_BITW-1:0]  Rd_D;
  genvar p;
  for (p = 0; p <= PAR_IDX_MAX_VAL; p++) begin
    localparam integer SLV_BYTE_LOW   = MST_DATA_BYTEW*p;
    localparam integer SLV_BYTE_HIGH  = SLV_BYTE_LOW + (MST_DATA_BYTEW-1);
    localparam integer SLV_BIT_LOW    = MST_DATA_BITW*p;
    localparam integer SLV_BIT_HIGH   = SLV_BIT_LOW + (MST_DATA_BITW-1);
    always_comb begin
      if (ParIdxWr_S == p) begin
        ToSlave_PM.WrEn_S[SLV_BYTE_HIGH:SLV_BYTE_LOW] = FromMaster_PS.WrEn_S;
      end else begin
        ToSlave_PM.WrEn_S[SLV_BYTE_HIGH:SLV_BYTE_LOW] = '0;
      end
    end
    assign Rd_D[p] = ToSlave_PM.Rd_D[SLV_BIT_HIGH:SLV_BIT_LOW];
    assign ToSlave_PM.Wr_D[SLV_BIT_HIGH:SLV_BIT_LOW] = FromMaster_PS.Wr_D;
  end
  assign FromMaster_PS.Rd_D = Rd_D[ParIdxRd_S];

  // }}}

endmodule

// vim: nosmartindent autoindent foldmethod=marker
