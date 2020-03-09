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
 * BRAM Data Width Converter Testbench
 *
 * Current Maintainers:
 * - Andreas Kurth  <akurth@iis.ee.ethz.ch>
 * - Pirmin Vogel   <vogelpi@iis.ee.ethz.ch>
 */

`include "assertions.sv"

module Testbench

  // Parameters {{{
  #(
    parameter CLK_PERIOD      = 10ns,
    parameter STIM_APPL_DELAY =  5ns,
    parameter RESP_ACQ_DELAY  =  2ns,
    parameter STIM_PATH       = "./vectors/stim.txt",
    parameter EXP_RESP_PATH   = "./vectors/expresp.txt"
  );
  // }}}

  // Module-Wide Constants {{{
  localparam integer  ADDR_BITW     = 32;
  localparam integer  MST_DATA_BITW = 32;
  localparam integer  SLV_DATA_BITW = 96;
  // }}}

  // Clock and Reset Generator {{{
  logic Clk_C, Rst_RB, EndOfSim_S;
  ClkRstGen
    #(
      .CLK_LOW_TIME   (CLK_PERIOD/2),
      .CLK_HIGH_TIME  (CLK_PERIOD/2)
    )
    clkRstGen
    (
      .EndOfSim_SI  (EndOfSim_S),
      .Clk_CO       (Clk_C),
      .Rst_RBO      (Rst_RB)
    );
  // }}}

  // Instantiation of Master and Slave Interfaces to be connected {{{
  BramPort
    #(
      .DATA_BITW(MST_DATA_BITW),
      .ADDR_BITW(ADDR_BITW)
    ) Bram_PM ();
  BramPort
    #(
      .DATA_BITW(SLV_DATA_BITW),
      .ADDR_BITW(ADDR_BITW)
    ) Bram_PS ();
  // }}}

  // DUT Instantiation {{{
  BramDwc
    #(
      .ADDR_BITW    (ADDR_BITW),
      .MST_DATA_BITW(MST_DATA_BITW),
      .SLV_DATA_BITW(SLV_DATA_BITW)
    ) dut (
      .FromMaster_PS(Bram_PM),
      .ToSlave_PM   (Bram_PS)
    );
  // }}}

  // Master Driver {{{
  assign Bram_PM.Clk_C  = Clk_C;
  assign Bram_PM.Rst_R  = ~Rst_RB;
  assign Bram_PM.En_S   = '1;
  // }}}

  // Assert properties that always hold. {{{
  always @ (Bram_PM.Clk_C) begin
    assert (Bram_PS.Clk_C == Bram_PM.Clk_C)
      else $error("Slave clock is not equal to master clock!");
    assert (Bram_PS.En_S == Bram_PM.En_S)
      else $error("Slave enable signal is not equal to master enable signal!");
  end
  always @ (Bram_PM.Rst_R) begin
    assert (Bram_PS.Rst_R == Bram_PM.Rst_R)
      else $error("Slave reset signal is not equal to master reset signal!");
  end
  // }}}

  // Set simulation up. {{{
  integer stim_fd, expresp_fd;
  logic EndOfStim_S     = 0;
  logic EndOfExpResp_S  = 0;
  assign EndOfSim_S = EndOfStim_S && EndOfExpResp_S;
  initial begin

    // Open files with test vectors. {{{
    stim_fd = $fopen(STIM_PATH, "r");
    if (stim_fd == 0)
      $fatal(1, "Failed to open stimuli file '%s'!", STIM_PATH);
    expresp_fd = $fopen(EXP_RESP_PATH, "r");
    if (expresp_fd == 0)
      $fatal(1, "Failed to open expected responses file '%s'!", EXP_RESP_PATH);
    // }}}

  end
  // }}}

  // Apply stimuli. {{{
  string stim_vec;
  integer stim_read;
  struct {
    logic [32-1:0]  Addr_S;
    logic [ 4-1:0]  WrEn_S;
    logic [96-1:0]  Rd_D;
    logic [32-1:0]  Wr_D;
  } Stim;
  integer stim_ln = 0;
  always @ (posedge Clk_C) begin
    if (~EndOfStim_S) begin
      stim_read = 0;
      while (stim_read != 4) begin
        stim_ln   = stim_ln + 1;
        stim_read = $fgets(stim_vec, stim_fd);
        stim_read = $sscanf(stim_vec, "%h %h %h %h",
            Stim.Addr_S, Stim.WrEn_S, Stim.Wr_D, Stim.Rd_D);
        if ($feof(stim_fd)) begin
          EndOfStim_S = 1;
          break;
        end
      end
      #STIM_APPL_DELAY;
      Bram_PM.Addr_S  = Stim.Addr_S;
      Bram_PM.WrEn_S  = Stim.WrEn_S;
      Bram_PM.Wr_D    = Stim.Wr_D;
      Bram_PS.Rd_D    = Stim.Rd_D;
    end
  end
  // }}}

  // Acquire and compare expected responses. {{{
  logic ExpRespAcqEn_S = 0;
  string expresp_vec;
  integer expresp_read;
  struct {
    logic [32-1:0]  Addr_S;
    logic [12-1:0]  WrEn_S;
    logic [32-1:0]  Rd_D;
    logic [96-1:0]  Wr_D;
  } ExpResp;
  integer expresp_ln = 0;
  always @ (posedge Clk_C) begin
    if (ExpRespAcqEn_S) begin
      if (~EndOfExpResp_S) begin
        expresp_read = 0;
        while (expresp_read != 4) begin
          expresp_ln = expresp_ln + 1;
          expresp_read = $fgets(expresp_vec, expresp_fd);
          expresp_read = $sscanf(expresp_vec, "%h %h %h %h",
              ExpResp.Addr_S, ExpResp.WrEn_S, ExpResp.Wr_D, ExpResp.Rd_D);
          if ($feof(expresp_fd)) begin
            EndOfExpResp_S = 1;
            break;
          end
        end
        if (~EndOfExpResp_S) begin
          #RESP_ACQ_DELAY;
          `assert_equal_msg(Bram_PS.Addr_S, ExpResp.Addr_S, "Addr_S", expresp_ln);
          `assert_equal_msg(Bram_PS.WrEn_S, ExpResp.WrEn_S, "WrEn_S", expresp_ln);
          `assert_equal_msg(Bram_PS.Wr_D,   ExpResp.Wr_D, "Wr_D", expresp_ln);
          `assert_equal_msg(Bram_PM.Rd_D,   ExpResp.Rd_D, "Rd_D", expresp_ln);
        end
      end
    end else begin
      ExpRespAcqEn_S = 1;
    end
  end

  // }}}

  // Deactivated Tests {{{

  // The following code would correctly fail fatally.  The code is currently inactive to avoid
  // confusion with real assertion failures.
  /*
  BramPort
    #(
      .DATA_BITW(96),
      .ADDR_BITW(32)
    ) wideMaster ();
  BramPort
    #(
      .DATA_BITW(32),
      .ADDR_BITW(32)
    ) narrowSlave ();
  BramDwc incorrectFromToBitwidths
    (
      .FromMaster_PS(wideMaster),
      .ToSlave_PM   (narrowSlave)
    );
  */

  // }}}

endmodule

// vim: nosmartindent autoindent foldmethod=marker
