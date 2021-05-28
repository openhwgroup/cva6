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
 * BRAM Port Interface
 *
 * This interface contains all signals required to connect a Block RAM.
 *
 * Parameter Description:
 *  DATA_BITW   Width of the data ports in bits.  Must be a multiple of 8.
 *  ADDR_BITW   Width of the address port in bits.  Must be a multiple of 8.
 *
 * Port Description:
 *  Clk_C   All operations on this interface are synchronous to this single-phase clock port.
 *  Rst_R   Synchronous reset for the output register/latch of the interface; does NOT reset the
 *          BRAM.  Note that this reset is active high.
 *  En_S    Enables read, write, and reset operations to through this interface.
 *  Addr_S  Byte-wise address for all operations on this interface.  Note that the word address
 *          offset varies with `DATA_BITW`!
 *  Rd_D    Data output for read operations on the BRAM.
 *  Wr_D    Data input for write operations on the BRAM.
 *  WrEn_S  Byte-wise write enable.
 *
 * Current Maintainers:
 * - Andreas Kurth  <akurth@iis.ee.ethz.ch>
 * - Pirmin Vogel   <vogelpi@iis.ee.ethz.ch>
 */

interface BramPort
  #(
    parameter DATA_BITW = 32,
    parameter ADDR_BITW = 32
  );

  logic                       Clk_C;
  logic                       Rst_R;
  logic                       En_S;
  logic  [ADDR_BITW-1:0]      Addr_S;
  logic  [DATA_BITW-1:0]      Rd_D;
  logic  [DATA_BITW-1:0]      Wr_D;
  logic  [(DATA_BITW/8)-1:0]  WrEn_S;

  modport Slave (
    input  Clk_C, Rst_R, En_S, Addr_S, Wr_D, WrEn_S,
    output Rd_D
  );

  modport Master (
    input  Rd_D,
    output Clk_C, Rst_R, En_S, Addr_S, Wr_D, WrEn_S
  );

endinterface

// vim: nosmartindent autoindent
