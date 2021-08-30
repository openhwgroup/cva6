// Copyright 2020 OpenHW Group
// Copyright 2020 Datum Technology Corporation
// Copyright 2020 Silicon Labs, Inc.
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     https://solderpad.org/licenses/
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

// This module facilitates easy connection of a uvma_obi_memory_if instance to the assertion module,
// which has individual wire ports

module uvma_obi_memory_assert_if_wrp
  import uvm_pkg::*;
  #(
    parameter int unsigned ADDR_WIDTH  = 32,
    parameter int unsigned DATA_WIDTH  = 32,
    parameter int unsigned AUSER_WIDTH = 0,
    parameter int unsigned WUSER_WIDTH = 0,
    parameter int unsigned RUSER_WIDTH = 0,
    parameter int unsigned ID_WIDTH    = 0,
    parameter int unsigned ACHK_WIDTH  = 0,
    parameter int unsigned RCHK_WIDTH  = 0,
    parameter bit          IS_1P2      = 0
  )
  (
    uvma_obi_memory_if obi
  );


  // ---------------------------------------------------------------------------
  // Local parameters
  // ---------------------------------------------------------------------------

  // Some "WIDTHs" may be zero, set these to 1 to avoid negative bit-vector indices
  localparam EFF_ID_WIDTH    = ID_WIDTH == 0 ? 1 : ID_WIDTH;
  localparam EFF_AUSER_WIDTH = AUSER_WIDTH == 0 ? 1 : AUSER_WIDTH;
  localparam EFF_RUSER_WIDTH = RUSER_WIDTH == 0 ? 1 : RUSER_WIDTH;
  localparam EFF_WUSER_WIDTH = WUSER_WIDTH == 0 ? 1 : WUSER_WIDTH;
  localparam EFF_ACHK_WIDTH  = ACHK_WIDTH == 0 ? 1 : ACHK_WIDTH;
  localparam EFF_RCHK_WIDTH  = RCHK_WIDTH == 0 ? 1 : RCHK_WIDTH;

  // ---------------------------------------------------------------------------
  // Begin module code
  // ---------------------------------------------------------------------------

  uvma_obi_memory_assert#(
    .ADDR_WIDTH(ADDR_WIDTH),
    .DATA_WIDTH(DATA_WIDTH),
    .AUSER_WIDTH(AUSER_WIDTH),
    .WUSER_WIDTH(WUSER_WIDTH),
    .RUSER_WIDTH(RUSER_WIDTH),
    .ID_WIDTH(ID_WIDTH),
    .ACHK_WIDTH(ACHK_WIDTH),
    .RCHK_WIDTH(RCHK_WIDTH),
    .IS_1P2(IS_1P2)
  ) u_assert(
    .clk(obi.clk),
    .reset_n(obi.reset_n),
    .req(obi.req),
    .gnt(obi.gnt),
    .addr(obi.addr[ADDR_WIDTH-1:0]),
    .we(obi.we),
    .be(obi.be),
    .wdata(obi.wdata[DATA_WIDTH-1:0]),
    .auser(obi.auser[EFF_AUSER_WIDTH-1:0]),
    .wuser(obi.wuser[EFF_WUSER_WIDTH-1:0]),
    .aid(obi.aid[EFF_ID_WIDTH-1:0]),
    .atop(obi.atop),
    .memtype(obi.memtype),
    .prot(obi.prot),
    .reqpar(obi.reqpar),
    .gntpar(obi.gntpar),
    .achk(obi.achk[EFF_ACHK_WIDTH-1:0]),
    .rdata(obi.rdata[DATA_WIDTH-1:0]),
    .rvalid(obi.rvalid),
    .rready(obi.rready),
    .err(obi.err),
    .ruser(obi.ruser[EFF_RUSER_WIDTH-1:0]),
    .rid(obi.rid[EFF_ID_WIDTH-1:0]),
    .exokay(obi.exokay),
    .rvalidpar(obi.rvalidpar),
    .rreadypar(obi.rreadypar),
    .rchk(obi.rchk[EFF_RCHK_WIDTH-1:0])
  );

endmodule : uvma_obi_memory_assert_if_wrp
