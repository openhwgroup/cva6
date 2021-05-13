// 
// Copyright 2021 OpenHW Group
// Copyright 2021 Datum Technology Corporation
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
// 
// Licensed under the Solderpad Hardware License v 2.1 (the "License"); you may
// not use this file except in compliance with the License, or, at your option,
// the Apache License version 2.0. You may obtain a copy of the License at
// 
//     https://solderpad.org/licenses/SHL-2.1/
// 
// Unless required by applicable law or agreed to in writing, any work
// distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
// WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
// License for the specific language governing permissions and limitations
// under the License.
// 


`ifndef __UVMA_OBI_IF_SV__
`define __UVMA_OBI_IF_SV__


/**
 * Encapsulates all signals and clocking of Open Bus Interface interface. Used
 * by monitor (uvma_obi_mon_c) and driver (uvma_obi_drv_c).
 */
interface uvma_obi_if #(
   parameter AUSER_WIDTH = `UVMA_OBI_AUSER_DEFAULT_WIDTH, ///< Width of the auser signal. RI5CY, Ibex, CV32E40* do not have the auser signal.
   parameter WUSER_WIDTH = `UVMA_OBI_WUSER_DEFAULT_WIDTH, ///< Width of the wuser signal. RI5CY, Ibex, CV32E40* do not have the wuser signal.
   parameter RUSER_WIDTH = `UVMA_OBI_RUSER_DEFAULT_WIDTH, ///< Width of the ruser signal. RI5CY, Ibex, CV32E40* do not have the ruser signal.
   parameter ADDR_WIDTH  = `UVMA_OBI_ADDR_DEFAULT_WIDTH , ///< Width of the addr signal.
   parameter DATA_WIDTH  = `UVMA_OBI_DATA_DEFAULT_WIDTH , ///< Width of the rdata and wdata signals. be width is DATA_WIDTH / 8. Valid DATA_WIDTH settings are 32 and 64.
   parameter ID_WIDTH    = `UVMA_OBI_ID_DEFAULT_WIDTH   , ///< Width of the aid and rid signals.
   parameter ACHK_WIDTH  = `UVMA_OBI_ACHK_DEFAULT_WIDTH , ///< Width of the achk signal.
   parameter RCHK_WIDTH  = `UVMA_OBI_RCHK_DEFAULT_WIDTH   ///< Width of the rchk signal.
)
(
   input logic clk    , ///< The bus clock times all bus transfers. All signal timings are related to the rising edge of clk.
   input logic reset_n  ///< The bus reset signal is active LOW and resets the system and the bus. This is the only active LOW signal.
);
   
   // 'A Channel' signals
   wire                         req    ; ///< Address transfer request. req=1 signals the availability of valid address phase signals.
   wire                         gnt    ; ///< Grant. Ready to accept address transfer. Address transfer is accepted on rising clk with req=1 and gnt=1.
   wire [(ADDR_WIDTH-1):0]      addr   ; ///< Address
   wire                         we     ; ///< Write Enable, high for writes, low for reads.
   wire [((DATA_WIDTH/8)-1):0]  be     ; ///< Byte Enable. Is set for the bytes to write/read.
   wire [(DATA_WIDTH-1):0]      wdata  ; ///< Write data. Only valid for write transactions. Undefined for read transactions.
   wire [(AUSER_WIDTH-1):0]     auser  ; ///< Address Phase User signals. Valid for both read and write transactions.
   wire [(WUSER_WIDTH-1):0]     wuser  ; ///< Additional Address Phase User signals. Only valid for write transactions. Undefined for read transactions.
   wire [(ID_WIDTH-1):0]        aid    ; ///< Address Phase transaction identifier.
   wire [5:0]                   atop   ; ///< Atomic Operation.
   wire [1:0]                   memtype; ///< Memory type attributes.
   wire [2:0]                   prot   ; ///< Protection attributes.
   wire                         reqpar ; ///< Parity bit for req signal (odd parity).
   wire                         gntpar ; ///< Parity bit for gnt signal (odd parity).
   wire [(ACHK_WIDTH-1):0]      achk   ; ///< Checksum for address phase signals (except achk itself).
   
   
   // 'R Channel' signals
   wire                      rvalid   ; ///< Response transfer request. rvalid=1 signals the availability of valid response phase signals. Used for both reads and writes.
   wire                      rready   ; ///< Ready to accept response transfer. Response transfer is accepted on rising clk with rvalid=1 and rready=1.
   wire [(DATA_WIDTH-1):0]   rdata    ; ///< Read data. Only valid for read transactions. Undefined for write transactions.
   wire                      err      ; ///< Error.
   wire [(RUSER_WIDTH-1):0]  ruser    ; ///< Response phase User signals. Only valid for read transactions. Undefined for write transactions.
   wire [(ID_WIDTH-1):0]     rid      ; ///< Response Phase transaction identifier.
   wire                      exokay   ; ///< Exclusive transaction okay.
   wire                      rvalidpar; ///< Parity bit for rvalid signal (odd parity).
   wire                      rreadypar; ///< Parity bit for rready signal (odd parity).
   wire [(RCHK_WIDTH-1):0]   rchk     ; ///< Checksum for address phase signals (except rchk itself).
   
   
   /**
    * Used by DUT in 'mstr' mode.
    */
   clocking dut_mstr_cb @(posedge clk);
      input   gnt      ,
              gntpar   ,
              rvalid   ,
              rdata    ,
              err      ,
              ruser    ,
              rid      ,
              exokay   ,
              rvalidpar,
              rchk     ;
      output  req      ,
              addr     ,
              we       ,
              be       ,
              wdata    ,
              auser    ,
              wuser    ,
              aid      ,
              atop     ,
              memtype  ,
              prot     ,
              reqpar   ,
              achk     ,
              rready   ,
              rreadypar;
   endclocking : dut_mstr_cb
   
   /**
    * Used by DUT in 'slv' mode.
    */
   clocking dut_slv_cb @(posedge clk);
      input   req      ,
              addr     ,
              we       ,
              be       ,
              wdata    ,
              auser    ,
              wuser    ,
              aid      ,
              atop     ,
              memtype  ,
              prot     ,
              reqpar   ,
              achk     ,
              rready   ,
              rreadypar;
      output  gnt      ,
              gntpar   ,
              rvalid   ,
              rdata    ,
              err      ,
              ruser    ,
              rid      ,
              exokay   ,
              rvalidpar,
              rchk     ;
   endclocking : dut_slv_cb
   
   /**
    * Used by uvma_obi_drv_c.
    */
   clocking drv_mstr_cb @(posedge clk);
      input   gnt      ,
              gntpar   ,
              rvalid   ,
              rdata    ,
              err      ,
              ruser    ,
              rid      ,
              exokay   ,
              rvalidpar,
              rchk     ;
      output  req      ,
              addr     ,
              we       ,
              be       ,
              wdata    ,
              auser    ,
              wuser    ,
              aid      ,
              atop     ,
              memtype  ,
              prot     ,
              reqpar   ,
              achk     ,
              rready   ,
              rreadypar;
   endclocking : drv_mstr_cb
   
   /**
    * Used by uvma_obi_drv_c.
    */
   clocking drv_slv_cb @(posedge clk);
      input   req      ,
              addr     ,
              we       ,
              be       ,
              wdata    ,
              auser    ,
              wuser    ,
              aid      ,
              atop     ,
              memtype  ,
              prot     ,
              reqpar   ,
              achk     ,
              rready   ,
              rreadypar;
      output  gnt      ,
              gntpar   ,
              rvalid   ,
              rdata    ,
              err      ,
              ruser    ,
              rid      ,
              exokay   ,
              rvalidpar,
              rchk     ;
   endclocking : drv_slv_cb
   
   /**
    * Used by uvma_obi_mon_c.
    */
   clocking mon_cb @(posedge clk);
      input   req      ,
              gnt      ,
              addr     ,
              we       ,
              be       ,
              wdata    ,
              auser    ,
              wuser    ,
              aid      ,
              atop     ,
              memtype  ,
              prot     ,
              reqpar   ,
              gntpar   ,
              achk     ,
              rvalid   ,
              rready   ,
              rdata    ,
              err      ,
              ruser    ,
              rid      ,
              exokay   ,
              rvalidpar,
              rreadypar,
              rchk     ;
   endclocking : mon_cb
   
   
   modport dut_mstr_mp   (clocking dut_mstr_cb); ///< Used by DUT in 'mstr' mode.
   modport dut_slv_mp    (clocking dut_slv_cb ); ///< Used by DUT in 'slv' mode.
   modport active_mstr_mp(clocking drv_mstr_cb); ///< Used by uvma_obi_drv_c in 'mstr' mode.
   modport active_slv_mp (clocking drv_slv_cb ); ///< Used by uvma_obi_drv_c in 'slv' mode.
   modport passive_mp    (clocking mon_cb     ); ///< Used by uvma_obi_mon_c.
   
endinterface : uvma_obi_if


`endif // __UVMA_OBI_IF_SV__
