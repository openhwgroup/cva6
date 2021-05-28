// Copyright (c) 2014-2018 ETH Zurich, University of Bologna
//
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Fabian Schuiki <fschuiki@iis.ee.ethz.ch>

package axi_pkg;

  typedef logic [1:0] burst_t;
  typedef logic [1:0] resp_t;
  typedef logic [3:0] cache_t;
  typedef logic [2:0] prot_t;
  typedef logic [3:0] qos_t;
  typedef logic [3:0] region_t;
  typedef logic [7:0] len_t;
  typedef logic [2:0] size_t;
  typedef logic [5:0] atop_t; // atomic operations
  typedef logic [3:0] nsaid_t; // non-secure address identifier

  localparam BURST_FIXED = 2'b00;
  localparam BURST_INCR  = 2'b01;
  localparam BURST_WRAP  = 2'b10;

  localparam RESP_OKAY   = 2'b00;
  localparam RESP_EXOKAY = 2'b01;
  localparam RESP_SLVERR = 2'b10;
  localparam RESP_DECERR = 2'b11;

  localparam CACHE_BUFFERABLE = 4'b0001;
  localparam CACHE_MODIFIABLE = 4'b0010;
  localparam CACHE_RD_ALLOC   = 4'b0100;
  localparam CACHE_WR_ALLOC   = 4'b1000;

  // ATOP[5:0]
  localparam ATOP_ATOMICSWAP  = 6'b110000;
  localparam ATOP_ATOMICCMP   = 6'b110001;
  // ATOP[5:4]
  localparam ATOP_NONE        = 2'b00;
  localparam ATOP_ATOMICSTORE = 2'b01;
  localparam ATOP_ATOMICLOAD  = 2'b10;
  // ATOP[3]
  localparam ATOP_LITTLE_END  = 1'b0;
  localparam ATOP_BIG_END     = 1'b1;
  // ATOP[2:0]
  localparam ATOP_ADD   = 3'b000;
  localparam ATOP_CLR   = 3'b001;
  localparam ATOP_EOR   = 3'b010;
  localparam ATOP_SET   = 3'b011;
  localparam ATOP_SMAX  = 3'b100;
  localparam ATOP_SMIN  = 3'b101;
  localparam ATOP_UMAX  = 3'b110;
  localparam ATOP_UMIN  = 3'b111;

  // 4 is recommended by AXI standard, so lets stick to it, do not change
  localparam IdWidth   = 4;
  localparam UserWidth = 1;
  localparam AddrWidth = 64;
  localparam DataWidth = 64;
  localparam StrbWidth = DataWidth / 8;

  typedef logic [IdWidth-1:0]   id_t;
  typedef logic [AddrWidth-1:0] addr_t;
  typedef logic [DataWidth-1:0] data_t;
  typedef logic [StrbWidth-1:0] strb_t;
  typedef logic [UserWidth-1:0] user_t;

  // AW Channel
  typedef struct packed {
      id_t     id;
      addr_t   addr;
      len_t    len;
      size_t   size;
      burst_t  burst;
      logic   lock;
      cache_t  cache;
      prot_t   prot;
      qos_t    qos;
      region_t region;
      atop_t   atop;
  } aw_chan_t;

  // W Channel
  typedef struct packed {
      data_t data;
      strb_t strb;
      logic  last;
  } w_chan_t;

  // B Channel
  typedef struct packed {
      id_t   id;
      resp_t resp;
  } b_chan_t;

  // AR Channel
  typedef struct packed {
      id_t     id;
      addr_t   addr;
      len_t    len;
      size_t   size;
      burst_t  burst;
      logic    lock;
      cache_t  cache;
      prot_t   prot;
      qos_t    qos;
      region_t region;
  } ar_chan_t;

  // R Channel
  typedef struct packed {
      id_t   id;
      data_t data;
      resp_t resp;
      logic  last;
  } r_chan_t;

endpackage
