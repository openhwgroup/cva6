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
// Authors:
// - Fabian Schuiki <fschuiki@iis.ee.ethz.ch>
// - Wolfgang Roenninger <wroennin@iis.ee.ethz.ch>
// - Andreas Kurth <akurth@iis.ee.ethz.ch>



/// An AXI4 interface.
interface AXI_BUS #(
  parameter int unsigned AXI_ADDR_WIDTH = 0,
  parameter int unsigned AXI_DATA_WIDTH = 0,
  parameter int unsigned AXI_ID_WIDTH   = 0,
  parameter int unsigned AXI_USER_WIDTH = 0
);

  localparam int unsigned AXI_STRB_WIDTH = AXI_DATA_WIDTH / 8;

  typedef logic [AXI_ID_WIDTH-1:0]   id_t;
  typedef logic [AXI_ADDR_WIDTH-1:0] addr_t;
  typedef logic [AXI_DATA_WIDTH-1:0] data_t;
  typedef logic [AXI_STRB_WIDTH-1:0] strb_t;
  typedef logic [AXI_USER_WIDTH-1:0] user_t;

  id_t              aw_id;
  addr_t            aw_addr;
  axi_pkg::len_t    aw_len;
  axi_pkg::size_t   aw_size;
  axi_pkg::burst_t  aw_burst;
  logic             aw_lock;
  axi_pkg::cache_t  aw_cache;
  axi_pkg::prot_t   aw_prot;
  axi_pkg::qos_t    aw_qos;
  axi_pkg::region_t aw_region;
  axi_pkg::atop_t   aw_atop;
  user_t            aw_user;
  logic             aw_valid;
  logic             aw_ready;

  data_t            w_data;
  strb_t            w_strb;
  logic             w_last;
  user_t            w_user;
  logic             w_valid;
  logic             w_ready;

  id_t              b_id;
  axi_pkg::resp_t   b_resp;
  user_t            b_user;
  logic             b_valid;
  logic             b_ready;

  id_t              ar_id;
  addr_t            ar_addr;
  axi_pkg::len_t    ar_len;
  axi_pkg::size_t   ar_size;
  axi_pkg::burst_t  ar_burst;
  logic             ar_lock;
  axi_pkg::cache_t  ar_cache;
  axi_pkg::prot_t   ar_prot;
  axi_pkg::qos_t    ar_qos;
  axi_pkg::region_t ar_region;
  user_t            ar_user;
  logic             ar_valid;
  logic             ar_ready;

  id_t              r_id;
  data_t            r_data;
  axi_pkg::resp_t   r_resp;
  logic             r_last;
  user_t            r_user;
  logic             r_valid;
  logic             r_ready;

  modport Master (
    output aw_id, aw_addr, aw_len, aw_size, aw_burst, aw_lock, aw_cache, aw_prot, aw_qos, aw_region, aw_atop, aw_user, aw_valid, input aw_ready,
    output w_data, w_strb, w_last, w_user, w_valid, input w_ready,
    input b_id, b_resp, b_user, b_valid, output b_ready,
    output ar_id, ar_addr, ar_len, ar_size, ar_burst, ar_lock, ar_cache, ar_prot, ar_qos, ar_region, ar_user, ar_valid, input ar_ready,
    input r_id, r_data, r_resp, r_last, r_user, r_valid, output r_ready
  );

  modport Slave (
    input aw_id, aw_addr, aw_len, aw_size, aw_burst, aw_lock, aw_cache, aw_prot, aw_qos, aw_region, aw_atop, aw_user, aw_valid, output aw_ready,
    input w_data, w_strb, w_last, w_user, w_valid, output w_ready,
    output b_id, b_resp, b_user, b_valid, input b_ready,
    input ar_id, ar_addr, ar_len, ar_size, ar_burst, ar_lock, ar_cache, ar_prot, ar_qos, ar_region, ar_user, ar_valid, output ar_ready,
    output r_id, r_data, r_resp, r_last, r_user, r_valid, input r_ready
  );

endinterface


/// A clocked AXI4 interface for use in design verification.
interface AXI_BUS_DV #(
  parameter int unsigned AXI_ADDR_WIDTH = 0,
  parameter int unsigned AXI_DATA_WIDTH = 0,
  parameter int unsigned AXI_ID_WIDTH   = 0,
  parameter int unsigned AXI_USER_WIDTH = 0
)(
  input logic clk_i
);

  localparam int unsigned AXI_STRB_WIDTH = AXI_DATA_WIDTH / 8;

  typedef logic [AXI_ID_WIDTH-1:0]   id_t;
  typedef logic [AXI_ADDR_WIDTH-1:0] addr_t;
  typedef logic [AXI_DATA_WIDTH-1:0] data_t;
  typedef logic [AXI_STRB_WIDTH-1:0] strb_t;
  typedef logic [AXI_USER_WIDTH-1:0] user_t;

  id_t              aw_id;
  addr_t            aw_addr;
  axi_pkg::len_t    aw_len;
  axi_pkg::size_t   aw_size;
  axi_pkg::burst_t  aw_burst;
  logic             aw_lock;
  axi_pkg::cache_t  aw_cache;
  axi_pkg::prot_t   aw_prot;
  axi_pkg::qos_t    aw_qos;
  axi_pkg::region_t aw_region;
  axi_pkg::atop_t   aw_atop;
  user_t            aw_user;
  logic             aw_valid;
  logic             aw_ready;

  data_t            w_data;
  strb_t            w_strb;
  logic             w_last;
  user_t            w_user;
  logic             w_valid;
  logic             w_ready;

  id_t              b_id;
  axi_pkg::resp_t   b_resp;
  user_t            b_user;
  logic             b_valid;
  logic             b_ready;

  id_t              ar_id;
  addr_t            ar_addr;
  axi_pkg::len_t    ar_len;
  axi_pkg::size_t   ar_size;
  axi_pkg::burst_t  ar_burst;
  logic             ar_lock;
  axi_pkg::cache_t  ar_cache;
  axi_pkg::prot_t   ar_prot;
  axi_pkg::qos_t    ar_qos;
  axi_pkg::region_t ar_region;
  user_t            ar_user;
  logic             ar_valid;
  logic             ar_ready;

  id_t              r_id;
  data_t            r_data;
  axi_pkg::resp_t   r_resp;
  logic             r_last;
  user_t            r_user;
  logic             r_valid;
  logic             r_ready;

  modport Master (
    output aw_id, aw_addr, aw_len, aw_size, aw_burst, aw_lock, aw_cache, aw_prot, aw_qos, aw_region, aw_atop, aw_user, aw_valid, input aw_ready,
    output w_data, w_strb, w_last, w_user, w_valid, input w_ready,
    input b_id, b_resp, b_user, b_valid, output b_ready,
    output ar_id, ar_addr, ar_len, ar_size, ar_burst, ar_lock, ar_cache, ar_prot, ar_qos, ar_region, ar_user, ar_valid, input ar_ready,
    input r_id, r_data, r_resp, r_last, r_user, r_valid, output r_ready
  );

  modport Slave (
    input aw_id, aw_addr, aw_len, aw_size, aw_burst, aw_lock, aw_cache, aw_prot, aw_qos, aw_region, aw_atop, aw_user, aw_valid, output aw_ready,
    input w_data, w_strb, w_last, w_user, w_valid, output w_ready,
    output b_id, b_resp, b_user, b_valid, input b_ready,
    input ar_id, ar_addr, ar_len, ar_size, ar_burst, ar_lock, ar_cache, ar_prot, ar_qos, ar_region, ar_user, ar_valid, output ar_ready,
    output r_id, r_data, r_resp, r_last, r_user, r_valid, input r_ready
  );

  modport Monitor (
    input aw_id, aw_addr, aw_len, aw_size, aw_burst, aw_lock, aw_cache, aw_prot, aw_qos, aw_region, aw_atop, aw_user, aw_valid, aw_ready,
          w_data, w_strb, w_last, w_user, w_valid, w_ready,
          b_id, b_resp, b_user, b_valid, b_ready,
          ar_id, ar_addr, ar_len, ar_size, ar_burst, ar_lock, ar_cache, ar_prot, ar_qos, ar_region, ar_user, ar_valid, ar_ready,
          r_id, r_data, r_resp, r_last, r_user, r_valid, r_ready
  );

  // pragma translate_off
  `ifndef VERILATOR
  // Single-Channel Assertions: Signals including valid must not change between valid and handshake.
  // AW
  assert property (@(posedge clk_i) (aw_valid && !aw_ready |=> $stable(aw_id)));
  assert property (@(posedge clk_i) (aw_valid && !aw_ready |=> $stable(aw_addr)));
  assert property (@(posedge clk_i) (aw_valid && !aw_ready |=> $stable(aw_len)));
  assert property (@(posedge clk_i) (aw_valid && !aw_ready |=> $stable(aw_size)));
  assert property (@(posedge clk_i) (aw_valid && !aw_ready |=> $stable(aw_burst)));
  assert property (@(posedge clk_i) (aw_valid && !aw_ready |=> $stable(aw_lock)));
  assert property (@(posedge clk_i) (aw_valid && !aw_ready |=> $stable(aw_cache)));
  assert property (@(posedge clk_i) (aw_valid && !aw_ready |=> $stable(aw_prot)));
  assert property (@(posedge clk_i) (aw_valid && !aw_ready |=> $stable(aw_qos)));
  assert property (@(posedge clk_i) (aw_valid && !aw_ready |=> $stable(aw_region)));
  assert property (@(posedge clk_i) (aw_valid && !aw_ready |=> $stable(aw_atop)));
  assert property (@(posedge clk_i) (aw_valid && !aw_ready |=> $stable(aw_user)));
  assert property (@(posedge clk_i) (aw_valid && !aw_ready |=> aw_valid));
  // W
  assert property (@(posedge clk_i) ( w_valid && ! w_ready |=> $stable(w_data)));
  assert property (@(posedge clk_i) ( w_valid && ! w_ready |=> $stable(w_strb)));
  assert property (@(posedge clk_i) ( w_valid && ! w_ready |=> $stable(w_last)));
  assert property (@(posedge clk_i) ( w_valid && ! w_ready |=> $stable(w_user)));
  assert property (@(posedge clk_i) ( w_valid && ! w_ready |=> w_valid));
  // B
  assert property (@(posedge clk_i) ( b_valid && ! b_ready |=> $stable(b_id)));
  assert property (@(posedge clk_i) ( b_valid && ! b_ready |=> $stable(b_resp)));
  assert property (@(posedge clk_i) ( b_valid && ! b_ready |=> $stable(b_user)));
  assert property (@(posedge clk_i) ( b_valid && ! b_ready |=> b_valid));
  // AR
  assert property (@(posedge clk_i) (ar_valid && !ar_ready |=> $stable(ar_id)));
  assert property (@(posedge clk_i) (ar_valid && !ar_ready |=> $stable(ar_addr)));
  assert property (@(posedge clk_i) (ar_valid && !ar_ready |=> $stable(ar_len)));
  assert property (@(posedge clk_i) (ar_valid && !ar_ready |=> $stable(ar_size)));
  assert property (@(posedge clk_i) (ar_valid && !ar_ready |=> $stable(ar_burst)));
  assert property (@(posedge clk_i) (ar_valid && !ar_ready |=> $stable(ar_lock)));
  assert property (@(posedge clk_i) (ar_valid && !ar_ready |=> $stable(ar_cache)));
  assert property (@(posedge clk_i) (ar_valid && !ar_ready |=> $stable(ar_prot)));
  assert property (@(posedge clk_i) (ar_valid && !ar_ready |=> $stable(ar_qos)));
  assert property (@(posedge clk_i) (ar_valid && !ar_ready |=> $stable(ar_region)));
  assert property (@(posedge clk_i) (ar_valid && !ar_ready |=> $stable(ar_user)));
  assert property (@(posedge clk_i) (ar_valid && !ar_ready |=> ar_valid));
  // R
  assert property (@(posedge clk_i) ( r_valid && ! r_ready |=> $stable(r_id)));
  assert property (@(posedge clk_i) ( r_valid && ! r_ready |=> $stable(r_data)));
  assert property (@(posedge clk_i) ( r_valid && ! r_ready |=> $stable(r_resp)));
  assert property (@(posedge clk_i) ( r_valid && ! r_ready |=> $stable(r_last)));
  assert property (@(posedge clk_i) ( r_valid && ! r_ready |=> $stable(r_user)));
  assert property (@(posedge clk_i) ( r_valid && ! r_ready |=> r_valid));
  `endif
  // pragma translate_on

endinterface


/// An asynchronous AXI4 interface.
interface AXI_BUS_ASYNC
#(
  parameter int unsigned AXI_ADDR_WIDTH = 0,
  parameter int unsigned AXI_DATA_WIDTH = 0,
  parameter int unsigned AXI_ID_WIDTH   = 0,
  parameter int unsigned AXI_USER_WIDTH = 0,
  parameter int unsigned BUFFER_WIDTH   = 0
);

  localparam int unsigned AXI_STRB_WIDTH = AXI_DATA_WIDTH / 8;

  typedef logic [AXI_ID_WIDTH-1:0]   id_t;
  typedef logic [AXI_ADDR_WIDTH-1:0] addr_t;
  typedef logic [AXI_DATA_WIDTH-1:0] data_t;
  typedef logic [AXI_STRB_WIDTH-1:0] strb_t;
  typedef logic [AXI_USER_WIDTH-1:0] user_t;
  typedef logic [BUFFER_WIDTH-1:0]   buffer_t;

  id_t              aw_id;
  addr_t            aw_addr;
  axi_pkg::len_t    aw_len;
  axi_pkg::size_t   aw_size;
  axi_pkg::burst_t  aw_burst;
  logic             aw_lock;
  axi_pkg::cache_t  aw_cache;
  axi_pkg::prot_t   aw_prot;
  axi_pkg::qos_t    aw_qos;
  axi_pkg::region_t aw_region;
  axi_pkg::atop_t   aw_atop;
  user_t            aw_user;
  buffer_t          aw_writetoken;
  buffer_t          aw_readpointer;

  data_t            w_data;
  strb_t            w_strb;
  logic             w_last;
  user_t            w_user;
  buffer_t          w_writetoken;
  buffer_t          w_readpointer;

  id_t              b_id;
  axi_pkg::resp_t   b_resp;
  user_t            b_user;
  buffer_t          b_writetoken;
  buffer_t          b_readpointer;

  id_t              ar_id;
  addr_t            ar_addr;
  axi_pkg::len_t    ar_len;
  axi_pkg::size_t   ar_size;
  axi_pkg::burst_t  ar_burst;
  logic             ar_lock;
  axi_pkg::cache_t  ar_cache;
  axi_pkg::prot_t   ar_prot;
  axi_pkg::qos_t    ar_qos;
  axi_pkg::region_t ar_region;
  user_t            ar_user;
  buffer_t          ar_writetoken;
  buffer_t          ar_readpointer;

  id_t              r_id;
  data_t            r_data;
  axi_pkg::resp_t   r_resp;
  logic             r_last;
  user_t            r_user;
  buffer_t          r_writetoken;
  buffer_t          r_readpointer;

  modport Master (
    output aw_id, aw_addr, aw_len, aw_size, aw_burst, aw_lock, aw_cache, aw_prot, aw_qos, aw_region, aw_atop, aw_user, aw_writetoken, input aw_readpointer,
    output w_data, w_strb, w_last, w_user, w_writetoken, input w_readpointer,
    input b_id, b_resp, b_user, b_writetoken, output b_readpointer,
    output ar_id, ar_addr, ar_len, ar_size, ar_burst, ar_lock, ar_cache, ar_prot, ar_qos, ar_region, ar_user, ar_writetoken, input ar_readpointer,
    input r_id, r_data, r_resp, r_last, r_user, r_writetoken, output r_readpointer
  );

  modport Slave (
    input aw_id, aw_addr, aw_len, aw_size, aw_burst, aw_lock, aw_cache, aw_prot, aw_qos, aw_region, aw_atop, aw_user, aw_writetoken, output aw_readpointer,
    input w_data, w_strb, w_last, w_user, w_writetoken, output w_readpointer,
    output b_id, b_resp, b_user, b_writetoken, input b_readpointer,
    input ar_id, ar_addr, ar_len, ar_size, ar_burst, ar_lock, ar_cache, ar_prot, ar_qos, ar_region, ar_user, ar_writetoken, output ar_readpointer,
    output r_id, r_data, r_resp, r_last, r_user, r_writetoken, input r_readpointer
  );

endinterface


`include "axi/typedef.svh"

/// An asynchronous AXI4 interface for Gray CDCs.
interface AXI_BUS_ASYNC_GRAY #(
  parameter int unsigned AXI_ADDR_WIDTH = 0,
  parameter int unsigned AXI_DATA_WIDTH = 0,
  parameter int unsigned AXI_ID_WIDTH = 0,
  parameter int unsigned AXI_USER_WIDTH = 0,
  parameter int unsigned LOG_DEPTH = 0
);

  localparam int unsigned AXI_STRB_WIDTH = AXI_DATA_WIDTH / 8;

  typedef logic [AXI_ID_WIDTH-1:0]   id_t;
  typedef logic [AXI_ADDR_WIDTH-1:0] addr_t;
  typedef logic [AXI_DATA_WIDTH-1:0] data_t;
  typedef logic [AXI_STRB_WIDTH-1:0] strb_t;
  typedef logic [AXI_USER_WIDTH-1:0] user_t;

  `AXI_TYPEDEF_AW_CHAN_T(aw_chan_t, addr_t, id_t, user_t)
  `AXI_TYPEDEF_W_CHAN_T(w_chan_t, data_t, strb_t, user_t)
  `AXI_TYPEDEF_B_CHAN_T(b_chan_t, id_t, user_t)
  `AXI_TYPEDEF_AR_CHAN_T(ar_chan_t, addr_t, id_t, user_t)
  `AXI_TYPEDEF_R_CHAN_T(r_chan_t, data_t, id_t, user_t)

  aw_chan_t  [2**LOG_DEPTH-1:0] aw_data;
  w_chan_t   [2**LOG_DEPTH-1:0] w_data;
  b_chan_t   [2**LOG_DEPTH-1:0] b_data;
  ar_chan_t  [2**LOG_DEPTH-1:0] ar_data;
  r_chan_t   [2**LOG_DEPTH-1:0] r_data;
  logic           [LOG_DEPTH:0] aw_wptr,  aw_rptr,
                                w_wptr,   w_rptr,
                                b_wptr,   b_rptr,
                                ar_wptr,  ar_rptr,
                                r_wptr,   r_rptr;

  modport Master (
    output aw_data, aw_wptr, input aw_rptr,
    output w_data, w_wptr, input w_rptr,
    input b_data, b_wptr, output b_rptr,
    output ar_data, ar_wptr, input ar_rptr,
    input r_data, r_wptr, output r_rptr);

  modport Slave (
    input aw_data, aw_wptr, output aw_rptr,
    input w_data, w_wptr, output w_rptr,
    output b_data, b_wptr, input b_rptr,
    input ar_data, ar_wptr, output ar_rptr,
    output r_data, r_wptr, input r_rptr);

endinterface


/// An AXI4-Lite interface.
interface AXI_LITE #(
  parameter int unsigned AXI_ADDR_WIDTH = 0,
  parameter int unsigned AXI_DATA_WIDTH = 0
);

  localparam int unsigned AXI_STRB_WIDTH = AXI_DATA_WIDTH / 8;

  typedef logic [AXI_ADDR_WIDTH-1:0] addr_t;
  typedef logic [AXI_DATA_WIDTH-1:0] data_t;
  typedef logic [AXI_STRB_WIDTH-1:0] strb_t;

  // AW channel
  addr_t          aw_addr;
  axi_pkg::prot_t aw_prot;
  logic           aw_valid;
  logic           aw_ready;

  data_t          w_data;
  strb_t          w_strb;
  logic           w_valid;
  logic           w_ready;

  axi_pkg::resp_t b_resp;
  logic           b_valid;
  logic           b_ready;

  addr_t          ar_addr;
  axi_pkg::prot_t ar_prot;
  logic           ar_valid;
  logic           ar_ready;

  data_t          r_data;
  axi_pkg::resp_t r_resp;
  logic           r_valid;
  logic           r_ready;

  modport Master (
    output aw_addr, aw_prot, aw_valid, input aw_ready,
    output w_data, w_strb, w_valid, input w_ready,
    input b_resp, b_valid, output b_ready,
    output ar_addr, ar_prot, ar_valid, input ar_ready,
    input r_data, r_resp, r_valid, output r_ready
  );

  modport Slave (
    input aw_addr, aw_prot, aw_valid, output aw_ready,
    input w_data, w_strb, w_valid, output w_ready,
    output b_resp, b_valid, input b_ready,
    input ar_addr, ar_prot, ar_valid, output ar_ready,
    output r_data, r_resp, r_valid, input r_ready
  );

endinterface


/// A clocked AXI4-Lite interface for use in design verification.
interface AXI_LITE_DV #(
  parameter int unsigned AXI_ADDR_WIDTH = 0,
  parameter int unsigned AXI_DATA_WIDTH = 0
)(
  input logic clk_i
);

  localparam AXI_STRB_WIDTH = AXI_DATA_WIDTH / 8;

  typedef logic [AXI_ADDR_WIDTH-1:0] addr_t;
  typedef logic [AXI_DATA_WIDTH-1:0] data_t;
  typedef logic [AXI_STRB_WIDTH-1:0] strb_t;

  // AW channel
  addr_t          aw_addr;
  axi_pkg::prot_t aw_prot;
  logic           aw_valid;
  logic           aw_ready;

  data_t          w_data;
  strb_t          w_strb;
  logic           w_valid;
  logic           w_ready;

  axi_pkg::resp_t b_resp;
  logic           b_valid;
  logic           b_ready;

  addr_t          ar_addr;
  axi_pkg::prot_t ar_prot;
  logic           ar_valid;
  logic           ar_ready;

  data_t          r_data;
  axi_pkg::resp_t r_resp;
  logic           r_valid;
  logic           r_ready;

  modport Master (
    output aw_addr, aw_prot, aw_valid, input aw_ready,
    output w_data, w_strb, w_valid, input w_ready,
    input b_resp, b_valid, output b_ready,
    output ar_addr, ar_prot, ar_valid, input ar_ready,
    input r_data, r_resp, r_valid, output r_ready
  );

  modport Slave (
    input aw_addr, aw_prot, aw_valid, output aw_ready,
    input w_data, w_strb, w_valid, output w_ready,
    output b_resp, b_valid, input b_ready,
    input ar_addr, ar_prot, ar_valid, output ar_ready,
    output r_data, r_resp, r_valid, input r_ready
  );

endinterface


/// An asynchronous AXI4-Lite interface for Gray CDCs.
interface AXI_LITE_ASYNC_GRAY #(
  parameter int unsigned AXI_ADDR_WIDTH = 0,
  parameter int unsigned AXI_DATA_WIDTH = 0,
  parameter int unsigned LOG_DEPTH = 0
);

  localparam int unsigned AXI_STRB_WIDTH = AXI_DATA_WIDTH / 8;

  typedef logic [AXI_ADDR_WIDTH-1:0] addr_t;
  typedef logic [AXI_DATA_WIDTH-1:0] data_t;
  typedef logic [AXI_STRB_WIDTH-1:0] strb_t;

  `AXI_LITE_TYPEDEF_AW_CHAN_T(aw_chan_t, addr_t)
  `AXI_LITE_TYPEDEF_W_CHAN_T(w_chan_t, data_t, strb_t)
  `AXI_LITE_TYPEDEF_B_CHAN_T(b_chan_t)
  `AXI_LITE_TYPEDEF_AR_CHAN_T(ar_chan_t, addr_t)
  `AXI_LITE_TYPEDEF_R_CHAN_T(r_chan_t, data_t)

  aw_chan_t  [2**LOG_DEPTH-1:0] aw_data;
  w_chan_t   [2**LOG_DEPTH-1:0] w_data;
  b_chan_t   [2**LOG_DEPTH-1:0] b_data;
  ar_chan_t  [2**LOG_DEPTH-1:0] ar_data;
  r_chan_t   [2**LOG_DEPTH-1:0] r_data;
  logic           [LOG_DEPTH:0] aw_wptr,  aw_rptr,
                                w_wptr,   w_rptr,
                                b_wptr,   b_rptr,
                                ar_wptr,  ar_rptr,
                                r_wptr,   r_rptr;

  modport Master (
    output aw_data, aw_wptr, input aw_rptr,
    output w_data, w_wptr, input w_rptr,
    input b_data, b_wptr, output b_rptr,
    output ar_data, ar_wptr, input ar_rptr,
    input r_data, r_wptr, output r_rptr);

  modport Slave (
    input aw_data, aw_wptr, output aw_rptr,
    input w_data, w_wptr, output w_rptr,
    output b_data, b_wptr, input b_rptr,
    input ar_data, ar_wptr, output ar_rptr,
    output r_data, r_wptr, input r_rptr);

endinterface
