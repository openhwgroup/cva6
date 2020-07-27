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
//
// This file defines the interfaces we support.

import axi_pkg::*;


/// An AXI4 interface.
interface AXI_BUS #(
  parameter AXI_ADDR_WIDTH = -1,
  parameter AXI_DATA_WIDTH = -1,
  parameter AXI_ID_WIDTH   = -1,
  parameter AXI_USER_WIDTH = -1
);

  localparam AXI_STRB_WIDTH = AXI_DATA_WIDTH / 8;

  typedef logic [AXI_ID_WIDTH-1:0]   id_t;
  typedef logic [AXI_ADDR_WIDTH-1:0] addr_t;
  typedef logic [AXI_DATA_WIDTH-1:0] data_t;
  typedef logic [AXI_STRB_WIDTH-1:0] strb_t;
  typedef logic [AXI_USER_WIDTH-1:0] user_t;
  typedef logic [5:0] atop_t;

  id_t        aw_id;
  addr_t      aw_addr;
  logic [7:0] aw_len;
  logic [2:0] aw_size;
  burst_t     aw_burst;
  logic       aw_lock;
  cache_t     aw_cache;
  prot_t      aw_prot;
  qos_t       aw_qos;
  atop_t      aw_atop;
  region_t    aw_region;
  user_t      aw_user;
  logic       aw_valid;
  logic       aw_ready;

  data_t      w_data;
  strb_t      w_strb;
  logic       w_last;
  user_t      w_user;
  logic       w_valid;
  logic       w_ready;

  id_t        b_id;
  resp_t      b_resp;
  user_t      b_user;
  logic       b_valid;
  logic       b_ready;

  id_t        ar_id;
  addr_t      ar_addr;
  logic [7:0] ar_len;
  logic [2:0] ar_size;
  burst_t     ar_burst;
  logic       ar_lock;
  cache_t     ar_cache;
  prot_t      ar_prot;
  qos_t       ar_qos;
  region_t    ar_region;
  user_t      ar_user;
  logic       ar_valid;
  logic       ar_ready;

  id_t        r_id;
  data_t      r_data;
  resp_t      r_resp;
  logic       r_last;
  user_t      r_user;
  logic       r_valid;
  logic       r_ready;

  modport Master (
    output aw_id, aw_addr, aw_len, aw_size, aw_burst, aw_lock, aw_cache, aw_prot, aw_qos, aw_atop, aw_region, aw_user, aw_valid, input aw_ready,
    output w_data, w_strb, w_last, w_user, w_valid, input w_ready,
    input b_id, b_resp, b_user, b_valid, output b_ready,
    output ar_id, ar_addr, ar_len, ar_size, ar_burst, ar_lock, ar_cache, ar_prot, ar_qos, ar_region, ar_user, ar_valid, input ar_ready,
    input r_id, r_data, r_resp, r_last, r_user, r_valid, output r_ready
  );

  modport Slave (
    input aw_id, aw_addr, aw_len, aw_size, aw_burst, aw_lock, aw_cache, aw_prot, aw_qos, aw_atop, aw_region, aw_user, aw_valid, output aw_ready,
    input w_data, w_strb, w_last, w_user, w_valid, output w_ready,
    output b_id, b_resp, b_user, b_valid, input b_ready,
    input ar_id, ar_addr, ar_len, ar_size, ar_burst, ar_lock, ar_cache, ar_prot, ar_qos, ar_region, ar_user, ar_valid, output ar_ready,
    output r_id, r_data, r_resp, r_last, r_user, r_valid, input r_ready
  );

endinterface


/// An asynchronous AXI4 interface.
interface AXI_BUS_ASYNC
#(
  parameter AXI_ADDR_WIDTH = -1,
  parameter AXI_DATA_WIDTH = -1,
  parameter AXI_ID_WIDTH   = -1,
  parameter AXI_USER_WIDTH = -1,
  parameter BUFFER_WIDTH   = -1
);

  localparam AXI_STRB_WIDTH = AXI_DATA_WIDTH / 8;


  logic [AXI_ID_WIDTH-1:0]    aw_id;
  logic [AXI_ADDR_WIDTH-1:0]  aw_addr;
  logic [7:0]                 aw_len;
  logic [2:0]                 aw_size;
  logic [1:0]                 aw_burst;
  logic                       aw_lock;
  logic [3:0]                 aw_cache;
  logic [2:0]                 aw_prot;
  logic [3:0]                 aw_qos;
  logic [5:0]                 aw_atop;
  logic [3:0]                 aw_region;
  logic [AXI_USER_WIDTH-1:0]  aw_user;
  logic [BUFFER_WIDTH-1:0]    aw_writetoken;
  logic [BUFFER_WIDTH-1:0]    aw_readpointer;

  logic [AXI_DATA_WIDTH-1:0]  w_data;
  logic [AXI_STRB_WIDTH-1:0]  w_strb;
  logic                       w_last;
  logic [AXI_USER_WIDTH-1:0]  w_user;
  logic [BUFFER_WIDTH-1:0]    w_writetoken;
  logic [BUFFER_WIDTH-1:0]    w_readpointer;

  logic [AXI_ID_WIDTH-1:0]    b_id;
  logic [1:0]                 b_resp;
  logic [AXI_USER_WIDTH-1:0]  b_user;
  logic [BUFFER_WIDTH-1:0]    b_writetoken;
  logic [BUFFER_WIDTH-1:0]    b_readpointer;

  logic [AXI_ID_WIDTH-1:0]    ar_id;
  logic [AXI_ADDR_WIDTH-1:0]  ar_addr;
  logic [7:0]                 ar_len;
  logic [2:0]                 ar_size;
  logic [1:0]                 ar_burst;
  logic                       ar_lock;
  logic [3:0]                 ar_cache;
  logic [2:0]                 ar_prot;
  logic [3:0]                 ar_qos;
  logic [3:0]                 ar_region;
  logic [AXI_USER_WIDTH-1:0]  ar_user;
  logic [BUFFER_WIDTH-1:0]    ar_writetoken;
  logic [BUFFER_WIDTH-1:0]    ar_readpointer;

  logic [AXI_ID_WIDTH-1:0]    r_id;
  logic [AXI_DATA_WIDTH-1:0]  r_data;
  logic [1:0]                 r_resp;
  logic                       r_last;
  logic [AXI_USER_WIDTH-1:0]  r_user;
  logic [BUFFER_WIDTH-1:0]    r_writetoken;
  logic [BUFFER_WIDTH-1:0]    r_readpointer;

  modport Master (
    output aw_id, aw_addr, aw_len, aw_size, aw_burst, aw_lock, aw_cache, aw_prot, aw_qos, aw_atop, aw_region, aw_user, aw_writetoken, input aw_readpointer,
    output w_data, w_strb, w_last, w_user, w_writetoken, input w_readpointer,
    input b_id, b_resp, b_user, b_writetoken, output b_readpointer,
    output ar_id, ar_addr, ar_len, ar_size, ar_burst, ar_lock, ar_cache, ar_prot, ar_qos, ar_region, ar_user, ar_writetoken, input ar_readpointer,
    input r_id, r_data, r_resp, r_last, r_user, r_writetoken, output r_readpointer
  );

  modport Slave (
    input aw_id, aw_addr, aw_len, aw_size, aw_burst, aw_lock, aw_cache, aw_prot, aw_qos, aw_atop, aw_region, aw_user, aw_writetoken, output aw_readpointer,
    input w_data, w_strb, w_last, w_user, w_writetoken, output w_readpointer,
    output b_id, b_resp, b_user, b_writetoken, input b_readpointer,
    input ar_id, ar_addr, ar_len, ar_size, ar_burst, ar_lock, ar_cache, ar_prot, ar_qos, ar_region, ar_user, ar_writetoken, output ar_readpointer,
    output r_id, r_data, r_resp, r_last, r_user, r_writetoken, input r_readpointer
  );

endinterface


/// An AXI4-Lite interface.
interface AXI_LITE #(
  parameter AXI_ADDR_WIDTH = -1,
  parameter AXI_DATA_WIDTH = -1
);

  localparam AXI_STRB_WIDTH = AXI_DATA_WIDTH / 8;

  typedef logic [AXI_ADDR_WIDTH-1:0] addr_t;
  typedef logic [AXI_DATA_WIDTH-1:0] data_t;
  typedef logic [AXI_STRB_WIDTH-1:0] strb_t;

  // AW channel
  addr_t aw_addr;
  logic  aw_valid;
  logic  aw_ready;

  data_t w_data;
  strb_t w_strb;
  logic  w_valid;
  logic  w_ready;

  resp_t b_resp;
  logic  b_valid;
  logic  b_ready;

  addr_t ar_addr;
  logic  ar_valid;
  logic  ar_ready;

  data_t r_data;
  resp_t r_resp;
  logic  r_valid;
  logic  r_ready;

  modport Master (
    output aw_addr, aw_valid, input aw_ready,
    output w_data, w_strb, w_valid, input w_ready,
    input b_resp, b_valid, output b_ready,
    output ar_addr, ar_valid, input ar_ready,
    input r_data, r_resp, r_valid, output r_ready
  );

  modport Slave (
    input aw_addr, aw_valid, output aw_ready,
    input w_data, w_strb, w_valid, output w_ready,
    output b_resp, b_valid, input b_ready,
    input ar_addr, ar_valid, output ar_ready,
    output r_data, r_resp, r_valid, input r_ready
  );

  /// The interface as an output (issuing requests, initiator, master).
  modport out (
    output aw_addr, aw_valid, input aw_ready,
    output w_data, w_strb, w_valid, input w_ready,
    input b_resp, b_valid, output b_ready,
    output ar_addr, ar_valid, input ar_ready,
    input r_data, r_resp, r_valid, output r_ready
  );

  /// The interface as an input (accepting requests, target, slave).
  modport in (
    input aw_addr, aw_valid, output aw_ready,
    input w_data, w_strb, w_valid, output w_ready,
    output b_resp, b_valid, input b_ready,
    input ar_addr, ar_valid, output ar_ready,
    output r_data, r_resp, r_valid, input r_ready
  );

endinterface


/// An AXI routing table.
///
/// For each slave, multiple rules can be defined. Each rule consists of an
/// address mask and a base. Addresses are masked and then compared against the
/// base to decide where transfers need to go.
interface AXI_ROUTING_RULES #(
  /// The address width.
  parameter int AXI_ADDR_WIDTH = -1,
  /// The number of slaves in the routing table.
  parameter int NUM_SLAVE  = -1,
  /// The number of rules in the routing table.
  parameter int NUM_RULES  = -1
);

  struct packed {
    logic enabled;
    logic [AXI_ADDR_WIDTH-1:0] mask;
    logic [AXI_ADDR_WIDTH-1:0] base;
  } [NUM_RULES-1:0] rules [NUM_SLAVE];

  modport xbar(input rules);
  modport cfg(output rules);

endinterface


/// An AXI arbitration interface.
interface AXI_ARBITRATION #(
  /// The number of requestors.
  parameter int NUM_REQ = -1
);

  // Incoming requests.
  logic [NUM_REQ-1:0] in_req;
  logic [NUM_REQ-1:0] in_ack;

  // Outgoing request.
  logic out_req;
  logic out_ack;
  logic [$clog2(NUM_REQ)-1:0] out_sel;

  // The arbiter side of the interface.
  modport arb(input  in_req, out_ack, output out_req, out_sel, in_ack);

  // The requestor side of the interface.
  modport req(output in_req, out_ack, input  out_req, out_sel, in_ack);

endinterface
