// Copyright 2015 - 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
////////////////////////////////////////////////////////////////////////////////
//          Only general functions and definitions are defined here           //
//              These functions are not intended to be modified               //
////////////////////////////////////////////////////////////////////////////////

interface AXI_BUS
#(
    parameter AXI_ADDR_WIDTH = 64,
    parameter AXI_DATA_WIDTH = 64,
    parameter AXI_ID_WIDTH   = 10,
    parameter AXI_USER_WIDTH = 6
);

  localparam AXI_STRB_WIDTH = AXI_DATA_WIDTH/8;

  logic [AXI_ADDR_WIDTH-1:0] aw_addr;
  logic [2:0]                aw_prot;
  logic [3:0]                aw_region;
  logic [7:0]                aw_len;
  logic [2:0]                aw_size;
  logic [1:0]                aw_burst;
  logic                      aw_lock;
  logic [3:0]                aw_cache;
  logic [3:0]                aw_qos;
  logic [AXI_ID_WIDTH-1:0]   aw_id;
  logic [AXI_USER_WIDTH-1:0] aw_user;
  logic                      aw_ready;
  logic                      aw_valid;

  logic [AXI_ADDR_WIDTH-1:0] ar_addr;
  logic [2:0]                ar_prot;
  logic [3:0]                ar_region;
  logic [7:0]                ar_len;
  logic [2:0]                ar_size;
  logic [1:0]                ar_burst;
  logic                      ar_lock;
  logic [3:0]                ar_cache;
  logic [3:0]                ar_qos;
  logic [AXI_ID_WIDTH-1:0]   ar_id;
  logic [AXI_USER_WIDTH-1:0] ar_user;
  logic                      ar_ready;
  logic                      ar_valid;

  logic                      w_valid;
  logic [AXI_DATA_WIDTH-1:0] w_data;
  logic [AXI_STRB_WIDTH-1:0] w_strb;
  logic [AXI_USER_WIDTH-1:0] w_user;
  logic                      w_last;
  logic                      w_ready;

  logic [AXI_DATA_WIDTH-1:0] r_data;
  logic [1:0]                r_resp;
  logic                      r_last;
  logic [AXI_ID_WIDTH-1:0]   r_id;
  logic [AXI_USER_WIDTH-1:0] r_user;
  logic                      r_ready;
  logic                      r_valid;

  logic [1:0]                b_resp;
  logic [AXI_ID_WIDTH-1:0]   b_id;
  logic [AXI_USER_WIDTH-1:0] b_user;
  logic                      b_ready;
  logic                      b_valid;

  // Master Side
  //***************************************
  modport Master
  (

    output aw_valid, output aw_addr, output aw_prot, output aw_region,
    output aw_len, output aw_size, output aw_burst, output aw_lock,
    output aw_cache, output aw_qos, output aw_id, output aw_user,
    input aw_ready,

    output ar_valid, output ar_addr, output ar_prot, output ar_region,
    output ar_len, output ar_size, output ar_burst, output ar_lock,
    output ar_cache, output ar_qos, output ar_id, output ar_user,
    input ar_ready,

    output w_valid, output w_data, output w_strb,  output w_user, output w_last,
    input w_ready,

    input r_valid, input r_data, input r_resp, input r_last, input r_id, input r_user,
    output r_ready,

    input b_valid, input b_resp, input b_id, input b_user,
    output b_ready

  );

  // Slave Side
  //***************************************
  modport Slave
  (

    input aw_valid, input aw_addr, input aw_prot, input aw_region,
    input aw_len, input aw_size, input aw_burst, input aw_lock,
    input aw_cache, input aw_qos, input aw_id, input aw_user,
    output aw_ready,

    input ar_valid, input ar_addr, input ar_prot, input ar_region,
    input ar_len, input ar_size, input ar_burst, input ar_lock,
    input ar_cache, input ar_qos, input ar_id, input ar_user,
    output ar_ready,

    input w_valid, input w_data, input w_strb, input w_user, input w_last,
    output w_ready,

    output r_valid, output r_data, output r_resp, output r_last, output r_id, output r_user,
    input r_ready,

    output b_valid, output b_resp, output b_id, output b_user,
    input b_ready

  );

endinterface

