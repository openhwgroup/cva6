// Copyright 2022 Thales DIS SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Alae Eddine EZ ZEJJARI (alae-eddine.ez-zejjari@external.thalesgroup.com)
// Co-Author: Abdelaali Khardazi

/**** AXI4 interface with parametrized :  ****/

interface uvma_axi_intf #(
   parameter AXI_ADDR_WIDTH      = `UVMA_AXI_ADDR_MAX_WIDTH,
   parameter AXI_DATA_WIDTH      = `UVMA_AXI_DATA_MAX_WIDTH,
   parameter AXI_USER_WIDTH      = `UVMA_AXI_USER_MAX_WIDTH,
   parameter AXI_ID_WIDTH        = `UVMA_AXI_ID_MAX_WIDTH
) (input bit clk, bit rst_n);

   // AXI4 signals
   // Write Address channel
   logic    [AXI_ID_WIDTH-1:0]       aw_id;
   logic    [AXI_ADDR_WIDTH-1:0]     aw_addr;
   logic    [AXI_USER_WIDTH-1:0]     aw_user;
   logic    [7:0]                    aw_len;
   logic    [2:0]                    aw_size;
   logic    [1:0]                    aw_burst;
   logic                             aw_lock;
   logic    [3:0]                    aw_cache;
   logic    [2:0]                    aw_prot;
   logic    [3:0]                    aw_qos;
   logic    [3:0]                    aw_region;
   logic                             aw_valid;
   logic                             aw_ready;
   logic    [5:0]                    aw_atop;

   //write data channel
   logic    [AXI_DATA_WIDTH-1:0]     w_data;
   logic    [AXI_DATA_WIDTH/8-1:0]   w_strb;
   logic    [AXI_USER_WIDTH-1:0]     w_user;
   logic                             w_last;
   logic                             w_valid;
   logic                             w_ready;

   // write response channel
   logic    [AXI_ID_WIDTH-1:0]       b_id;
   logic    [AXI_USER_WIDTH-1:0]     b_user;
   logic    [1:0]                    b_resp;
   logic                             b_valid;
   logic                             b_ready;

   // read address channel
   logic    [AXI_ID_WIDTH-1:0]       ar_id;
   logic    [AXI_ADDR_WIDTH-1:0]     ar_addr;
   logic    [AXI_USER_WIDTH-1:0]     ar_user;
   logic    [7:0]                    ar_len;
   logic    [2:0]                    ar_size;
   logic    [1:0]                    ar_burst;
   logic                             ar_lock;
   logic    [3:0]                    ar_cache;
   logic    [2:0]                    ar_prot;
   logic    [3:0]                    ar_qos;
   logic    [3:0]                    ar_region;
   logic                             ar_valid;
   logic                             ar_ready;

   //read data channel
   logic    [AXI_ID_WIDTH-1:0]       r_id;
   logic    [AXI_DATA_WIDTH-1:0]     r_data;
   logic    [AXI_USER_WIDTH-1:0]     r_user;
   logic    [1:0]                    r_resp;
   logic                             r_last;
   logic                             r_valid;
   logic                             r_ready;



   clocking slv_axi_cb @(posedge clk or rst_n);
      output   ar_ready,
               r_id, r_data, r_resp, r_last, r_valid, r_user,
               aw_ready,
               w_ready,
               b_id, b_resp, b_user, b_valid;
      input    ar_id, ar_addr, ar_user, ar_len, ar_size, ar_burst, ar_lock, ar_cache, ar_prot, ar_qos, ar_region, ar_valid,
               r_ready,
               aw_id, aw_addr, aw_user, aw_len, aw_size, aw_burst, aw_lock, aw_cache, aw_prot, aw_qos, aw_region, aw_valid, aw_atop,
               w_data, w_strb, w_last, w_user, w_valid,
               b_ready;
   endclocking: slv_axi_cb

   clocking psv_axi_cb @(posedge clk or rst_n);
      input    ar_id, ar_addr, ar_user, ar_len, ar_size, ar_burst, ar_lock, ar_cache, ar_prot, ar_qos, ar_region, ar_valid, ar_ready,
               r_ready, r_id, r_data, r_resp, r_user, r_last, r_valid,
               aw_id, aw_addr, aw_user, aw_len, aw_size, aw_burst, aw_lock, aw_cache, aw_prot, aw_qos, aw_region, aw_valid, aw_atop, aw_ready,
               w_data, w_strb, w_last, w_user, w_valid, w_ready,
               b_id, b_resp, b_user, b_valid, b_ready;
   endclocking: psv_axi_cb

   modport slave (clocking slv_axi_cb);
   modport passive (clocking psv_axi_cb);

endinterface : uvma_axi_intf
