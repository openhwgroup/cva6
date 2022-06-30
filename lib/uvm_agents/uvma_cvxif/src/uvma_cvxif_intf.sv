// Copyright 2021 Thales DIS design services SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Zineb EL KACIMI (zineb.el-kacimi@external.thalesgroup.com)


`ifndef __UVMA_CVXIF_INTF_SV__
`define __UVMA_CVXIF_INTF_SV__


//the CoreV-X-Interface for the CVA6
interface uvma_cvxif_intf import cvxif_pkg::*;
(input logic  clk,
 input logic  reset_n);

   cvxif_req_t   cvxif_req_i;
   cvxif_resp_t  cvxif_resp_o;

   /**
    * Used by the monitor.
   */
   clocking monitor_cb @(posedge clk);
      input cvxif_resp_o,
            cvxif_req_i;
   endclocking : monitor_cb

endinterface;


`endif //__UVMA_CVXIF_INTF_SV__
